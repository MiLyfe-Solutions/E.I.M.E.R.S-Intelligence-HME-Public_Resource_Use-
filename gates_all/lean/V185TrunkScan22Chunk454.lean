import V185TrunkScan22Chunk453

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4047399 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4047399 : Nat := 118140960795 + 4047399 * 2 ^ 59
def prefixEnd_4047399 : Nat := 4983230072969 + 3 ^ 40 * 4047399 * 2
def baseEnd_4047399 : Nat := 1385507391684610177665905

theorem tailTrace_4047399 : CollatzResearch.WordTrace tailWord_4047399 prefixEnd_4047399 1385507391684610177665905 := by
  unfold tailWord_4047399
  simp only [CollatzResearch.WordTrace]
  refine ⟨147620769063972138561825251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98413846042648092374550167 147620769063972138561825251)
  ·
    refine ⟨221431153595958207842737877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147620769063972138561825251 221431153595958207842737877)
    ·
      refine ⟨5189792662405270496314169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 221431153595958207842737877 5189792662405270496314169)
      ·
        refine ⟨3892344496803952872235627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189792662405270496314169 3892344496803952872235627)
        ·
          refine ⟨5838516745205929308353441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892344496803952872235627 5838516745205929308353441)
          ·
            refine ⟨4378887558904446981265081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5838516745205929308353441 4378887558904446981265081)
            ·
              refine ⟨3284165669178335235948811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378887558904446981265081 3284165669178335235948811)
              ·
                refine ⟨4926248503767502853923217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284165669178335235948811 4926248503767502853923217)
                ·
                  refine ⟨3694686377825627140442413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4926248503767502853923217 3694686377825627140442413)
                  ·
                    refine ⟨1385507391684610177665905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694686377825627140442413 1385507391684610177665905)
                    ·
                      rfl

theorem cell22_4047399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4047399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047399 prefixEnd_4047399 := by exact prefixLift 4047399
  have htrace : WordTrace (prefixWord ++ tailWord_4047399) baseStart_4047399 baseEnd_4047399 := by
    simpa [prefixWord, tailWord_4047399, baseEnd_4047399] using wordTrace_append hprefix tailTrace_4047399
  have hstable : (prefixWord ++ tailWord_4047399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047399).length < 2 ^ (prefixWord ++ tailWord_4047399).sum := by decide
  have hdescent : baseEnd_4047399 < baseStart_4047399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047404 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_4047404 : Nat := 118140960795 + 4047404 * 2 ^ 59
def prefixEnd_4047404 : Nat := 4983230072969 + 3 ^ 40 * 4047404 * 2
def baseEnd_4047404 : Nat := 1385509103286791831290889

theorem tailTrace_4047404 : CollatzResearch.WordTrace tailWord_4047404 prefixEnd_4047404 1385509103286791831290889 := by
  unfold tailWord_4047404
  simp only [CollatzResearch.WordTrace]
  refine ⟨73810475714477012207878633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98413967619302682943838177 73810475714477012207878633)
  ·
    refine ⟨55357856785857759155908975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73810475714477012207878633 55357856785857759155908975)
    ·
      refine ⟨83036785178786638733863463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55357856785857759155908975 83036785178786638733863463)
      ·
        refine ⟨124555177768179958100795195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83036785178786638733863463 124555177768179958100795195)
        ·
          refine ⟨186832766652269937151192793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124555177768179958100795195 186832766652269937151192793)
          ·
            refine ⟨140124574989202452863394595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186832766652269937151192793 140124574989202452863394595)
            ·
              refine ⟨210186862483803679295091893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140124574989202452863394595 210186862483803679295091893)
              ·
                refine ⟨19705018357856594933914865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210186862483803679295091893 19705018357856594933914865)
                ·
                  refine ⟨14778763768392446200436149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19705018357856594933914865 14778763768392446200436149)
                  ·
                    refine ⟨1385509103286791831290889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14778763768392446200436149 1385509103286791831290889)
                    ·
                      rfl

theorem cell22_4047404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_4047404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047404 prefixEnd_4047404 := by exact prefixLift 4047404
  have htrace : WordTrace (prefixWord ++ tailWord_4047404) baseStart_4047404 baseEnd_4047404 := by
    simpa [prefixWord, tailWord_4047404, baseEnd_4047404] using wordTrace_append hprefix tailTrace_4047404
  have hstable : (prefixWord ++ tailWord_4047404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047404).length < 2 ^ (prefixWord ++ tailWord_4047404).sum := by decide
  have hdescent : baseEnd_4047404 < baseStart_4047404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047479 : List Nat := [1, 1, 3, 1, 1, 3, 2, 10]
def baseStart_4047479 : Nat := 118140960795 + 4047479 * 2 ^ 59
def prefixEnd_4047479 : Nat := 4983230072969 + 3 ^ 40 * 4047479 * 2
def baseEnd_4047479 : Nat := 153948308591057403962851

theorem tailTrace_4047479 : CollatzResearch.WordTrace tailWord_4047479 prefixEnd_4047479 153948308591057403962851 := by
  unfold tailWord_4047479
  simp only [CollatzResearch.WordTrace]
  refine ⟨147623686903682312224737491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98415791269121541483158327 147623686903682312224737491)
  ·
    refine ⟨221435530355523468337106237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147623686903682312224737491 221435530355523468337106237)
    ·
      refine ⟨83038323883321300626414839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221435530355523468337106237 83038323883321300626414839)
      ·
        refine ⟨124557485824981950939622259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83038323883321300626414839 124557485824981950939622259)
        ·
          refine ⟨186836228737472926409433389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124557485824981950939622259 186836228737472926409433389)
          ·
            refine ⟨70063585776552347403537521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186836228737472926409433389 70063585776552347403537521)
            ·
              refine ⟨52547689332414260552653141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70063585776552347403537521 52547689332414260552653141)
              ·
                refine ⟨153948308591057403962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52547689332414260552653141 153948308591057403962851)
                ·
                  rfl

theorem cell22_4047479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 10].length) (baseStart_4047479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047479 prefixEnd_4047479 := by exact prefixLift 4047479
  have htrace : WordTrace (prefixWord ++ tailWord_4047479) baseStart_4047479 baseEnd_4047479 := by
    simpa [prefixWord, tailWord_4047479, baseEnd_4047479] using wordTrace_append hprefix tailTrace_4047479
  have hstable : (prefixWord ++ tailWord_4047479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047479).length < 2 ^ (prefixWord ++ tailWord_4047479).sum := by decide
  have hdescent : baseEnd_4047479 < baseStart_4047479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047481 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_4047481 : Nat := 118140960795 + 4047481 * 2 ^ 59
def prefixEnd_4047481 : Nat := 4983230072969 + 3 ^ 40 * 4047481 * 2
def baseEnd_4047481 : Nat := 1385535461960389297115653

theorem tailTrace_4047481 : CollatzResearch.WordTrace tailWord_4047481 prefixEnd_4047481 1385535461960389297115653 := by
  unfold tailWord_4047481
  simp only [CollatzResearch.WordTrace]
  refine ⟨147623759849675066566310297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98415839899783377710873531 147623759849675066566310297)
  ·
    refine ⟨110717819887256299924732723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147623759849675066566310297 110717819887256299924732723)
    ·
      refine ⟨166076729830884449887099085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110717819887256299924732723 166076729830884449887099085)
      ·
        refine ⟨62278773686581668707662157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166076729830884449887099085 62278773686581668707662157)
        ·
          refine ⟨23354540132468125765373309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62278773686581668707662157 23354540132468125765373309)
          ·
            refine ⟨8757952549675547162014991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23354540132468125765373309 8757952549675547162014991)
            ·
              refine ⟨13136928824513320743022487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757952549675547162014991 13136928824513320743022487)
              ·
                refine ⟨19705393236769981114533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13136928824513320743022487 19705393236769981114533731)
                ·
                  refine ⟨29558089855154971671800597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19705393236769981114533731 29558089855154971671800597)
                  ·
                    refine ⟨1385535461960389297115653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29558089855154971671800597 1385535461960389297115653)
                    ·
                      rfl

theorem cell22_4047481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_4047481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047481 prefixEnd_4047481 := by exact prefixLift 4047481
  have htrace : WordTrace (prefixWord ++ tailWord_4047481) baseStart_4047481 baseEnd_4047481 := by
    simpa [prefixWord, tailWord_4047481, baseEnd_4047481] using wordTrace_append hprefix tailTrace_4047481
  have hstable : (prefixWord ++ tailWord_4047481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047481).length < 2 ^ (prefixWord ++ tailWord_4047481).sum := by decide
  have hdescent : baseEnd_4047481 < baseStart_4047481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047485 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 4]
def baseStart_4047485 : Nat := 118140960795 + 4047485 * 2 ^ 59
def prefixEnd_4047485 : Nat := 4983230072969 + 3 ^ 40 * 4047485 * 2
def baseEnd_4047485 : Nat := 461845610414044873338547

theorem tailTrace_4047485 : CollatzResearch.WordTrace tailWord_4047485 prefixEnd_4047485 461845610414044873338547 := by
  unfold tailWord_4047485
  simp only [CollatzResearch.WordTrace]
  refine ⟨147623905741660575249455909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98415937161107050166303939 147623905741660575249455909)
  ·
    refine ⟨27679482326561357859272983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147623905741660575249455909 27679482326561357859272983)
    ·
      refine ⟨41519223489842036788909475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27679482326561357859272983 41519223489842036788909475)
      ·
        refine ⟨62278835234763055183364213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41519223489842036788909475 62278835234763055183364213)
        ·
          refine ⟨5838640803259036423440395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62278835234763055183364213 5838640803259036423440395)
          ·
            refine ⟨8757961204888554635160593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838640803259036423440395 8757961204888554635160593)
            ·
              refine ⟨6568470903666415976370445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8757961204888554635160593 6568470903666415976370445)
              ·
                refine ⟨2463176588874905991138917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6568470903666415976370445 2463176588874905991138917)
                ·
                  refine ⟨461845610414044873338547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463176588874905991138917 461845610414044873338547)
                  ·
                    rfl

theorem cell22_4047485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_4047485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047485 prefixEnd_4047485 := by exact prefixLift 4047485
  have htrace : WordTrace (prefixWord ++ tailWord_4047485) baseStart_4047485 baseEnd_4047485 := by
    simpa [prefixWord, tailWord_4047485, baseEnd_4047485] using wordTrace_append hprefix tailTrace_4047485
  have hstable : (prefixWord ++ tailWord_4047485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047485).length < 2 ^ (prefixWord ++ tailWord_4047485).sum := by decide
  have hdescent : baseEnd_4047485 < baseStart_4047485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047530 : List Nat := [3, 1, 5, 2, 1, 1, 1, 8]
def baseStart_4047530 : Nat := 118140960795 + 4047530 * 2 ^ 59
def prefixEnd_4047530 : Nat := 4983230072969 + 3 ^ 40 * 4047530 * 2
def baseEnd_4047530 : Nat := 153950248406863278071167

theorem tailTrace_4047530 : CollatzResearch.WordTrace tailWord_4047530 prefixEnd_4047530 153950248406863278071167 := by
  unfold tailWord_4047530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36906386756624386983711011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98417031350998365289896029 36906386756624386983711011)
  ·
    refine ⟨55359580134936580475566517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36906386756624386983711011 55359580134936580475566517)
    ·
      refine ⟨5189960637650304419584361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55359580134936580475566517 5189960637650304419584361)
      ·
        refine ⟨3892470478237728314688271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189960637650304419584361 3892470478237728314688271)
        ·
          refine ⟨5838705717356592472032407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892470478237728314688271 5838705717356592472032407)
          ·
            refine ⟨8758058576034888708048611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838705717356592472032407 8758058576034888708048611)
            ·
              refine ⟨13137087864052333062072917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758058576034888708048611 13137087864052333062072917)
              ·
                refine ⟨153950248406863278071167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13137087864052333062072917 153950248406863278071167)
                ·
                  rfl

theorem cell22_4047530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_4047530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047530 prefixEnd_4047530 := by exact prefixLift 4047530
  have htrace : WordTrace (prefixWord ++ tailWord_4047530) baseStart_4047530 baseEnd_4047530 := by
    simpa [prefixWord, tailWord_4047530, baseEnd_4047530] using wordTrace_append hprefix tailTrace_4047530
  have hstable : (prefixWord ++ tailWord_4047530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047530).length < 2 ^ (prefixWord ++ tailWord_4047530).sum := by decide
  have hdescent : baseEnd_4047530 < baseStart_4047530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047575 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 5]
def baseStart_4047575 : Nat := 118140960795 + 4047575 * 2 ^ 59
def prefixEnd_4047575 : Nat := 4983230072969 + 3 ^ 40 * 4047575 * 2
def baseEnd_4047575 : Nat := 461855880027134795088455

theorem tailTrace_4047575 : CollatzResearch.WordTrace tailWord_4047575 prefixEnd_4047575 461855880027134795088455 := by
  unfold tailWord_4047575
  simp only [CollatzResearch.WordTrace]
  refine ⟨147627188311334520620232179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98418125540889680413488119 147627188311334520620232179)
  ·
    refine ⟨221440782467001780930348269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147627188311334520620232179 221440782467001780930348269)
    ·
      refine ⟨83040293425125667848880601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221440782467001780930348269 83040293425125667848880601)
      ·
        refine ⟨62280220068844250886660451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83040293425125667848880601 62280220068844250886660451)
        ·
          refine ⟨93420330103266376329990677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62280220068844250886660451 93420330103266376329990677)
          ·
            refine ⟨4379077973590611390468313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93420330103266376329990677 4379077973590611390468313)
            ·
              refine ⟨3284308480192958542851235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379077973590611390468313 3284308480192958542851235)
              ·
                refine ⟨4926462720289437814276853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284308480192958542851235 4926462720289437814276853)
                ·
                  refine ⟨461855880027134795088455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926462720289437814276853 461855880027134795088455)
                  ·
                    rfl

theorem cell22_4047575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 5].length) (baseStart_4047575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047575 prefixEnd_4047575 := by exact prefixLift 4047575
  have htrace : WordTrace (prefixWord ++ tailWord_4047575) baseStart_4047575 baseEnd_4047575 := by
    simpa [prefixWord, tailWord_4047575, baseEnd_4047575] using wordTrace_append hprefix tailTrace_4047575
  have hstable : (prefixWord ++ tailWord_4047575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047575).length < 2 ^ (prefixWord ++ tailWord_4047575).sum := by decide
  have hdescent : baseEnd_4047575 < baseStart_4047575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047588 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_4047588 : Nat := 118140960795 + 4047588 * 2 ^ 59
def prefixEnd_4047588 : Nat := 4983230072969 + 3 ^ 40 * 4047588 * 2
def baseEnd_4047588 : Nat := 1385572090247076684690325

theorem tailTrace_4047588 : CollatzResearch.WordTrace tailWord_4047588 prefixEnd_4047588 1385572090247076684690325 := by
  unfold tailWord_4047588
  simp only [CollatzResearch.WordTrace]
  refine ⟨73813831230143711920227709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98418441640191615893636945 73813831230143711920227709)
  ·
    refine ⟨27680186711303891970085391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73813831230143711920227709 27680186711303891970085391)
    ·
      refine ⟨41520280066955837955128087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27680186711303891970085391 41520280066955837955128087)
      ·
        refine ⟨62280420100433756932692131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41520280066955837955128087 62280420100433756932692131)
        ·
          refine ⟨93420630150650635399038197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62280420100433756932692131 93420630150650635399038197)
          ·
            refine ⟨8758184076623497068659831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93420630150650635399038197 8758184076623497068659831)
            ·
              refine ⟨13137276114935245602989747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758184076623497068659831 13137276114935245602989747)
              ·
                refine ⟨19705914172402868404484621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13137276114935245602989747 19705914172402868404484621)
                ·
                  refine ⟨7389717814651075651681733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19705914172402868404484621 7389717814651075651681733)
                  ·
                    refine ⟨1385572090247076684690325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389717814651075651681733 1385572090247076684690325)
                    ·
                      rfl

theorem cell22_4047588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_4047588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047588 prefixEnd_4047588 := by exact prefixLift 4047588
  have htrace : WordTrace (prefixWord ++ tailWord_4047588) baseStart_4047588 baseEnd_4047588 := by
    simpa [prefixWord, tailWord_4047588, baseEnd_4047588] using wordTrace_append hprefix tailTrace_4047588
  have hstable : (prefixWord ++ tailWord_4047588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047588).length < 2 ^ (prefixWord ++ tailWord_4047588).sum := by decide
  have hdescent : baseEnd_4047588 < baseStart_4047588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047603 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 4]
def baseStart_4047603 : Nat := 118140960795 + 4047603 * 2 ^ 59
def prefixEnd_4047603 : Nat := 4983230072969 + 3 ^ 40 * 4047603 * 2
def baseEnd_4047603 : Nat := 461859075017873881855093

theorem tailTrace_4047603 : CollatzResearch.WordTrace tailWord_4047603 prefixEnd_4047603 461859075017873881855093 := by
  unfold tailWord_4047603
  simp only [CollatzResearch.WordTrace]
  refine ⟨147628209555233081402251463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98418806370155387601500975 147628209555233081402251463)
  ·
    refine ⟨221442314332849622103377195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147628209555233081402251463 221442314332849622103377195)
    ·
      refine ⟨332163471499274433155065793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221442314332849622103377195 332163471499274433155065793)
      ·
        refine ⟨249122603624455824866299345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332163471499274433155065793 249122603624455824866299345)
        ·
          refine ⟨186841952718341868649724509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249122603624455824866299345 186841952718341868649724509)
          ·
            refine ⟨70065732269378200743646691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186841952718341868649724509 70065732269378200743646691)
            ·
              refine ⟨105098598404067301115470037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70065732269378200743646691 105098598404067301115470037)
              ·
                refine ⟨2463248400095327369893829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105098598404067301115470037 2463248400095327369893829)
                ·
                  refine ⟨461859075017873881855093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463248400095327369893829 461859075017873881855093)
                  ·
                    rfl

theorem cell22_4047603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 4].length) (baseStart_4047603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047603 prefixEnd_4047603 := by exact prefixLift 4047603
  have htrace : WordTrace (prefixWord ++ tailWord_4047603) baseStart_4047603 baseEnd_4047603 := by
    simpa [prefixWord, tailWord_4047603, baseEnd_4047603] using wordTrace_append hprefix tailTrace_4047603
  have hstable : (prefixWord ++ tailWord_4047603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047603).length < 2 ^ (prefixWord ++ tailWord_4047603).sum := by decide
  have hdescent : baseEnd_4047603 < baseStart_4047603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047620 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_4047620 : Nat := 118140960795 + 4047620 * 2 ^ 59
def prefixEnd_4047620 : Nat := 4983230072969 + 3 ^ 40 * 4047620 * 2
def baseEnd_4047620 : Nat := 461861014833679755963409

theorem tailTrace_4047620 : CollatzResearch.WordTrace tailWord_4047620 prefixEnd_4047620 461861014833679755963409 := by
  unfold tailWord_4047620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73814414798085746652810157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98419219730780995537080209 73814414798085746652810157)
  ·
    refine ⟨27680405549282154994803809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73814414798085746652810157 27680405549282154994803809)
    ·
      refine ⟨20760304161961616246102857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27680405549282154994803809 20760304161961616246102857)
      ·
        refine ⟨15570228121471212184577143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20760304161961616246102857 15570228121471212184577143)
        ·
          refine ⟨23355342182206818276865715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570228121471212184577143 23355342182206818276865715)
          ·
            refine ⟨35033013273310227415298573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23355342182206818276865715 35033013273310227415298573)
            ·
              refine ⟨13137379977491335280736965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35033013273310227415298573 13137379977491335280736965)
              ·
                refine ⟨2463258745779625365138181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13137379977491335280736965 2463258745779625365138181)
                ·
                  refine ⟨461861014833679755963409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463258745779625365138181 461861014833679755963409)
                  ·
                    rfl

theorem cell22_4047620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_4047620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047620 prefixEnd_4047620 := by exact prefixLift 4047620
  have htrace : WordTrace (prefixWord ++ tailWord_4047620) baseStart_4047620 baseEnd_4047620 := by
    simpa [prefixWord, tailWord_4047620, baseEnd_4047620] using wordTrace_append hprefix tailTrace_4047620
  have hstable : (prefixWord ++ tailWord_4047620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047620).length < 2 ^ (prefixWord ++ tailWord_4047620).sum := by decide
  have hdescent : baseEnd_4047620 < baseStart_4047620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047650 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_4047650 : Nat := 118140960795 + 4047650 * 2 ^ 59
def prefixEnd_4047650 : Nat := 4983230072969 + 3 ^ 40 * 4047650 * 2
def baseEnd_4047650 : Nat := 1385593314114129189640135

theorem tailTrace_4047650 : CollatzResearch.WordTrace tailWord_4047650 prefixEnd_4047650 1385593314114129189640135 := by
  unfold tailWord_4047650
  simp only [CollatzResearch.WordTrace]
  refine ⟨36907480946515702107303101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98419949190708538952808269 36907480946515702107303101)
  ·
    refine ⟨13840305354943388290238663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36907480946515702107303101 13840305354943388290238663)
    ·
      refine ⟨20760458032415082435357995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840305354943388290238663 20760458032415082435357995)
      ·
        refine ⟨31140687048622623653036993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20760458032415082435357995 31140687048622623653036993)
        ·
          refine ⟨23355515286466967739777745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31140687048622623653036993 23355515286466967739777745)
          ·
            refine ⟨17516636464850225804833309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23355515286466967739777745 17516636464850225804833309)
            ·
              refine ⟨6568738674318834676812491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17516636464850225804833309 6568738674318834676812491)
              ·
                refine ⟨9853108011478252015218737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568738674318834676812491 9853108011478252015218737)
                ·
                  refine ⟨7389831008608689011414053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9853108011478252015218737 7389831008608689011414053)
                  ·
                    refine ⟨1385593314114129189640135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7389831008608689011414053 1385593314114129189640135)
                    ·
                      rfl

theorem cell22_4047650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_4047650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047650 prefixEnd_4047650 := by exact prefixLift 4047650
  have htrace : WordTrace (prefixWord ++ tailWord_4047650) baseStart_4047650 baseEnd_4047650 := by
    simpa [prefixWord, tailWord_4047650, baseEnd_4047650] using wordTrace_append hprefix tailTrace_4047650
  have hstable : (prefixWord ++ tailWord_4047650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047650).length < 2 ^ (prefixWord ++ tailWord_4047650).sum := by decide
  have hdescent : baseEnd_4047650 < baseStart_4047650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047686 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4047686 : Nat := 118140960795 + 4047686 * 2 ^ 59
def prefixEnd_4047686 : Nat := 4983230072969 + 3 ^ 40 * 4047686 * 2
def baseEnd_4047686 : Nat := 1385605637649837095740025

theorem tailTrace_4047686 : CollatzResearch.WordTrace tailWord_4047686 prefixEnd_4047686 1385605637649837095740025 := by
  unfold tailWord_4047686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613476150435387080547591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98420824542621591051681941 4613476150435387080547591)
  ·
    refine ⟨6920214225653080620821387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4613476150435387080547591 6920214225653080620821387)
    ·
      refine ⟨10380321338479620931232081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6920214225653080620821387 10380321338479620931232081)
      ·
        refine ⟨7785241003859715698424061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10380321338479620931232081 7785241003859715698424061)
        ·
          refine ⟨2919465376447393386909023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7785241003859715698424061 2919465376447393386909023)
          ·
            refine ⟨4379198064671090080363535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919465376447393386909023 4379198064671090080363535)
            ·
              refine ⟨6568797097006635120545303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379198064671090080363535 6568797097006635120545303)
              ·
                refine ⟨9853195645509952680817955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568797097006635120545303 9853195645509952680817955)
                ·
                  refine ⟨14779793468264929021226933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9853195645509952680817955 14779793468264929021226933)
                  ·
                    refine ⟨1385605637649837095740025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14779793468264929021226933 1385605637649837095740025)
                    ·
                      rfl

theorem cell22_4047686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4047686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047686 prefixEnd_4047686 := by exact prefixLift 4047686
  have htrace : WordTrace (prefixWord ++ tailWord_4047686) baseStart_4047686 baseEnd_4047686 := by
    simpa [prefixWord, tailWord_4047686, baseEnd_4047686] using wordTrace_append hprefix tailTrace_4047686
  have hstable : (prefixWord ++ tailWord_4047686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047686).length < 2 ^ (prefixWord ++ tailWord_4047686).sum := by decide
  have hdescent : baseEnd_4047686 < baseStart_4047686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047783 : List Nat := [1, 1, 6, 1, 13]
def baseStart_4047783 : Nat := 118140960795 + 4047783 * 2 ^ 59
def prefixEnd_4047783 : Nat := 4983230072969 + 3 ^ 40 * 4047783 * 2
def baseEnd_4047783 : Nat := 5702217459803132411789

theorem tailTrace_4047783 : CollatzResearch.WordTrace tailWord_4047783 prefixEnd_4047783 5702217459803132411789 := by
  unfold tailWord_4047783
  simp only [CollatzResearch.WordTrace]
  refine ⟨147634774694580972143804003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98423183129720648095869335 147634774694580972143804003)
  ·
    refine ⟨221452162041871458215706005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147634774694580972143804003 221452162041871458215706005)
    ·
      refine ⟨10380570095712724603861219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221452162041871458215706005 10380570095712724603861219)
      ·
        refine ⟨15570855143569086905791829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380570095712724603861219 15570855143569086905791829)
        ·
          refine ⟨5702217459803132411789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15570855143569086905791829 5702217459803132411789)
          ·
            rfl

theorem cell22_4047783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 13].length) (baseStart_4047783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047783 prefixEnd_4047783 := by exact prefixLift 4047783
  have htrace : WordTrace (prefixWord ++ tailWord_4047783) baseStart_4047783 baseEnd_4047783 := by
    simpa [prefixWord, tailWord_4047783, baseEnd_4047783] using wordTrace_append hprefix tailTrace_4047783
  have hstable : (prefixWord ++ tailWord_4047783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047783).length < 2 ^ (prefixWord ++ tailWord_4047783).sum := by decide
  have hdescent : baseEnd_4047783 < baseStart_4047783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047800 : List Nat := [2, 1, 2, 1, 2, 6, 1, 7]
def baseStart_4047800 : Nat := 118140960795 + 4047800 * 2 ^ 59
def prefixEnd_4047800 : Nat := 4983230072969 + 3 ^ 40 * 4047800 * 2
def baseEnd_4047800 : Nat := 153960518019953199821075

theorem tailTrace_4047800 : CollatzResearch.WordTrace tailWord_4047800 prefixEnd_4047800 153960518019953199821075 := by
  unfold tailWord_4047800
  simp only [CollatzResearch.WordTrace]
  refine ⟨73817697367759692023586427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98423596490346256031448569 73817697367759692023586427)
  ·
    refine ⟨110726546051639538035379641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73817697367759692023586427 110726546051639538035379641)
    ·
      refine ⟨83044909538729653526534731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110726546051639538035379641 83044909538729653526534731)
      ·
        refine ⟨124567364308094480289802097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83044909538729653526534731 124567364308094480289802097)
        ·
          refine ⟨93425523231070860217351573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124567364308094480289802097 93425523231070860217351573)
          ·
            refine ⟨4379321401456446572688355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93425523231070860217351573 4379321401456446572688355)
            ·
              refine ⟨6568982102184669859032533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379321401456446572688355 6568982102184669859032533)
              ·
                refine ⟨153960518019953199821075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6568982102184669859032533 153960518019953199821075)
                ·
                  rfl

theorem cell22_4047800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_4047800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047800 prefixEnd_4047800 := by exact prefixLift 4047800
  have htrace : WordTrace (prefixWord ++ tailWord_4047800) baseStart_4047800 baseEnd_4047800 := by
    simpa [prefixWord, tailWord_4047800, baseEnd_4047800] using wordTrace_append hprefix tailTrace_4047800
  have hstable : (prefixWord ++ tailWord_4047800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047800).length < 2 ^ (prefixWord ++ tailWord_4047800).sum := by decide
  have hdescent : baseEnd_4047800 < baseStart_4047800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047815 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 5, 3]
def baseStart_4047815 : Nat := 118140960795 + 4047815 * 2 ^ 59
def prefixEnd_4047815 : Nat := 4983230072969 + 3 ^ 40 * 4047815 * 2
def baseEnd_4047815 : Nat := 1385649796986123759264629

theorem tailTrace_4047815 : CollatzResearch.WordTrace tailWord_4047815 prefixEnd_4047815 1385649796986123759264629 := by
  unfold tailWord_4047815
  simp only [CollatzResearch.WordTrace]
  refine ⟨147635941830465041608968899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98423961220310027739312599 147635941830465041608968899)
  ·
    refine ⟨221453912745697562413453349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147635941830465041608968899 221453912745697562413453349)
    ·
      refine ⟨41522608639818292952522503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221453912745697562413453349 41522608639818292952522503)
      ·
        refine ⟨62283912959727439428783755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41522608639818292952522503 62283912959727439428783755)
        ·
          refine ⟨93425869439591159143175633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62283912959727439428783755 93425869439591159143175633)
          ·
            refine ⟨70069402079693369357381725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93425869439591159143175633 70069402079693369357381725)
            ·
              refine ⟨26276025779885013509018147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70069402079693369357381725 26276025779885013509018147)
              ·
                refine ⟨39414038669827520263527221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26276025779885013509018147 39414038669827520263527221)
                ·
                  refine ⟨3695066125296330024705677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39414038669827520263527221 3695066125296330024705677)
                  ·
                    refine ⟨1385649796986123759264629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695066125296330024705677 1385649796986123759264629)
                    ·
                      rfl

theorem cell22_4047815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_4047815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047815 prefixEnd_4047815 := by exact prefixLift 4047815
  have htrace : WordTrace (prefixWord ++ tailWord_4047815) baseStart_4047815 baseEnd_4047815 := by
    simpa [prefixWord, tailWord_4047815, baseEnd_4047815] using wordTrace_append hprefix tailTrace_4047815
  have hstable : (prefixWord ++ tailWord_4047815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047815).length < 2 ^ (prefixWord ++ tailWord_4047815).sum := by decide
  have hdescent : baseEnd_4047815 < baseStart_4047815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047907 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 6]
def baseStart_4047907 : Nat := 118140960795 + 4047907 * 2 ^ 59
def prefixEnd_4047907 : Nat := 4983230072969 + 3 ^ 40 * 4047907 * 2
def baseEnd_4047907 : Nat := 461893763488755395321449

theorem tailTrace_4047907 : CollatzResearch.WordTrace tailWord_4047907 prefixEnd_4047907 461893763488755395321449 := by
  unfold tailWord_4047907
  simp only [CollatzResearch.WordTrace]
  refine ⟨147639297346131741321317975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98426198230754494214211983 147639297346131741321317975)
  ·
    refine ⟨221458946019197611981976963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147639297346131741321317975 221458946019197611981976963)
    ·
      refine ⟨332188419028796417972965445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221458946019197611981976963 332188419028796417972965445)
      ·
        refine ⟨62285328567899328369931021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332188419028796417972965445 62285328567899328369931021)
        ·
          refine ⟨23356998212962248138724133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62285328567899328369931021 23356998212962248138724133)
          ·
            refine ⟨4379437164930421526010775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23356998212962248138724133 4379437164930421526010775)
            ·
              refine ⟨6569155747395632289016163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379437164930421526010775 6569155747395632289016163)
              ·
                refine ⟨9853733621093448433524245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569155747395632289016163 9853733621093448433524245)
                ·
                  refine ⟨461893763488755395321449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9853733621093448433524245 461893763488755395321449)
                  ·
                    rfl

theorem cell22_4047907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 6].length) (baseStart_4047907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047907 prefixEnd_4047907 := by exact prefixLift 4047907
  have htrace : WordTrace (prefixWord ++ tailWord_4047907) baseStart_4047907 baseEnd_4047907 := by
    simpa [prefixWord, tailWord_4047907, baseEnd_4047907] using wordTrace_append hprefix tailTrace_4047907
  have hstable : (prefixWord ++ tailWord_4047907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047907).length < 2 ^ (prefixWord ++ tailWord_4047907).sum := by decide
  have hdescent : baseEnd_4047907 < baseStart_4047907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047920 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_4047920 : Nat := 118140960795 + 4047920 * 2 ^ 59
def prefixEnd_4047920 : Nat := 4983230072969 + 3 ^ 40 * 4047920 * 2
def baseEnd_4047920 : Nat := 1385685740631938485389307

theorem tailTrace_4047920 : CollatzResearch.WordTrace tailWord_4047920 prefixEnd_4047920 1385685740631938485389307 := by
  unfold tailWord_4047920
  simp only [CollatzResearch.WordTrace]
  refine ⟨73819885747542322270770607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98426514330056429694360809 73819885747542322270770607)
  ·
    refine ⟨110729828621313483406155911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73819885747542322270770607 110729828621313483406155911)
    ·
      refine ⟨166094742931970225109233867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110729828621313483406155911 166094742931970225109233867)
      ·
        refine ⟨249142114397955337663850801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166094742931970225109233867 249142114397955337663850801)
        ·
          refine ⟨186856585798466503247888101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249142114397955337663850801 186856585798466503247888101)
          ·
            refine ⟨35035609837212469358979019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186856585798466503247888101 35035609837212469358979019)
            ·
              refine ⟨52553414755818704038468529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35035609837212469358979019 52553414755818704038468529)
              ·
                refine ⟨39415061066864028028851397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52553414755818704038468529 39415061066864028028851397)
                ·
                  refine ⟨7390323950037005255409637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39415061066864028028851397 7390323950037005255409637)
                  ·
                    refine ⟨1385685740631938485389307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390323950037005255409637 1385685740631938485389307)
                    ·
                      rfl

theorem cell22_4047920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_4047920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047920 prefixEnd_4047920 := by exact prefixLift 4047920
  have htrace : WordTrace (prefixWord ++ tailWord_4047920) baseStart_4047920 baseEnd_4047920 := by
    simpa [prefixWord, tailWord_4047920, baseEnd_4047920] using wordTrace_append hprefix tailTrace_4047920
  have hstable : (prefixWord ++ tailWord_4047920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047920).length < 2 ^ (prefixWord ++ tailWord_4047920).sum := by decide
  have hdescent : baseEnd_4047920 < baseStart_4047920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047926 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4047926 : Nat := 118140960795 + 4047926 * 2 ^ 59
def prefixEnd_4047926 : Nat := 4983230072969 + 3 ^ 40 * 4047926 * 2
def baseEnd_4047926 : Nat := 1385687794554556469739289

theorem tailTrace_4047926 : CollatzResearch.WordTrace tailWord_4047926 prefixEnd_4047926 1385687794554556469739289 := by
  unfold tailWord_4047926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227499395816431722891227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98426660222041938377506421 9227499395816431722891227)
  ·
    refine ⟨13841249093724647584336841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9227499395816431722891227 13841249093724647584336841)
    ·
      refine ⟨10380936820293485688252631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13841249093724647584336841 10380936820293485688252631)
      ·
        refine ⟨15571405230440228532378947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380936820293485688252631 15571405230440228532378947)
        ·
          refine ⟨23357107845660342798568421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15571405230440228532378947 23357107845660342798568421)
          ·
            refine ⟨4379457721061314274731579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23357107845660342798568421 4379457721061314274731579)
            ·
              refine ⟨6569186581591971412097369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379457721061314274731579 6569186581591971412097369)
              ·
                refine ⟨4926889936193978559073027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6569186581591971412097369 4926889936193978559073027)
                ·
                  refine ⟨7390334904290967838609541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926889936193978559073027 7390334904290967838609541)
                  ·
                    refine ⟨1385687794554556469739289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390334904290967838609541 1385687794554556469739289)
                    ·
                      rfl

theorem cell22_4047926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4047926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047926 prefixEnd_4047926 := by exact prefixLift 4047926
  have htrace : WordTrace (prefixWord ++ tailWord_4047926) baseStart_4047926 baseEnd_4047926 := by
    simpa [prefixWord, tailWord_4047926, baseEnd_4047926] using wordTrace_append hprefix tailTrace_4047926
  have hstable : (prefixWord ++ tailWord_4047926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047926).length < 2 ^ (prefixWord ++ tailWord_4047926).sum := by decide
  have hdescent : baseEnd_4047926 < baseStart_4047926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047958 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4047958 : Nat := 118140960795 + 4047958 * 2 ^ 59
def prefixEnd_4047958 : Nat := 4983230072969 + 3 ^ 40 * 4047958 * 2
def baseEnd_4047958 : Nat := 461899582936173017646397

theorem tailTrace_4047958 : CollatzResearch.WordTrace tailWord_4047958 prefixEnd_4047958 461899582936173017646397 := by
  unfold tailWord_4047958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9227572341809186064464033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98427438312631318020949685 9227572341809186064464033)
  ·
    refine ⟨6920679256356889548348025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9227572341809186064464033 6920679256356889548348025)
    ·
      refine ⟨5190509442267667161261019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6920679256356889548348025 5190509442267667161261019)
      ·
        refine ⟨7785764163401500741891529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190509442267667161261019 7785764163401500741891529)
        ·
          refine ⟨5839323122551125556418647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7785764163401500741891529 5839323122551125556418647)
          ·
            refine ⟨8758984683826688334627971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839323122551125556418647 8758984683826688334627971)
            ·
              refine ⟨13138477025740032501941957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8758984683826688334627971 13138477025740032501941957)
              ·
                refine ⟨2463464442326256094114117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13138477025740032501941957 2463464442326256094114117)
                ·
                  refine ⟨461899582936173017646397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463464442326256094114117 461899582936173017646397)
                  ·
                    rfl

theorem cell22_4047958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4047958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047958 prefixEnd_4047958 := by exact prefixLift 4047958
  have htrace : WordTrace (prefixWord ++ tailWord_4047958) baseStart_4047958 baseEnd_4047958 := by
    simpa [prefixWord, tailWord_4047958, baseEnd_4047958] using wordTrace_append hprefix tailTrace_4047958
  have hstable : (prefixWord ++ tailWord_4047958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047958).length < 2 ^ (prefixWord ++ tailWord_4047958).sum := by decide
  have hdescent : baseEnd_4047958 < baseStart_4047958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4047967 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 3, 3]
def baseStart_4047967 : Nat := 118140960795 + 4047967 * 2 ^ 59
def prefixEnd_4047967 : Nat := 4983230072969 + 3 ^ 40 * 4047967 * 2
def baseEnd_4047967 : Nat := 1385701829692446029464163

theorem tailTrace_4047967 : CollatzResearch.WordTrace tailWord_4047967 prefixEnd_4047967 1385701829692446029464163 := by
  unfold tailWord_4047967
  simp only [CollatzResearch.WordTrace]
  refine ⟨147641485725914371568502155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98427657150609581045668103 147641485725914371568502155)
  ·
    refine ⟨221462228588871557352753233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147641485725914371568502155 221462228588871557352753233)
    ·
      refine ⟨166096671441653668014564925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221462228588871557352753233 166096671441653668014564925)
      ·
        refine ⟨62286251790620125505461847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166096671441653668014564925 62286251790620125505461847)
        ·
          refine ⟨93429377685930188258192771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62286251790620125505461847 93429377685930188258192771)
          ·
            refine ⟨140144066528895282387289157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93429377685930188258192771 140144066528895282387289157)
            ·
              refine ⟨26277012474167865447616717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140144066528895282387289157 26277012474167865447616717)
              ·
                refine ⟨9853879677812949542856269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26277012474167865447616717 9853879677812949542856269)
                ·
                  refine ⟨3695204879179856078571101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9853879677812949542856269 3695204879179856078571101)
                  ·
                    refine ⟨1385701829692446029464163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695204879179856078571101 1385701829692446029464163)
                    ·
                      rfl

theorem cell22_4047967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_4047967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4047967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4047967 prefixEnd_4047967 := by exact prefixLift 4047967
  have htrace : WordTrace (prefixWord ++ tailWord_4047967) baseStart_4047967 baseEnd_4047967 := by
    simpa [prefixWord, tailWord_4047967, baseEnd_4047967] using wordTrace_append hprefix tailTrace_4047967
  have hstable : (prefixWord ++ tailWord_4047967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4047967).length < 2 ^ (prefixWord ++ tailWord_4047967).sum := by decide
  have hdescent : baseEnd_4047967 < baseStart_4047967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4047967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048001 : List Nat := [1, 2, 4, 2, 2, 1, 1, 5, 1, 3]
def baseStart_4048001 : Nat := 118140960795 + 4048001 * 2 ^ 59
def prefixEnd_4048001 : Nat := 4983230072969 + 3 ^ 40 * 4048001 * 2
def baseEnd_4048001 : Nat := 1385713468587281274114059

theorem tailTrace_4048001 : CollatzResearch.WordTrace tailWord_4048001 prefixEnd_4048001 1385713468587281274114059 := by
  unfold tailWord_4048001
  simp only [CollatzResearch.WordTrace]
  refine ⟨147642725807791195375239857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98428483871860796916826571 147642725807791195375239857)
  ·
    refine ⟨110732044355843396531429893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147642725807791195375239857 110732044355843396531429893)
    ·
      refine ⟨20762258316720636849643105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110732044355843396531429893 20762258316720636849643105)
      ·
        refine ⟨15571693737540477637232329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20762258316720636849643105 15571693737540477637232329)
        ·
          refine ⟨11678770303155358227924247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15571693737540477637232329 11678770303155358227924247)
          ·
            refine ⟨17518155454733037341886371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678770303155358227924247 17518155454733037341886371)
            ·
              refine ⟨26277233182099556012829557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17518155454733037341886371 26277233182099556012829557)
              ·
                refine ⟨2463490610821833376202771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26277233182099556012829557 2463490610821833376202771)
                ·
                  refine ⟨3695235916232750064304157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463490610821833376202771 3695235916232750064304157)
                  ·
                    refine ⟨1385713468587281274114059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695235916232750064304157 1385713468587281274114059)
                    ·
                      rfl

theorem cell22_4048001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_4048001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048001 prefixEnd_4048001 := by exact prefixLift 4048001
  have htrace : WordTrace (prefixWord ++ tailWord_4048001) baseStart_4048001 baseEnd_4048001 := by
    simpa [prefixWord, tailWord_4048001, baseEnd_4048001] using wordTrace_append hprefix tailTrace_4048001
  have hstable : (prefixWord ++ tailWord_4048001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048001).length < 2 ^ (prefixWord ++ tailWord_4048001).sum := by decide
  have hdescent : baseEnd_4048001 < baseStart_4048001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048014 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_4048014 : Nat := 118140960795 + 4048014 * 2 ^ 59
def prefixEnd_4048014 : Nat := 4983230072969 + 3 ^ 40 * 4048014 * 2
def baseEnd_4048014 : Nat := 461905972917651191179673

theorem tailTrace_4048014 : CollatzResearch.WordTrace tailWord_4048014 prefixEnd_4048014 461905972917651191179673 := by
  unfold tailWord_4048014
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455399994593012324432887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98428799971162732396975397 18455399994593012324432887)
  ·
    refine ⟨27683099991889518486649331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455399994593012324432887 27683099991889518486649331)
    ·
      refine ⟨41524649987834277729973997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27683099991889518486649331 41524649987834277729973997)
      ·
        refine ⟨15571743745437854148740249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41524649987834277729973997 15571743745437854148740249)
        ·
          refine ⟨11678807809078390611555187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15571743745437854148740249 11678807809078390611555187)
          ·
            refine ⟨17518211713617585917332781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678807809078390611555187 17518211713617585917332781)
            ·
              refine ⟨6569329392606594718999793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17518211713617585917332781 6569329392606594718999793)
              ·
                refine ⟨4926997044454946039249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6569329392606594718999793 4926997044454946039249845)
                ·
                  refine ⟨461905972917651191179673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4926997044454946039249845 461905972917651191179673)
                  ·
                    rfl

theorem cell22_4048014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_4048014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048014 prefixEnd_4048014 := by exact prefixLift 4048014
  have htrace : WordTrace (prefixWord ++ tailWord_4048014) baseStart_4048014 baseEnd_4048014 := by
    simpa [prefixWord, tailWord_4048014, baseEnd_4048014] using wordTrace_append hprefix tailTrace_4048014
  have hstable : (prefixWord ++ tailWord_4048014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048014).length < 2 ^ (prefixWord ++ tailWord_4048014).sum := by decide
  have hdescent : baseEnd_4048014 < baseStart_4048014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048031 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 5]
def baseStart_4048031 : Nat := 118140960795 + 4048031 * 2 ^ 59
def prefixEnd_4048031 : Nat := 4983230072969 + 3 ^ 40 * 4048031 * 2
def baseEnd_4048031 : Nat := 461907912733457065287989

theorem tailTrace_4048031 : CollatzResearch.WordTrace tailWord_4048031 prefixEnd_4048031 461907912733457065287989 := by
  unfold tailWord_4048031
  simp only [CollatzResearch.WordTrace]
  refine ⟨147643819997682510498831947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98429213331788340332554631 147643819997682510498831947)
  ·
    refine ⟨221465729996523765748247921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147643819997682510498831947 221465729996523765748247921)
    ·
      refine ⟨166099297497392824311185941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221465729996523765748247921 166099297497392824311185941)
      ·
        refine ⟨7785904570190288639586841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166099297497392824311185941 7785904570190288639586841)
        ·
          refine ⟨5839428427642716479690131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7785904570190288639586841 5839428427642716479690131)
          ·
            refine ⟨8759142641464074719535197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839428427642716479690131 8759142641464074719535197)
            ·
              refine ⟨3284678490549028019825699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8759142641464074719535197 3284678490549028019825699)
              ·
                refine ⟨4927017735823542029738549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284678490549028019825699 4927017735823542029738549)
                ·
                  refine ⟨461907912733457065287989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4927017735823542029738549 461907912733457065287989)
                  ·
                    rfl

theorem cell22_4048031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 5].length) (baseStart_4048031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048031 prefixEnd_4048031 := by exact prefixLift 4048031
  have htrace : WordTrace (prefixWord ++ tailWord_4048031) baseStart_4048031 baseEnd_4048031 := by
    simpa [prefixWord, tailWord_4048031, baseEnd_4048031] using wordTrace_append hprefix tailTrace_4048031
  have hstable : (prefixWord ++ tailWord_4048031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048031).length < 2 ^ (prefixWord ++ tailWord_4048031).sum := by decide
  have hdescent : baseEnd_4048031 < baseStart_4048031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048072 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_4048072 : Nat := 118140960795 + 4048072 * 2 ^ 59
def prefixEnd_4048072 : Nat := 4983230072969 + 3 ^ 40 * 4048072 * 2
def baseEnd_4048072 : Nat := 1385737773338260755588841

theorem tailTrace_4048072 : CollatzResearch.WordTrace tailWord_4048072 prefixEnd_4048072 1385737773338260755588841 := by
  unfold tailWord_4048072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73822657695266987250537235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98430210260355983000716313 73822657695266987250537235)
  ·
    refine ⟨110733986542900480875805853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73822657695266987250537235 110733986542900480875805853)
    ·
      refine ⟨41525244953587680328427195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110733986542900480875805853 41525244953587680328427195)
      ·
        refine ⟨62287867430381520492640793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41525244953587680328427195 62287867430381520492640793)
        ·
          refine ⟨46715900572786140369480595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62287867430381520492640793 46715900572786140369480595)
          ·
            refine ⟨70073850859179210554220893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46715900572786140369480595 70073850859179210554220893)
            ·
              refine ⟨26277694072192203957832835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70073850859179210554220893 26277694072192203957832835)
              ·
                refine ⟨39416541108288305936749253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26277694072192203957832835 39416541108288305936749253)
                ·
                  refine ⟨7390601457804057363140485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39416541108288305936749253 7390601457804057363140485)
                  ·
                    refine ⟨1385737773338260755588841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7390601457804057363140485 1385737773338260755588841)
                    ·
                      rfl

theorem cell22_4048072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_4048072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048072 prefixEnd_4048072 := by exact prefixLift 4048072
  have htrace : WordTrace (prefixWord ++ tailWord_4048072) baseStart_4048072 baseEnd_4048072 := by
    simpa [prefixWord, tailWord_4048072, baseEnd_4048072] using wordTrace_append hprefix tailTrace_4048072
  have hstable : (prefixWord ++ tailWord_4048072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048072).length < 2 ^ (prefixWord ++ tailWord_4048072).sum := by decide
  have hdescent : baseEnd_4048072 < baseStart_4048072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048074 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_4048074 : Nat := 118140960795 + 4048074 * 2 ^ 59
def prefixEnd_4048074 : Nat := 4983230072969 + 3 ^ 40 * 4048074 * 2
def baseEnd_4048074 : Nat := 1385738457979133417038835

theorem tailTrace_4048074 : CollatzResearch.WordTrace tailWord_4048074 prefixEnd_4048074 1385738457979133417038835 := by
  unfold tailWord_4048074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36911347084131682210661819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98430258891017819228431517 36911347084131682210661819)
  ·
    refine ⟨55367020626197523315992729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36911347084131682210661819 55367020626197523315992729)
    ·
      refine ⟨41525265469648142486994547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55367020626197523315992729 41525265469648142486994547)
      ·
        refine ⟨62287898204472213730491821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41525265469648142486994547 62287898204472213730491821)
        ·
          refine ⟨23357961826677080148934433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62287898204472213730491821 23357961826677080148934433)
          ·
            refine ⟨17518471370007810111700825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23357961826677080148934433 17518471370007810111700825)
            ·
              refine ⟨13138853527505857583775619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17518471370007810111700825 13138853527505857583775619)
              ·
                refine ⟨19708280291258786375663429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13138853527505857583775619 19708280291258786375663429)
                ·
                  refine ⟨3695302554611022445436893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19708280291258786375663429 3695302554611022445436893)
                  ·
                    refine ⟨1385738457979133417038835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695302554611022445436893 1385738457979133417038835)
                    ·
                      rfl

theorem cell22_4048074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_4048074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048074 prefixEnd_4048074 := by exact prefixLift 4048074
  have htrace : WordTrace (prefixWord ++ tailWord_4048074) baseStart_4048074 baseEnd_4048074 := by
    simpa [prefixWord, tailWord_4048074, baseEnd_4048074] using wordTrace_append hprefix tailTrace_4048074
  have hstable : (prefixWord ++ tailWord_4048074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048074).length < 2 ^ (prefixWord ++ tailWord_4048074).sum := by decide
  have hdescent : baseEnd_4048074 < baseStart_4048074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048170 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4048170 : Nat := 118140960795 + 4048170 * 2 ^ 59
def prefixEnd_4048170 : Nat := 4983230072969 + 3 ^ 40 * 4048170 * 2
def baseEnd_4048170 : Nat := 1385771320741021166638541

theorem tailTrace_4048170 : CollatzResearch.WordTrace tailWord_4048170 prefixEnd_4048170 1385771320741021166638541 := by
  unfold tailWord_4048170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36912222436044734309535491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98432593162785958158761309 36912222436044734309535491)
  ·
    refine ⟨55368333654067101464303237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36912222436044734309535491 55368333654067101464303237)
    ·
      refine ⟨10381562560137581524556857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55368333654067101464303237 10381562560137581524556857)
      ·
        refine ⟨7786171920103186143417643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10381562560137581524556857 7786171920103186143417643)
        ·
          refine ⟨11679257880154779215126465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7786171920103186143417643 11679257880154779215126465)
          ·
            refine ⟨8759443410116084411344849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679257880154779215126465 8759443410116084411344849)
            ·
              refine ⟨6569582557587063308508637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8759443410116084411344849 6569582557587063308508637)
              ·
                refine ⟨2463593459095148740690739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6569582557587063308508637 2463593459095148740690739)
                ·
                  refine ⟨3695390188642723111036109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463593459095148740690739 3695390188642723111036109)
                  ·
                    refine ⟨1385771320741021166638541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695390188642723111036109 1385771320741021166638541)
                    ·
                      rfl

theorem cell22_4048170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4048170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048170 prefixEnd_4048170 := by exact prefixLift 4048170
  have htrace : WordTrace (prefixWord ++ tailWord_4048170) baseStart_4048170 baseEnd_4048170 := by
    simpa [prefixWord, tailWord_4048170, baseEnd_4048170] using wordTrace_append hprefix tailTrace_4048170
  have hstable : (prefixWord ++ tailWord_4048170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048170).length < 2 ^ (prefixWord ++ tailWord_4048170).sum := by decide
  have hdescent : baseEnd_4048170 < baseStart_4048170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048221 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4048221 : Nat := 118140960795 + 4048221 * 2 ^ 59
def prefixEnd_4048221 : Nat := 4983230072969 + 3 ^ 40 * 4048221 * 2
def baseEnd_4048221 : Nat := 1385788779083274033613385

theorem tailTrace_4048221 : CollatzResearch.WordTrace tailWord_4048221 prefixEnd_4048221 1385788779083274033613385 := by
  unfold tailWord_4048221
  simp only [CollatzResearch.WordTrace]
  refine ⟨147650749866994172948248517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98433833244662781965499011 147650749866994172948248517)
  ·
    refine ⟨27684515600061407427796597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147650749866994172948248517 27684515600061407427796597)
    ·
      refine ⟨2595423337505756946355931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27684515600061407427796597 2595423337505756946355931)
      ·
        refine ⟨3893135006258635419533897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595423337505756946355931 3893135006258635419533897)
        ·
          refine ⟨2919851254693976564650423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3893135006258635419533897 2919851254693976564650423)
          ·
            refine ⟨4379776882040964846975635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919851254693976564650423 4379776882040964846975635)
            ·
              refine ⟨6569665323061447270463453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379776882040964846975635 6569665323061447270463453)
              ·
                refine ⟨2463624496148042726423795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6569665323061447270463453 2463624496148042726423795)
                ·
                  refine ⟨3695436744222064089635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463624496148042726423795 3695436744222064089635693)
                  ·
                    refine ⟨1385788779083274033613385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695436744222064089635693 1385788779083274033613385)
                    ·
                      rfl

theorem cell22_4048221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4048221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048221 prefixEnd_4048221 := by exact prefixLift 4048221
  have htrace : WordTrace (prefixWord ++ tailWord_4048221) baseStart_4048221 baseEnd_4048221 := by
    simpa [prefixWord, tailWord_4048221, baseEnd_4048221] using wordTrace_append hprefix tailTrace_4048221
  have hstable : (prefixWord ++ tailWord_4048221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048221).length < 2 ^ (prefixWord ++ tailWord_4048221).sum := by decide
  have hdescent : baseEnd_4048221 < baseStart_4048221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048224 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_4048224 : Nat := 118140960795 + 4048224 * 2 ^ 59
def prefixEnd_4048224 : Nat := 4983230072969 + 3 ^ 40 * 4048224 * 2
def baseEnd_4048224 : Nat := 1385789806044583025788375

theorem tailTrace_4048224 : CollatzResearch.WordTrace tailWord_4048224 prefixEnd_4048224 1385789806044583025788375 := by
  unfold tailWord_4048224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73825429642991652230303863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98433906190655536307071817 73825429642991652230303863)
  ·
    refine ⟨110738144464487478345455795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73825429642991652230303863 110738144464487478345455795)
    ·
      refine ⟨166107216696731217518183693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110738144464487478345455795 166107216696731217518183693)
      ·
        refine ⟨62290206261274206569318885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166107216696731217518183693 62290206261274206569318885)
        ·
          refine ⟨11679413673988913731747291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62290206261274206569318885 11679413673988913731747291)
          ·
            refine ⟨17519120510983370597620937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679413673988913731747291 17519120510983370597620937)
            ·
              refine ⟨13139340383237527948215703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17519120510983370597620937 13139340383237527948215703)
              ·
                refine ⟨19709010574856291922323555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13139340383237527948215703 19709010574856291922323555)
                ·
                  refine ⟨29563515862284437883485333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19709010574856291922323555 29563515862284437883485333)
                  ·
                    refine ⟨1385789806044583025788375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29563515862284437883485333 1385789806044583025788375)
                    ·
                      rfl

theorem cell22_4048224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_4048224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048224 prefixEnd_4048224 := by exact prefixLift 4048224
  have htrace : WordTrace (prefixWord ++ tailWord_4048224) baseStart_4048224 baseEnd_4048224 := by
    simpa [prefixWord, tailWord_4048224, baseEnd_4048224] using wordTrace_append hprefix tailTrace_4048224
  have hstable : (prefixWord ++ tailWord_4048224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048224).length < 2 ^ (prefixWord ++ tailWord_4048224).sum := by decide
  have hdescent : baseEnd_4048224 < baseStart_4048224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048226 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4048226 : Nat := 118140960795 + 4048226 * 2 ^ 59
def prefixEnd_4048226 : Nat := 4983230072969 + 3 ^ 40 * 4048226 * 2
def baseEnd_4048226 : Nat := 1385790490685455687238369

theorem tailTrace_4048226 : CollatzResearch.WordTrace tailWord_4048226 prefixEnd_4048226 1385790490685455687238369 := by
  unfold tailWord_4048226
  simp only [CollatzResearch.WordTrace]
  refine ⟨36912733057994014700545133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98433954821317372534787021 36912733057994014700545133)
  ·
    refine ⟨13842274896747755512704425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36912733057994014700545133 13842274896747755512704425)
    ·
      refine ⟨10381706172560816634528319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13842274896747755512704425 10381706172560816634528319)
      ·
        refine ⟨15572559258841224951792479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381706172560816634528319 15572559258841224951792479)
        ·
          refine ⟨23358838888261837427688719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15572559258841224951792479 23358838888261837427688719)
          ·
            refine ⟨35038258332392756141533079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23358838888261837427688719 35038258332392756141533079)
            ·
              refine ⟨52557387498589134212299619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35038258332392756141533079 52557387498589134212299619)
              ·
                refine ⟨78836081247883701318449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52557387498589134212299619 78836081247883701318449429)
                ·
                  refine ⟨3695441308494548499302317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78836081247883701318449429 3695441308494548499302317)
                  ·
                    refine ⟨1385790490685455687238369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695441308494548499302317 1385790490685455687238369)
                    ·
                      rfl

theorem cell22_4048226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4048226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048226 prefixEnd_4048226 := by exact prefixLift 4048226
  have htrace : WordTrace (prefixWord ++ tailWord_4048226) baseStart_4048226 baseEnd_4048226 := by
    simpa [prefixWord, tailWord_4048226, baseEnd_4048226] using wordTrace_append hprefix tailTrace_4048226
  have hstable : (prefixWord ++ tailWord_4048226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048226).length < 2 ^ (prefixWord ++ tailWord_4048226).sum := by decide
  have hdescent : baseEnd_4048226 < baseStart_4048226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048228 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_4048228 : Nat := 118140960795 + 4048228 * 2 ^ 59
def prefixEnd_4048228 : Nat := 4983230072969 + 3 ^ 40 * 4048228 * 2
def baseEnd_4048228 : Nat := 461930391775442782896121

theorem tailTrace_4048228 : CollatzResearch.WordTrace tailWord_4048228 prefixEnd_4048228 461930391775442782896121 := by
  unfold tailWord_4048228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73825502588984406571876669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98434003451979208762502225 73825502588984406571876669)
  ·
    refine ⟨27684563470869152464453751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73825502588984406571876669 27684563470869152464453751)
    ·
      refine ⟨41526845206303728696680627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27684563470869152464453751 41526845206303728696680627)
      ·
        refine ⟨62290267809455593045020941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41526845206303728696680627 62290267809455593045020941)
        ·
          refine ⟨23358850428545847391882853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62290267809455593045020941 23358850428545847391882853)
          ·
            refine ⟨4379784455352346385978035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23358850428545847391882853 4379784455352346385978035)
            ·
              refine ⟨6569676683028519578967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379784455352346385978035 6569676683028519578967053)
              ·
                refine ⟨2463628756135694842112645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6569676683028519578967053 2463628756135694842112645)
                ·
                  refine ⟨461930391775442782896121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463628756135694842112645 461930391775442782896121)
                  ·
                    rfl

theorem cell22_4048228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_4048228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048228 prefixEnd_4048228 := by exact prefixLift 4048228
  have htrace : WordTrace (prefixWord ++ tailWord_4048228) baseStart_4048228 baseEnd_4048228 := by
    simpa [prefixWord, tailWord_4048228, baseEnd_4048228] using wordTrace_append hprefix tailTrace_4048228
  have hstable : (prefixWord ++ tailWord_4048228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048228).length < 2 ^ (prefixWord ++ tailWord_4048228).sum := by decide
  have hdescent : baseEnd_4048228 < baseStart_4048228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048245 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 4]
def baseStart_4048245 : Nat := 118140960795 + 4048245 * 2 ^ 59
def prefixEnd_4048245 : Nat := 4983230072969 + 3 ^ 40 * 4048245 * 2
def baseEnd_4048245 : Nat := 461932331591248657004437

theorem tailTrace_4048245 : CollatzResearch.WordTrace tailWord_4048245 prefixEnd_4048245 461932331591248657004437 := by
  unfold tailWord_4048245
  simp only [CollatzResearch.WordTrace]
  refine ⟨147651625218907225047122189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98434416812604816698081459 147651625218907225047122189)
  ·
    refine ⟨55369359457090209392670821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147651625218907225047122189 55369359457090209392670821)
    ·
      refine ⟨10381754898204414261125779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55369359457090209392670821 10381754898204414261125779)
      ·
        refine ⟨15572632347306621391688669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381754898204414261125779 15572632347306621391688669)
        ·
          refine ⟨5839737130239983021883251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15572632347306621391688669 5839737130239983021883251)
          ·
            refine ⟨8759605695359974532824877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839737130239983021883251 8759605695359974532824877)
            ·
              refine ⟨3284852135759990449809329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8759605695359974532824877 3284852135759990449809329)
              ·
                refine ⟨2463639101819992837356997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3284852135759990449809329 2463639101819992837356997)
                ·
                  refine ⟨461932331591248657004437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2463639101819992837356997 461932331591248657004437)
                  ·
                    rfl

theorem cell22_4048245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_4048245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048245 prefixEnd_4048245 := by exact prefixLift 4048245
  have htrace : WordTrace (prefixWord ++ tailWord_4048245) baseStart_4048245 baseEnd_4048245 := by
    simpa [prefixWord, tailWord_4048245, baseEnd_4048245] using wordTrace_append hprefix tailTrace_4048245
  have hstable : (prefixWord ++ tailWord_4048245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048245).length < 2 ^ (prefixWord ++ tailWord_4048245).sum := by decide
  have hdescent : baseEnd_4048245 < baseStart_4048245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048260 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_4048260 : Nat := 118140960795 + 4048260 * 2 ^ 59
def prefixEnd_4048260 : Nat := 4983230072969 + 3 ^ 40 * 4048260 * 2
def baseEnd_4048260 : Nat := 1385802129580290931888265

theorem tailTrace_4048260 : CollatzResearch.WordTrace tailWord_4048260 prefixEnd_4048260 1385802129580290931888265 := by
  unfold tailWord_4048260
  simp only [CollatzResearch.WordTrace]
  refine ⟨73826086156926441304459117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98434781542568588405945489 73826086156926441304459117)
  ·
    refine ⟨27684782308847415489172169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73826086156926441304459117 27684782308847415489172169)
    ·
      refine ⟨20763586731635561616879127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27684782308847415489172169 20763586731635561616879127)
      ·
        refine ⟨31145380097453342425318691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20763586731635561616879127 31145380097453342425318691)
        ·
          refine ⟨46718070146180013637978037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31145380097453342425318691 46718070146180013637978037)
          ·
            refine ⟨4379819076204376278560441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46718070146180013637978037 4379819076204376278560441)
            ·
              refine ⟨3284864307153282208920331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379819076204376278560441 3284864307153282208920331)
              ·
                refine ⟨4927296460729923313380497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284864307153282208920331 4927296460729923313380497)
                ·
                  refine ⟨3695472345547442485035373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4927296460729923313380497 3695472345547442485035373)
                  ·
                    refine ⟨1385802129580290931888265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695472345547442485035373 1385802129580290931888265)
                    ·
                      rfl

theorem cell22_4048260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_4048260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048260 prefixEnd_4048260 := by exact prefixLift 4048260
  have htrace : WordTrace (prefixWord ++ tailWord_4048260) baseStart_4048260 baseEnd_4048260 := by
    simpa [prefixWord, tailWord_4048260, baseEnd_4048260] using wordTrace_append hprefix tailTrace_4048260
  have hstable : (prefixWord ++ tailWord_4048260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048260).length < 2 ^ (prefixWord ++ tailWord_4048260).sum := by decide
  have hdescent : baseEnd_4048260 < baseStart_4048260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048288 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 1, 3]
def baseStart_4048288 : Nat := 118140960795 + 4048288 * 2 ^ 59
def prefixEnd_4048288 : Nat := 4983230072969 + 3 ^ 40 * 4048288 * 2
def baseEnd_4048288 : Nat := 1385811714552508192188179

theorem tailTrace_4048288 : CollatzResearch.WordTrace tailWord_4048288 prefixEnd_4048288 1385811714552508192188179 := by
  unfold tailWord_4048288
  simp only [CollatzResearch.WordTrace]
  refine ⟨73826596778875721695468759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98435462371834295593958345 73826596778875721695468759)
  ·
    refine ⟨110739895168313582543203139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73826596778875721695468759 110739895168313582543203139)
    ·
      refine ⟨166109842752470373814804709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110739895168313582543203139 166109842752470373814804709)
      ·
        refine ⟨31145595516088195090275883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166109842752470373814804709 31145595516088195090275883)
        ·
          refine ⟨46718393274132292635413825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31145595516088195090275883 46718393274132292635413825)
          ·
            refine ⟨35038794955599219476560369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46718393274132292635413825 35038794955599219476560369)
            ·
              refine ⟨26279096216699414607420277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35038794955599219476560369 26279096216699414607420277)
              ·
                refine ⟨2463665270315570119445651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26279096216699414607420277 2463665270315570119445651)
                ·
                  refine ⟨3695497905473355179168477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463665270315570119445651 3695497905473355179168477)
                  ·
                    refine ⟨1385811714552508192188179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695497905473355179168477 1385811714552508192188179)
                    ·
                      rfl

theorem cell22_4048288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_4048288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048288 prefixEnd_4048288 := by exact prefixLift 4048288
  have htrace : WordTrace (prefixWord ++ tailWord_4048288) baseStart_4048288 baseEnd_4048288 := by
    simpa [prefixWord, tailWord_4048288, baseEnd_4048288] using wordTrace_append hprefix tailTrace_4048288
  have hstable : (prefixWord ++ tailWord_4048288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048288).length < 2 ^ (prefixWord ++ tailWord_4048288).sum := by decide
  have hdescent : baseEnd_4048288 < baseStart_4048288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048382 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4048382 : Nat := 118140960795 + 4048382 * 2 ^ 59
def prefixEnd_4048382 : Nat := 4983230072969 + 3 ^ 40 * 4048382 * 2
def baseEnd_4048382 : Nat := 1385843892673523280337891

theorem tailTrace_4048382 : CollatzResearch.WordTrace tailWord_4048382 prefixEnd_4048382 1385843892673523280337891 := by
  unfold tailWord_4048382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457077752426362180607425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98437748012940598296572933 18457077752426362180607425)
  ·
    refine ⟨13842808314319771635455569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18457077752426362180607425 13842808314319771635455569)
    ·
      refine ⟨10382106235739828726591677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13842808314319771635455569 10382106235739828726591677)
      ·
        refine ⟨3893289838402435772471879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10382106235739828726591677 3893289838402435772471879)
        ·
          refine ⟨5839934757603653658707819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893289838402435772471879 5839934757603653658707819)
          ·
            refine ⟨8759902136405480488061729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839934757603653658707819 8759902136405480488061729)
            ·
              refine ⟨6569926602304110366046297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8759902136405480488061729 6569926602304110366046297)
              ·
                refine ⟨4927444951728082774534723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6569926602304110366046297 4927444951728082774534723)
                ·
                  refine ⟨7391167427592124161802085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927444951728082774534723 7391167427592124161802085)
                  ·
                    refine ⟨1385843892673523280337891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391167427592124161802085 1385843892673523280337891)
                    ·
                      rfl

theorem cell22_4048382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4048382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048382 prefixEnd_4048382 := by exact prefixLift 4048382
  have htrace : WordTrace (prefixWord ++ tailWord_4048382) baseStart_4048382 baseEnd_4048382 := by
    simpa [prefixWord, tailWord_4048382, baseEnd_4048382] using wordTrace_append hprefix tailTrace_4048382
  have hstable : (prefixWord ++ tailWord_4048382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048382).length < 2 ^ (prefixWord ++ tailWord_4048382).sum := by decide
  have hdescent : baseEnd_4048382 < baseStart_4048382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048389 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_4048389 : Nat := 118140960795 + 4048389 * 2 ^ 59
def prefixEnd_4048389 : Nat := 4983230072969 + 3 ^ 40 * 4048389 * 2
def baseEnd_4048389 : Nat := 1385846288916577595412869

theorem tailTrace_4048389 : CollatzResearch.WordTrace tailWord_4048389 prefixEnd_4048389 1385846288916577595412869 := by
  unfold tailWord_4048389
  simp only [CollatzResearch.WordTrace]
  refine ⟨147656877330385537640364221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98437918220257025093576147 147656877330385537640364221)
  ·
    refine ⟨55371328998894576615136583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147656877330385537640364221 55371328998894576615136583)
    ·
      refine ⟨83056993498341864922704875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55371328998894576615136583 83056993498341864922704875)
      ·
        refine ⟨124585490247512797384057313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83056993498341864922704875 124585490247512797384057313)
        ·
          refine ⟨93439117685634598038042985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124585490247512797384057313 93439117685634598038042985)
          ·
            refine ⟨70079338264225948528532239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93439117685634598038042985 70079338264225948528532239)
            ·
              refine ⟨105119007396338922792798359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70079338264225948528532239 105119007396338922792798359)
              ·
                refine ⟨157678511094508384189197539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105119007396338922792798359 157678511094508384189197539)
                ·
                  refine ⟨236517766641762576283796309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157678511094508384189197539 236517766641762576283796309)
                  ·
                    refine ⟨1385846288916577595412869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236517766641762576283796309 1385846288916577595412869)
                    ·
                      rfl

theorem cell22_4048389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_4048389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048389 prefixEnd_4048389 := by exact prefixLift 4048389
  have htrace : WordTrace (prefixWord ++ tailWord_4048389) baseStart_4048389 baseEnd_4048389 := by
    simpa [prefixWord, tailWord_4048389, baseEnd_4048389] using wordTrace_append hprefix tailTrace_4048389
  have hstable : (prefixWord ++ tailWord_4048389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048389).length < 2 ^ (prefixWord ++ tailWord_4048389).sum := by decide
  have hdescent : baseEnd_4048389 < baseStart_4048389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048391 : List Nat := [1, 1, 4, 3, 2, 2, 1, 8]
def baseStart_4048391 : Nat := 118140960795 + 4048391 * 2 ^ 59
def prefixEnd_4048391 : Nat := 4983230072969 + 3 ^ 40 * 4048391 * 2
def baseEnd_4048391 : Nat := 153982997061938917429207

theorem tailTrace_4048391 : CollatzResearch.WordTrace tailWord_4048391 prefixEnd_4048391 153982997061938917429207 := by
  unfold tailWord_4048391
  simp only [CollatzResearch.WordTrace]
  refine ⟨147656950276378291981937027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98437966850918861321291351 147656950276378291981937027)
  ·
    refine ⟨221485425414567437972905541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147656950276378291981937027 221485425414567437972905541)
    ·
      refine ⟨41528517265231394619919789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221485425414567437972905541 41528517265231394619919789)
      ·
        refine ⟨15573193974461772982469921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41528517265231394619919789 15573193974461772982469921)
        ·
          refine ⟨11679895480846329736852441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15573193974461772982469921 11679895480846329736852441)
          ·
            refine ⟨8759921610634747302639331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679895480846329736852441 8759921610634747302639331)
            ·
              refine ⟨13139882415952120953958997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759921610634747302639331 13139882415952120953958997)
              ·
                refine ⟨153982997061938917429207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13139882415952120953958997 153982997061938917429207)
                ·
                  rfl

theorem cell22_4048391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 8].length) (baseStart_4048391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048391 prefixEnd_4048391 := by exact prefixLift 4048391
  have htrace : WordTrace (prefixWord ++ tailWord_4048391) baseStart_4048391 baseEnd_4048391 := by
    simpa [prefixWord, tailWord_4048391, baseEnd_4048391] using wordTrace_append hprefix tailTrace_4048391
  have hstable : (prefixWord ++ tailWord_4048391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048391).length < 2 ^ (prefixWord ++ tailWord_4048391).sum := by decide
  have hdescent : baseEnd_4048391 < baseStart_4048391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048408 : List Nat := [2, 1, 2, 3, 5, 1, 8]
def baseStart_4048408 : Nat := 118140960795 + 4048408 * 2 ^ 59
def prefixEnd_4048408 : Nat := 4983230072969 + 3 ^ 40 * 4048408 * 2
def baseEnd_4048408 : Nat := 51327881222402514043993

theorem tailTrace_4048408 : CollatzResearch.WordTrace tailWord_4048408 prefixEnd_4048408 51327881222402514043993 := by
  unfold tailWord_4048408
  simp only [CollatzResearch.WordTrace]
  refine ⟨73828785158658351942652939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98438380211544469256870585 73828785158658351942652939)
  ·
    refine ⟨110743177737987527913979409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73828785158658351942652939 110743177737987527913979409)
    ·
      refine ⟨83057383303490645935484557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110743177737987527913979409 83057383303490645935484557)
      ·
        refine ⟨31146518738808992225806709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83057383303490645935484557 31146518738808992225806709)
        ·
          refine ⟨2919986131763343021169379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31146518738808992225806709 2919986131763343021169379)
          ·
            refine ⟨4379979197645014531754069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919986131763343021169379 4379979197645014531754069)
            ·
              refine ⟨51327881222402514043993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4379979197645014531754069 51327881222402514043993)
              ·
                rfl

theorem cell22_4048408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 8].length) (baseStart_4048408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048408 prefixEnd_4048408 := by exact prefixLift 4048408
  have htrace : WordTrace (prefixWord ++ tailWord_4048408) baseStart_4048408 baseEnd_4048408 := by
    simpa [prefixWord, tailWord_4048408, baseEnd_4048408] using wordTrace_append hprefix tailTrace_4048408
  have hstable : (prefixWord ++ tailWord_4048408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048408).length < 2 ^ (prefixWord ++ tailWord_4048408).sum := by decide
  have hdescent : baseEnd_4048408 < baseStart_4048408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048414 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4048414 : Nat := 118140960795 + 4048414 * 2 ^ 59
def prefixEnd_4048414 : Nat := 4983230072969 + 3 ^ 40 * 4048414 * 2
def baseEnd_4048414 : Nat := 461951615642495287845931

theorem tailTrace_4048414 : CollatzResearch.WordTrace tailWord_4048414 prefixEnd_4048414 461951615642495287845931 := by
  unfold tailWord_4048414
  simp only [CollatzResearch.WordTrace]
  refine ⟨18457223644411870863753037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98438526103529977940016197 18457223644411870863753037)
  ·
    refine ⟨6921458866654451573907389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18457223644411870863753037 6921458866654451573907389)
    ·
      refine ⟨2595547074995419340215271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6921458866654451573907389 2595547074995419340215271)
      ·
        refine ⟨3893320612493129010322907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595547074995419340215271 3893320612493129010322907)
        ·
          refine ⟨5839980918739693515484361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893320612493129010322907 5839980918739693515484361)
          ·
            refine ⟨4379985689054770136613271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5839980918739693515484361 4379985689054770136613271)
            ·
              refine ⟨6569978533582155204919907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379985689054770136613271 6569978533582155204919907)
              ·
                refine ⟨9854967800373232807379861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569978533582155204919907 9854967800373232807379861)
                ·
                  refine ⟨461951615642495287845931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9854967800373232807379861 461951615642495287845931)
                  ·
                    rfl

theorem cell22_4048414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4048414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048414 prefixEnd_4048414 := by exact prefixLift 4048414
  have htrace : WordTrace (prefixWord ++ tailWord_4048414) baseStart_4048414 baseEnd_4048414 := by
    simpa [prefixWord, tailWord_4048414, baseEnd_4048414] using wordTrace_append hprefix tailTrace_4048414
  have hstable : (prefixWord ++ tailWord_4048414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048414).length < 2 ^ (prefixWord ++ tailWord_4048414).sum := by decide
  have hdescent : baseEnd_4048414 < baseStart_4048414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048481 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 6]
def baseStart_4048481 : Nat := 118140960795 + 4048481 * 2 ^ 59
def prefixEnd_4048481 : Nat := 4983230072969 + 3 ^ 40 * 4048481 * 2
def baseEnd_4048481 : Nat := 461959260798906674037529

theorem tailTrace_4048481 : CollatzResearch.WordTrace tailWord_4048481 prefixEnd_4048481 461959260798906674037529 := by
  unfold tailWord_4048481
  simp only [CollatzResearch.WordTrace]
  refine ⟨147660232846052237352713297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98440155230701491568475531 147660232846052237352713297)
  ·
    refine ⟨110745174634539178014534973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147660232846052237352713297 110745174634539178014534973)
    ·
      refine ⟨41529440487952191755450615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110745174634539178014534973 41529440487952191755450615)
      ·
        refine ⟨62294160731928287633175923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41529440487952191755450615 62294160731928287633175923)
        ·
          refine ⟨93441241097892431449763885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62294160731928287633175923 93441241097892431449763885)
          ·
            refine ⟨35040465411709661793661457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93441241097892431449763885 35040465411709661793661457)
            ·
              refine ⟨26280349058782246345246093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35040465411709661793661457 26280349058782246345246093)
              ·
                refine ⟨9855130897043342379467285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26280349058782246345246093 9855130897043342379467285)
                ·
                  refine ⟨461959260798906674037529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9855130897043342379467285 461959260798906674037529)
                  ·
                    rfl

theorem cell22_4048481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_4048481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048481 prefixEnd_4048481 := by exact prefixLift 4048481
  have htrace : WordTrace (prefixWord ++ tailWord_4048481) baseStart_4048481 baseEnd_4048481 := by
    simpa [prefixWord, tailWord_4048481, baseEnd_4048481] using wordTrace_append hprefix tailTrace_4048481
  have hstable : (prefixWord ++ tailWord_4048481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048481).length < 2 ^ (prefixWord ++ tailWord_4048481).sum := by decide
  have hdescent : baseEnd_4048481 < baseStart_4048481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048498 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_4048498 : Nat := 118140960795 + 4048498 * 2 ^ 59
def prefixEnd_4048498 : Nat := 4983230072969 + 3 ^ 40 * 4048498 * 2
def baseEnd_4048498 : Nat := 461961200614712548145845

theorem tailTrace_4048498 : CollatzResearch.WordTrace tailWord_4048498 prefixEnd_4048498 461961200614712548145845 := by
  unfold tailWord_4048498
  simp only [CollatzResearch.WordTrace]
  refine ⟨36915213221747662314020537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98440568591327099504054765 36915213221747662314020537)
  ·
    refine ⟨27686409916310746735515403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36915213221747662314020537 27686409916310746735515403)
    ·
      refine ⟨41529614874466120103273105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27686409916310746735515403 41529614874466120103273105)
      ·
        refine ⟨31147211155849590077454829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41529614874466120103273105 31147211155849590077454829)
        ·
          refine ⟨11680204183443596279045561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31147211155849590077454829 11680204183443596279045561)
          ·
            refine ⟨8760153137582697209284171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11680204183443596279045561 8760153137582697209284171)
            ·
              refine ⟨13140229706374045813926257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760153137582697209284171 13140229706374045813926257)
              ·
                refine ⟨9855172279780534360444693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13140229706374045813926257 9855172279780534360444693)
                ·
                  refine ⟨461961200614712548145845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9855172279780534360444693 461961200614712548145845)
                  ·
                    rfl

theorem cell22_4048498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_4048498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048498 prefixEnd_4048498 := by exact prefixLift 4048498
  have htrace : WordTrace (prefixWord ++ tailWord_4048498) baseStart_4048498 baseEnd_4048498 := by
    simpa [prefixWord, tailWord_4048498, baseEnd_4048498] using wordTrace_append hprefix tailTrace_4048498
  have hstable : (prefixWord ++ tailWord_4048498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048498).length < 2 ^ (prefixWord ++ tailWord_4048498).sum := by decide
  have hdescent : baseEnd_4048498 < baseStart_4048498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048513 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_4048513 : Nat := 118140960795 + 4048513 * 2 ^ 59
def prefixEnd_4048513 : Nat := 4983230072969 + 3 ^ 40 * 4048513 * 2
def baseEnd_4048513 : Nat := 1385888736650682605312489

theorem tailTrace_4048513 : CollatzResearch.WordTrace tailWord_4048513 prefixEnd_4048513 1385888736650682605312489 := by
  unfold tailWord_4048513
  simp only [CollatzResearch.WordTrace]
  refine ⟨147661399981936306817878193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98440933321290871211918795 147661399981936306817878193)
  ·
    refine ⟨110746049986452230113408645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147661399981936306817878193 110746049986452230113408645)
    ·
      refine ⟨20764884372459793146264121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110746049986452230113408645 20764884372459793146264121)
      ·
        refine ⟨15573663279344844859698091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20764884372459793146264121 15573663279344844859698091)
        ·
          refine ⟨23360494919017267289547137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15573663279344844859698091 23360494919017267289547137)
          ·
            refine ⟨17520371189262950467160353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23360494919017267289547137 17520371189262950467160353)
            ·
              refine ⟨13140278391947212850370265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17520371189262950467160353 13140278391947212850370265)
              ·
                refine ⟨9855208793960409637777699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13140278391947212850370265 9855208793960409637777699)
                ·
                  refine ⟨14782813190940614456666549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855208793960409637777699 14782813190940614456666549)
                  ·
                    refine ⟨1385888736650682605312489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14782813190940614456666549 1385888736650682605312489)
                    ·
                      rfl

theorem cell22_4048513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_4048513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048513 prefixEnd_4048513 := by exact prefixLift 4048513
  have htrace : WordTrace (prefixWord ++ tailWord_4048513) baseStart_4048513 baseEnd_4048513 := by
    simpa [prefixWord, tailWord_4048513, baseEnd_4048513] using wordTrace_append hprefix tailTrace_4048513
  have hstable : (prefixWord ++ tailWord_4048513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048513).length < 2 ^ (prefixWord ++ tailWord_4048513).sum := by decide
  have hdescent : baseEnd_4048513 < baseStart_4048513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048598 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4048598 : Nat := 118140960795 + 4048598 * 2 ^ 59
def prefixEnd_4048598 : Nat := 4983230072969 + 3 ^ 40 * 4048598 * 2
def baseEnd_4048598 : Nat := 1385917833887770716937229

theorem tailTrace_4048598 : CollatzResearch.WordTrace tailWord_4048598 prefixEnd_4048598 1385917833887770716937229 := by
  unfold tailWord_4048598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229031261664272895920153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98443000124418910889814965 9229031261664272895920153)
  ·
    refine ⟨6921773446248204671940115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9229031261664272895920153 6921773446248204671940115)
    ·
      refine ⟨10382660169372307007910173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6921773446248204671940115 10382660169372307007910173)
      ·
        refine ⟨3893497563514615127966315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10382660169372307007910173 3893497563514615127966315)
        ·
          refine ⟨5840246345271922691949473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893497563514615127966315 5840246345271922691949473)
          ·
            refine ⟨4380184758953942018962105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840246345271922691949473 4380184758953942018962105)
            ·
              refine ⟨3285138569215456514221579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380184758953942018962105 3285138569215456514221579)
              ·
                refine ⟨4927707853823184771332369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285138569215456514221579 4927707853823184771332369)
                ·
                  refine ⟨3695780890367388578499277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4927707853823184771332369 3695780890367388578499277)
                  ·
                    refine ⟨1385917833887770716937229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695780890367388578499277 1385917833887770716937229)
                    ·
                      rfl

theorem cell22_4048598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4048598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048598 prefixEnd_4048598 := by exact prefixLift 4048598
  have htrace : WordTrace (prefixWord ++ tailWord_4048598) baseStart_4048598 baseEnd_4048598 := by
    simpa [prefixWord, tailWord_4048598, baseEnd_4048598] using wordTrace_append hprefix tailTrace_4048598
  have hstable : (prefixWord ++ tailWord_4048598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048598).length < 2 ^ (prefixWord ++ tailWord_4048598).sum := by decide
  have hdescent : baseEnd_4048598 < baseStart_4048598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048648 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4048648 : Nat := 118140960795 + 4048648 * 2 ^ 59
def prefixEnd_4048648 : Nat := 4983230072969 + 3 ^ 40 * 4048648 * 2
def baseEnd_4048648 : Nat := 1385934949909587253187075

theorem tailTrace_4048648 : CollatzResearch.WordTrace tailWord_4048648 prefixEnd_4048648 1385934949909587253187075 := by
  unfold tailWord_4048648
  simp only [CollatzResearch.WordTrace]
  refine ⟨73833161918223612437021299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98444215890964816582695065 73833161918223612437021299)
  ·
    refine ⟨110749742877335418655531949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73833161918223612437021299 110749742877335418655531949)
    ·
      refine ⟨41531153579000781995824481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110749742877335418655531949 41531153579000781995824481)
      ·
        refine ⟨31148365184250586496868361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41531153579000781995824481 31148365184250586496868361)
        ·
          refine ⟨23361273888187939872651271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31148365184250586496868361 23361273888187939872651271)
          ·
            refine ⟨35041910832281909808976907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361273888187939872651271 35041910832281909808976907)
            ·
              refine ⟨52562866248422864713465361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35041910832281909808976907 52562866248422864713465361)
              ·
                refine ⟨39422149686317148535099021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52562866248422864713465361 39422149686317148535099021)
                ·
                  refine ⟨14783306132368930700662133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39422149686317148535099021 14783306132368930700662133)
                  ·
                    refine ⟨1385934949909587253187075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14783306132368930700662133 1385934949909587253187075)
                    ·
                      rfl

theorem cell22_4048648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4048648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048648 prefixEnd_4048648 := by exact prefixLift 4048648
  have htrace : WordTrace (prefixWord ++ tailWord_4048648) baseStart_4048648 baseEnd_4048648 := by
    simpa [prefixWord, tailWord_4048648, baseEnd_4048648] using wordTrace_append hprefix tailTrace_4048648
  have hstable : (prefixWord ++ tailWord_4048648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048648).length < 2 ^ (prefixWord ++ tailWord_4048648).sum := by decide
  have hdescent : baseEnd_4048648 < baseStart_4048648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048680 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4048680 : Nat := 118140960795 + 4048680 * 2 ^ 59
def prefixEnd_4048680 : Nat := 4983230072969 + 3 ^ 40 * 4048680 * 2
def baseEnd_4048680 : Nat := 1385945904163549836386977

theorem tailTrace_4048680 : CollatzResearch.WordTrace tailWord_4048680 prefixEnd_4048680 1385945904163549836386977 := by
  unfold tailWord_4048680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73833745486165647169603747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98444993981554196226138329 73833745486165647169603747)
  ·
    refine ⟨110750618229248470754405621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73833745486165647169603747 110750618229248470754405621)
    ·
      refine ⟨10382870458992044133225527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110750618229248470754405621 10382870458992044133225527)
      ·
        refine ⟨15574305688488066199838291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10382870458992044133225527 15574305688488066199838291)
        ·
          refine ⟨23361458532732099299757437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574305688488066199838291 23361458532732099299757437)
          ·
            refine ⟨8760546949774537237409039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23361458532732099299757437 8760546949774537237409039)
            ·
              refine ⟨13140820424661805856113559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760546949774537237409039 13140820424661805856113559)
              ·
                refine ⟨19711230636992708784170339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13140820424661805856113559 19711230636992708784170339)
                ·
                  refine ⟨29566845955489063176255509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19711230636992708784170339 29566845955489063176255509)
                  ·
                    refine ⟨1385945904163549836386977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29566845955489063176255509 1385945904163549836386977)
                    ·
                      rfl

theorem cell22_4048680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4048680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048680 prefixEnd_4048680 := by exact prefixLift 4048680
  have htrace : WordTrace (prefixWord ++ tailWord_4048680) baseStart_4048680 baseEnd_4048680 := by
    simpa [prefixWord, tailWord_4048680, baseEnd_4048680] using wordTrace_append hprefix tailTrace_4048680
  have hstable : (prefixWord ++ tailWord_4048680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048680).length < 2 ^ (prefixWord ++ tailWord_4048680).sum := by decide
  have hdescent : baseEnd_4048680 < baseStart_4048680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048686 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4048686 : Nat := 118140960795 + 4048686 * 2 ^ 59
def prefixEnd_4048686 : Nat := 4983230072969 + 3 ^ 40 * 4048686 * 2
def baseEnd_4048686 : Nat := 1385947958086167820736959

theorem tailTrace_4048686 : CollatzResearch.WordTrace tailWord_4048686 prefixEnd_4048686 1385947958086167820736959 := by
  unfold tailWord_4048686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458463726288694670490739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98445139873539704909283941 18458463726288694670490739)
  ·
    refine ⟨27687695589433042005736109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458463726288694670490739 27687695589433042005736109)
    ·
      refine ⟨10382885846037390752151041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27687695589433042005736109 10382885846037390752151041)
      ·
        refine ⟨7787164384528043064113281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10382885846037390752151041 7787164384528043064113281)
        ·
          refine ⟨5840373288396032298084961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7787164384528043064113281 5840373288396032298084961)
          ·
            refine ⟨4380279966297024223563721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5840373288396032298084961 4380279966297024223563721)
            ·
              refine ⟨3285209974722768167672791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380279966297024223563721 3285209974722768167672791)
              ·
                refine ⟨4927814962084152251509187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285209974722768167672791 4927814962084152251509187)
                ·
                  refine ⟨7391722443126228377263781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927814962084152251509187 7391722443126228377263781)
                  ·
                    refine ⟨1385947958086167820736959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391722443126228377263781 1385947958086167820736959)
                    ·
                      rfl

theorem cell22_4048686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4048686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048686 prefixEnd_4048686 := by exact prefixLift 4048686
  have htrace : WordTrace (prefixWord ++ tailWord_4048686) baseStart_4048686 baseEnd_4048686 := by
    simpa [prefixWord, tailWord_4048686, baseEnd_4048686] using wordTrace_append hprefix tailTrace_4048686
  have hstable : (prefixWord ++ tailWord_4048686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048686).length < 2 ^ (prefixWord ++ tailWord_4048686).sum := by decide
  have hdescent : baseEnd_4048686 < baseStart_4048686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048804 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_4048804 : Nat := 118140960795 + 4048804 * 2 ^ 59
def prefixEnd_4048804 : Nat := 4983230072969 + 3 ^ 40 * 4048804 * 2
def baseEnd_4048804 : Nat := 1385988351897654846286597

theorem tailTrace_4048804 : CollatzResearch.WordTrace tailWord_4048804 prefixEnd_4048804 1385988351897654846286597 := by
  unfold tailWord_4048804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73836006811941031758360733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98448009082588042344480977 73836006811941031758360733)
  ·
    refine ⟨27688502554477886909385275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73836006811941031758360733 27688502554477886909385275)
    ·
      refine ⟨41532753831716830364077913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27688502554477886909385275 41532753831716830364077913)
      ·
        refine ⟨31149565373787622773058435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41532753831716830364077913 31149565373787622773058435)
        ·
          refine ⟨46724348060681434159587653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31149565373787622773058435 46724348060681434159587653)
          ·
            refine ⟨8760815261377768904922685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46724348060681434159587653 8760815261377768904922685)
            ·
              refine ⟨3285305723016663339346007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8760815261377768904922685 3285305723016663339346007)
              ·
                refine ⟨4927958584524995009019011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3285305723016663339346007 4927958584524995009019011)
                ·
                  refine ⟨7391937876787492513528517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927958584524995009019011 7391937876787492513528517)
                  ·
                    refine ⟨1385988351897654846286597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391937876787492513528517 1385988351897654846286597)
                    ·
                      rfl

theorem cell22_4048804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_4048804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048804 prefixEnd_4048804 := by exact prefixLift 4048804
  have htrace : WordTrace (prefixWord ++ tailWord_4048804) baseStart_4048804 baseEnd_4048804 := by
    simpa [prefixWord, tailWord_4048804, baseEnd_4048804] using wordTrace_append hprefix tailTrace_4048804
  have hstable : (prefixWord ++ tailWord_4048804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048804).length < 2 ^ (prefixWord ++ tailWord_4048804).sum := by decide
  have hdescent : baseEnd_4048804 < baseStart_4048804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048815 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_4048815 : Nat := 118140960795 + 4048815 * 2 ^ 59
def prefixEnd_4048815 : Nat := 4983230072969 + 3 ^ 40 * 4048815 * 2
def baseEnd_4048815 : Nat := 1385992117422454484261563

theorem tailTrace_4048815 : CollatzResearch.WordTrace tailWord_4048815 prefixEnd_4048815 1385992117422454484261563 := by
  unfold tailWord_4048815
  simp only [CollatzResearch.WordTrace]
  refine ⟨147672414826842212395371899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98448276551228141596914599 147672414826842212395371899)
  ·
    refine ⟨221508622240263318593057849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147672414826842212395371899 221508622240263318593057849)
    ·
      refine ⟨166131466680197488944793387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221508622240263318593057849 166131466680197488944793387)
      ·
        refine ⟨249197200020296233417190081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166131466680197488944793387 249197200020296233417190081)
        ·
          refine ⟨186897900015222175062892561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249197200020296233417190081 186897900015222175062892561)
          ·
            refine ⟨140173425011416631297169421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186897900015222175062892561 140173425011416631297169421)
            ·
              refine ⟨52565034379281236736438533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140173425011416631297169421 52565034379281236736438533)
              ·
                refine ⟨9855943946115231888082225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52565034379281236736438533 9855943946115231888082225)
                ·
                  refine ⟨7391957959586423916061669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855943946115231888082225 7391957959586423916061669)
                  ·
                    refine ⟨1385992117422454484261563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7391957959586423916061669 1385992117422454484261563)
                    ·
                      rfl

theorem cell22_4048815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_4048815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048815 prefixEnd_4048815 := by exact prefixLift 4048815
  have htrace : WordTrace (prefixWord ++ tailWord_4048815) baseStart_4048815 baseEnd_4048815 := by
    simpa [prefixWord, tailWord_4048815, baseEnd_4048815] using wordTrace_append hprefix tailTrace_4048815
  have hstable : (prefixWord ++ tailWord_4048815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048815).length < 2 ^ (prefixWord ++ tailWord_4048815).sum := by decide
  have hdescent : baseEnd_4048815 < baseStart_4048815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048879 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 1, 3]
def baseStart_4048879 : Nat := 118140960795 + 4048879 * 2 ^ 59
def prefixEnd_4048879 : Nat := 4983230072969 + 3 ^ 40 * 4048879 * 2
def baseEnd_4048879 : Nat := 1386014025930379650661367

theorem tailTrace_4048879 : CollatzResearch.WordTrace tailWord_4048879 prefixEnd_4048879 1386014025930379650661367 := by
  unfold tailWord_4048879
  simp only [CollatzResearch.WordTrace]
  refine ⟨147674749098610351325701691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98449832732406900883801127 147674749098610351325701691)
  ·
    refine ⟨221512123647915526988552537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147674749098610351325701691 221512123647915526988552537)
    ·
      refine ⟨166134092735936645241414403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221512123647915526988552537 166134092735936645241414403)
      ·
        refine ⟨249201139103904967862121605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166134092735936645241414403 249201139103904967862121605)
        ·
          refine ⟨46725213581982181474147801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249201139103904967862121605 46725213581982181474147801)
          ·
            refine ⟨35043910186486636105610851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46725213581982181474147801 35043910186486636105610851)
            ·
              refine ⟨52565865279729954158416277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35043910186486636105610851 52565865279729954158416277)
              ·
                refine ⟨2464024934987341601175763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52565865279729954158416277 2464024934987341601175763)
                ·
                  refine ⟨3696037402481012401763645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464024934987341601175763 3696037402481012401763645)
                  ·
                    refine ⟨1386014025930379650661367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696037402481012401763645 1386014025930379650661367)
                    ·
                      rfl

theorem cell22_4048879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 3].length) (baseStart_4048879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048879 prefixEnd_4048879 := by exact prefixLift 4048879
  have htrace : WordTrace (prefixWord ++ tailWord_4048879) baseStart_4048879 baseEnd_4048879 := by
    simpa [prefixWord, tailWord_4048879, baseEnd_4048879] using wordTrace_append hprefix tailTrace_4048879
  have hstable : (prefixWord ++ tailWord_4048879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048879).length < 2 ^ (prefixWord ++ tailWord_4048879).sum := by decide
  have hdescent : baseEnd_4048879 < baseStart_4048879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4048988 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_4048988 : Nat := 118140960795 + 4048988 * 2 ^ 59
def prefixEnd_4048988 : Nat := 4983230072969 + 3 ^ 40 * 4048988 * 2
def baseEnd_4048988 : Nat := 462017112952646566562011

theorem tailTrace_4048988 : CollatzResearch.WordTrace tailWord_4048988 prefixEnd_4048988 462017112952646566562011 := by
  unfold tailWord_4048988
  simp only [CollatzResearch.WordTrace]
  refine ⟨73839362327607731470709809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98452483103476975294279745 73839362327607731470709809)
  ·
    refine ⟨55379521745705798603032357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73839362327607731470709809 55379521745705798603032357)
    ·
      refine ⟨10383660327319837238068567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55379521745705798603032357 10383660327319837238068567)
      ·
        refine ⟨15575490490979755857102851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383660327319837238068567 15575490490979755857102851)
        ·
          refine ⟨23363235736469633785654277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575490490979755857102851 23363235736469633785654277)
          ·
            refine ⟨4380606700588056334810177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23363235736469633785654277 4380606700588056334810177)
            ·
              refine ⟨3285455025441042251107633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4380606700588056334810177 3285455025441042251107633)
              ·
                refine ⟨2464091269080781688330725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285455025441042251107633 2464091269080781688330725)
                ·
                  refine ⟨462017112952646566562011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464091269080781688330725 462017112952646566562011)
                  ·
                    rfl

theorem cell22_4048988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_4048988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4048988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4048988 prefixEnd_4048988 := by exact prefixLift 4048988
  have htrace : WordTrace (prefixWord ++ tailWord_4048988) baseStart_4048988 baseEnd_4048988 := by
    simpa [prefixWord, tailWord_4048988, baseEnd_4048988] using wordTrace_append hprefix tailTrace_4048988
  have hstable : (prefixWord ++ tailWord_4048988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4048988).length < 2 ^ (prefixWord ++ tailWord_4048988).sum := by decide
  have hdescent : baseEnd_4048988 < baseStart_4048988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4048988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049031 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 1, 3]
def baseStart_4049031 : Nat := 118140960795 + 4049031 * 2 ^ 59
def prefixEnd_4049031 : Nat := 4983230072969 + 3 ^ 40 * 4049031 * 2
def baseEnd_4049031 : Nat := 1386066058636701920860901

theorem tailTrace_4049031 : CollatzResearch.WordTrace tailWord_4049031 prefixEnd_4049031 1386066058636701920860901 := by
  unfold tailWord_4049031
  simp only [CollatzResearch.WordTrace]
  refine ⟨147680292994059681285234947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98453528662706454190156631 147680292994059681285234947)
  ·
    refine ⟨221520439491089521927852421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147680292994059681285234947 221520439491089521927852421)
    ·
      refine ⟨41535082404579285361472329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221520439491089521927852421 41535082404579285361472329)
      ·
        refine ⟨31151311803434464021104247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41535082404579285361472329 31151311803434464021104247)
        ·
          refine ⟨46726967705151696031656371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31151311803434464021104247 46726967705151696031656371)
          ·
            refine ⟨70090451557727544047484557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46726967705151696031656371 70090451557727544047484557)
            ·
              refine ⟨26283919334147829017806709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70090451557727544047484557 26283919334147829017806709)
              ·
                refine ⟨2464117437576358970419379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26283919334147829017806709 2464117437576358970419379)
                ·
                  refine ⟨3696176156364538455629069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464117437576358970419379 3696176156364538455629069)
                  ·
                    refine ⟨1386066058636701920860901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696176156364538455629069 1386066058636701920860901)
                    ·
                      rfl

theorem cell22_4049031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_4049031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049031 prefixEnd_4049031 := by exact prefixLift 4049031
  have htrace : WordTrace (prefixWord ++ tailWord_4049031) baseStart_4049031 baseEnd_4049031 := by
    simpa [prefixWord, tailWord_4049031, baseEnd_4049031] using wordTrace_append hprefix tailTrace_4049031
  have hstable : (prefixWord ++ tailWord_4049031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049031).length < 2 ^ (prefixWord ++ tailWord_4049031).sum := by decide
  have hdescent : baseEnd_4049031 < baseStart_4049031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049087 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_4049087 : Nat := 118140960795 + 4049087 * 2 ^ 59
def prefixEnd_4049087 : Nat := 4983230072969 + 3 ^ 40 * 4049087 * 2
def baseEnd_4049087 : Nat := 1386085228581136441460729

theorem tailTrace_4049087 : CollatzResearch.WordTrace tailWord_4049087 prefixEnd_4049087 1386085228581136441460729 := by
  unfold tailWord_4049087
  simp only [CollatzResearch.WordTrace]
  refine ⟨147682335481856802849273515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98454890321237868566182343 147682335481856802849273515)
  ·
    refine ⟨221523503222785204273910273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147682335481856802849273515 221523503222785204273910273)
    ·
      refine ⟨166142627417088903205432705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221523503222785204273910273 166142627417088903205432705)
      ·
        refine ⟨124606970562816677404074529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166142627417088903205432705 124606970562816677404074529)
        ·
          refine ⟨93455227922112508053055897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124606970562816677404074529 93455227922112508053055897)
          ·
            refine ⟨70091420941584381039791923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93455227922112508053055897 70091420941584381039791923)
            ·
              refine ⟨105137131412376571559687885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70091420941584381039791923 105137131412376571559687885)
              ·
                refine ⟨39426424279641214334882957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105137131412376571559687885 39426424279641214334882957)
                ·
                  refine ⟨14784909104865455375581109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39426424279641214334882957 14784909104865455375581109)
                  ·
                    refine ⟨1386085228581136441460729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14784909104865455375581109 1386085228581136441460729)
                    ·
                      rfl

theorem cell22_4049087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_4049087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049087 prefixEnd_4049087 := by exact prefixLift 4049087
  have htrace : WordTrace (prefixWord ++ tailWord_4049087) baseStart_4049087 baseEnd_4049087 := by
    simpa [prefixWord, tailWord_4049087, baseEnd_4049087] using wordTrace_append hprefix tailTrace_4049087
  have hstable : (prefixWord ++ tailWord_4049087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049087).length < 2 ^ (prefixWord ++ tailWord_4049087).sum := by decide
  have hdescent : baseEnd_4049087 < baseStart_4049087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049106 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_4049106 : Nat := 118140960795 + 4049106 * 2 ^ 59
def prefixEnd_4049106 : Nat := 4983230072969 + 3 ^ 40 * 4049106 * 2
def baseEnd_4049106 : Nat := 462030577556475575078557

theorem tailTrace_4049106 : CollatzResearch.WordTrace tailWord_4049106 prefixEnd_4049106 462030577556475575078557 := by
  unfold tailWord_4049106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920757117196992273553793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98455352312525312729476781 36920757117196992273553793)
  ·
    refine ⟨27690567837897744205165345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36920757117196992273553793 27690567837897744205165345)
    ·
      refine ⟨20767925878423308153874009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27690567837897744205165345 20767925878423308153874009)
      ·
        refine ⟨15575944408817481115405507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20767925878423308153874009 15575944408817481115405507)
        ·
          refine ⟨23363916613226221673108261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575944408817481115405507 23363916613226221673108261)
          ·
            refine ⟨4380734364979916563707799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23363916613226221673108261 4380734364979916563707799)
            ·
              refine ⟨6571101547469874845561699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380734364979916563707799 6571101547469874845561699)
              ·
                refine ⟨9856652321204812268342549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571101547469874845561699 9856652321204812268342549)
                ·
                  refine ⟨462030577556475575078557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9856652321204812268342549 462030577556475575078557)
                  ·
                    rfl

theorem cell22_4049106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_4049106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049106 prefixEnd_4049106 := by exact prefixLift 4049106
  have htrace : WordTrace (prefixWord ++ tailWord_4049106) baseStart_4049106 baseEnd_4049106 := by
    simpa [prefixWord, tailWord_4049106, baseEnd_4049106] using wordTrace_append hprefix tailTrace_4049106
  have hstable : (prefixWord ++ tailWord_4049106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049106).length < 2 ^ (prefixWord ++ tailWord_4049106).sum := by decide
  have hdescent : baseEnd_4049106 < baseStart_4049106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049121 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_4049121 : Nat := 118140960795 + 4049121 * 2 ^ 59
def prefixEnd_4049121 : Nat := 4983230072969 + 3 ^ 40 * 4049121 * 2
def baseEnd_4049121 : Nat := 1386096867475971686110625

theorem tailTrace_4049121 : CollatzResearch.WordTrace tailWord_4049121 prefixEnd_4049121 1386096867475971686110625 := by
  unfold tailWord_4049121
  simp only [CollatzResearch.WordTrace]
  refine ⟨147683575563733626656011217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98455717042489084437340811 147683575563733626656011217)
  ·
    refine ⟨110762681672800219992008413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147683575563733626656011217 110762681672800219992008413)
    ·
      refine ⟨41536005627300082497003155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110762681672800219992008413 41536005627300082497003155)
      ·
        refine ⟨62304008440950123745504733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41536005627300082497003155 62304008440950123745504733)
        ·
          refine ⟨23364003165356296404564275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62304008440950123745504733 23364003165356296404564275)
          ·
            refine ⟨35046004748034444606846413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23364003165356296404564275 35046004748034444606846413)
            ·
              refine ⟨13142251780512916727567405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35046004748034444606846413 13142251780512916727567405)
              ·
                refine ⟨4928344417692343772837777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142251780512916727567405 4928344417692343772837777)
                ·
                  refine ⟨3696258313269257829628333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4928344417692343772837777 3696258313269257829628333)
                  ·
                    refine ⟨1386096867475971686110625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696258313269257829628333 1386096867475971686110625)
                    ·
                      rfl

theorem cell22_4049121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_4049121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049121 prefixEnd_4049121 := by exact prefixLift 4049121
  have htrace : WordTrace (prefixWord ++ tailWord_4049121) baseStart_4049121 baseEnd_4049121 := by
    simpa [prefixWord, tailWord_4049121, baseEnd_4049121] using wordTrace_append hprefix tailTrace_4049121
  have hstable : (prefixWord ++ tailWord_4049121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049121).length < 2 ^ (prefixWord ++ tailWord_4049121).sum := by decide
  have hdescent : baseEnd_4049121 < baseStart_4049121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049147 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_4049147 : Nat := 118140960795 + 4049147 * 2 ^ 59
def prefixEnd_4049147 : Nat := 4983230072969 + 3 ^ 40 * 4049147 * 2
def baseEnd_4049147 : Nat := 1386105767807316284960545

theorem tailTrace_4049147 : CollatzResearch.WordTrace tailWord_4049147 prefixEnd_4049147 1386105767807316284960545 := by
  unfold tailWord_4049147
  simp only [CollatzResearch.WordTrace]
  refine ⟨147684523861639433096457695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98456349241092955397638463 147684523861639433096457695)
  ·
    refine ⟨221526785792459149644686543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147684523861639433096457695 221526785792459149644686543)
    ·
      refine ⟨332290178688688724467029815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221526785792459149644686543 332290178688688724467029815)
      ·
        refine ⟨498435268033033086700544723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332290178688688724467029815 498435268033033086700544723)
        ·
          refine ⟨747652902049549630050817085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498435268033033086700544723 747652902049549630050817085)
          ·
            refine ⟨280369838268581111269056407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747652902049549630050817085 280369838268581111269056407)
            ·
              refine ⟨420554757402871666903584611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280369838268581111269056407 420554757402871666903584611)
              ·
                refine ⟨630832136104307500355376917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420554757402871666903584611 630832136104307500355376917)
                ·
                  refine ⟨29570256379889414079158293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 630832136104307500355376917 29570256379889414079158293)
                  ·
                    refine ⟨1386105767807316284960545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29570256379889414079158293 1386105767807316284960545)
                    ·
                      rfl

theorem cell22_4049147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_4049147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049147 prefixEnd_4049147 := by exact prefixLift 4049147
  have htrace : WordTrace (prefixWord ++ tailWord_4049147) baseStart_4049147 baseEnd_4049147 := by
    simpa [prefixWord, tailWord_4049147, baseEnd_4049147] using wordTrace_append hprefix tailTrace_4049147
  have hstable : (prefixWord ++ tailWord_4049147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049147).length < 2 ^ (prefixWord ++ tailWord_4049147).sum := by decide
  have hdescent : baseEnd_4049147 < baseStart_4049147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049166 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_4049166 : Nat := 118140960795 + 4049166 * 2 ^ 59
def prefixEnd_4049166 : Nat := 4983230072969 + 3 ^ 40 * 4049166 * 2
def baseEnd_4049166 : Nat := 1386112271895606568735487

theorem tailTrace_4049166 : CollatzResearch.WordTrace tailWord_4049166 prefixEnd_4049166 1386112271895606568735487 := by
  unfold tailWord_4049166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460652106071324917674919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98456811232380399560932901 18460652106071324917674919)
  ·
    refine ⟨27690978159106987376512379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18460652106071324917674919 27690978159106987376512379)
    ·
      refine ⟨41536467238660481064768569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27690978159106987376512379 41536467238660481064768569)
      ·
        refine ⟨31152350428995360798576427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41536467238660481064768569 31152350428995360798576427)
        ·
          refine ⟨46728525643493041197864641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31152350428995360798576427 46728525643493041197864641)
          ·
            refine ⟨35046394232619780898398481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46728525643493041197864641 35046394232619780898398481)
            ·
              refine ⟨26284795674464835673798861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35046394232619780898398481 26284795674464835673798861)
              ·
                refine ⟨9856798377924313377674573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26284795674464835673798861 9856798377924313377674573)
                ·
                  refine ⟨3696299391721617516627965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9856798377924313377674573 3696299391721617516627965)
                  ·
                    refine ⟨1386112271895606568735487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696299391721617516627965 1386112271895606568735487)
                    ·
                      rfl

theorem cell22_4049166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_4049166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049166 prefixEnd_4049166 := by exact prefixLift 4049166
  have htrace : WordTrace (prefixWord ++ tailWord_4049166) baseStart_4049166 baseEnd_4049166 := by
    simpa [prefixWord, tailWord_4049166, baseEnd_4049166] using wordTrace_append hprefix tailTrace_4049166
  have hstable : (prefixWord ++ tailWord_4049166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049166).length < 2 ^ (prefixWord ++ tailWord_4049166).sum := by decide
  have hdescent : baseEnd_4049166 < baseStart_4049166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049179 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 5]
def baseStart_4049179 : Nat := 118140960795 + 4049179 * 2 ^ 59
def prefixEnd_4049179 : Nat := 4983230072969 + 3 ^ 40 * 4049179 * 2
def baseEnd_4049179 : Nat := 462038907353759622720149

theorem tailTrace_4049179 : CollatzResearch.WordTrace tailWord_4049179 prefixEnd_4049179 462038907353759622720149 := by
  unfold tailWord_4049179
  simp only [CollatzResearch.WordTrace]
  refine ⟨147685690997523502561622591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98457127331682335041081727 147685690997523502561622591)
  ·
    refine ⟨221528536496285253842433887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147685690997523502561622591 221528536496285253842433887)
    ·
      refine ⟨332292804744427880763650831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221528536496285253842433887 332292804744427880763650831)
      ·
        refine ⟨498439207116641821145476247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332292804744427880763650831 498439207116641821145476247)
        ·
          refine ⟨747658810674962731718214371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498439207116641821145476247 747658810674962731718214371)
          ·
            refine ⟨1121488216012444097577321557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747658810674962731718214371 1121488216012444097577321557)
            ·
              refine ⟨13142440031395829268484237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1121488216012444097577321557 13142440031395829268484237)
              ·
                refine ⟨4928415011773435975681589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13142440031395829268484237 4928415011773435975681589)
                ·
                  refine ⟨462038907353759622720149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4928415011773435975681589 462038907353759622720149)
                  ·
                    rfl

theorem cell22_4049179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 5].length) (baseStart_4049179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049179 prefixEnd_4049179 := by exact prefixLift 4049179
  have htrace : WordTrace (prefixWord ++ tailWord_4049179) baseStart_4049179 baseEnd_4049179 := by
    simpa [prefixWord, tailWord_4049179, baseEnd_4049179] using wordTrace_append hprefix tailTrace_4049179
  have hstable : (prefixWord ++ tailWord_4049179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049179).length < 2 ^ (prefixWord ++ tailWord_4049179).sum := by decide
  have hdescent : baseEnd_4049179 < baseStart_4049179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049224 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_4049224 : Nat := 118140960795 + 4049224 * 2 ^ 59
def prefixEnd_4049224 : Nat := 4983230072969 + 3 ^ 40 * 4049224 * 2
def baseEnd_4049224 : Nat := 462044042160304583595103

theorem tailTrace_4049224 : CollatzResearch.WordTrace tailWord_4049224 prefixEnd_4049224 462044042160304583595103 := by
  unfold tailWord_4049224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73843666141180237623505363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98458221521573650164673817 73843666141180237623505363)
  ·
    refine ⟨110765499211770356435258045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73843666141180237623505363 110765499211770356435258045)
    ·
      refine ⟨41537062204413883663221767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110765499211770356435258045 41537062204413883663221767)
      ·
        refine ⟨62305593306620825494832651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41537062204413883663221767 62305593306620825494832651)
        ·
          refine ⟨93458389959931238242248977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62305593306620825494832651 93458389959931238242248977)
          ·
            refine ⟨70093792469948428681686733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93458389959931238242248977 70093792469948428681686733)
            ·
              refine ⟨26285172176230660755632525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70093792469948428681686733 26285172176230660755632525)
              ·
                refine ⟨9856939566086497783362197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26285172176230660755632525 9856939566086497783362197)
                ·
                  refine ⟨462044042160304583595103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9856939566086497783362197 462044042160304583595103)
                  ·
                    rfl

theorem cell22_4049224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_4049224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049224 prefixEnd_4049224 := by exact prefixLift 4049224
  have htrace : WordTrace (prefixWord ++ tailWord_4049224) baseStart_4049224 baseEnd_4049224 := by
    simpa [prefixWord, tailWord_4049224, baseEnd_4049224] using wordTrace_append hprefix tailTrace_4049224
  have hstable : (prefixWord ++ tailWord_4049224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049224).length < 2 ^ (prefixWord ++ tailWord_4049224).sum := by decide
  have hdescent : baseEnd_4049224 < baseStart_4049224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049301 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_4049301 : Nat := 118140960795 + 4049301 * 2 ^ 59
def prefixEnd_4049301 : Nat := 4983230072969 + 3 ^ 40 * 4049301 * 2
def baseEnd_4049301 : Nat := 1386158485154511216610073

theorem tailTrace_4049301 : CollatzResearch.WordTrace tailWord_4049301 prefixEnd_4049301 1386158485154511216610073 := by
  unfold tailWord_4049301
  simp only [CollatzResearch.WordTrace]
  refine ⟨147690140703081517397563757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98460093802054344931709171 147690140703081517397563757)
  ·
    refine ⟨55383802763655569024086409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147690140703081517397563757 55383802763655569024086409)
    ·
      refine ⟨41537852072741676768064807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55383802763655569024086409 41537852072741676768064807)
      ·
        refine ⟨62306778109112515152097211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41537852072741676768064807 62306778109112515152097211)
        ·
          refine ⟨93460167163668772728145817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62306778109112515152097211 93460167163668772728145817)
          ·
            refine ⟨70095125372751579546109363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93460167163668772728145817 70095125372751579546109363)
            ·
              refine ⟨105142688059127369319164045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70095125372751579546109363 105142688059127369319164045)
              ·
                refine ⟨39428508022172763494686517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105142688059127369319164045 39428508022172763494686517)
                ·
                  refine ⟨3696422627078696577626861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39428508022172763494686517 3696422627078696577626861)
                  ·
                    refine ⟨1386158485154511216610073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696422627078696577626861 1386158485154511216610073)
                    ·
                      rfl

theorem cell22_4049301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_4049301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049301 prefixEnd_4049301 := by exact prefixLift 4049301
  have htrace : WordTrace (prefixWord ++ tailWord_4049301) baseStart_4049301 baseEnd_4049301 := by
    simpa [prefixWord, tailWord_4049301, baseEnd_4049301] using wordTrace_append hprefix tailTrace_4049301
  have hstable : (prefixWord ++ tailWord_4049301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049301).length < 2 ^ (prefixWord ++ tailWord_4049301).sum := by decide
  have hdescent : baseEnd_4049301 < baseStart_4049301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049335 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 1, 3]
def baseStart_4049335 : Nat := 118140960795 + 4049335 * 2 ^ 59
def prefixEnd_4049335 : Nat := 4983230072969 + 3 ^ 40 * 4049335 * 2
def baseEnd_4049335 : Nat := 1386170124049346461259969

theorem tailTrace_4049335 : CollatzResearch.WordTrace tailWord_4049335 prefixEnd_4049335 1386170124049346461259969 := by
  unfold tailWord_4049335
  simp only [CollatzResearch.WordTrace]
  refine ⟨147691380784958341204301459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98460920523305560802867639 147691380784958341204301459)
  ·
    refine ⟨221537071177437511806452189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147691380784958341204301459 221537071177437511806452189)
    ·
      refine ⟨83076401691539066927419571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221537071177437511806452189 83076401691539066927419571)
      ·
        refine ⟨124614602537308600391129357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83076401691539066927419571 124614602537308600391129357)
        ·
          refine ⟨46730475951490725146673509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124614602537308600391129357 46730475951490725146673509)
          ·
            refine ⟨8761964240904510965001283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46730475951490725146673509 8761964240904510965001283)
            ·
              refine ⟨13142946361356766447501925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8761964240904510965001283 13142946361356766447501925)
              ·
                refine ⟨2464302442754393708906611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13142946361356766447501925 2464302442754393708906611)
                ·
                  refine ⟨3696453664131590563359917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464302442754393708906611 3696453664131590563359917)
                  ·
                    refine ⟨1386170124049346461259969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696453664131590563359917 1386170124049346461259969)
                    ·
                      rfl

theorem cell22_4049335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_4049335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049335 prefixEnd_4049335 := by exact prefixLift 4049335
  have htrace : WordTrace (prefixWord ++ tailWord_4049335) baseStart_4049335 baseEnd_4049335 := by
    simpa [prefixWord, tailWord_4049335, baseEnd_4049335] using wordTrace_append hprefix tailTrace_4049335
  have hstable : (prefixWord ++ tailWord_4049335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049335).length < 2 ^ (prefixWord ++ tailWord_4049335).sum := by decide
  have hdescent : baseEnd_4049335 < baseStart_4049335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049393 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 4]
def baseStart_4049393 : Nat := 118140960795 + 4049393 * 2 ^ 59
def prefixEnd_4049393 : Nat := 4983230072969 + 3 ^ 40 * 4049393 * 2
def baseEnd_4049393 : Nat := 462063326211551214436597

theorem tailTrace_4049393 : CollatzResearch.WordTrace tailWord_4049393 prefixEnd_4049393 462063326211551214436597 := by
  unfold tailWord_4049393
  simp only [CollatzResearch.WordTrace]
  refine ⟨147693496218748217109912833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98462330812498811406608555 147693496218748217109912833)
  ·
    refine ⟨110770122164061162832434625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147693496218748217109912833 110770122164061162832434625)
    ·
      refine ⟨83077591623045872124325969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110770122164061162832434625 83077591623045872124325969)
      ·
        refine ⟨62308193717284404093244477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83077591623045872124325969 62308193717284404093244477)
        ·
          refine ⟨23365572643981651534966679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62308193717284404093244477 23365572643981651534966679)
          ·
            refine ⟨35048358965972477302450019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23365572643981651534966679 35048358965972477302450019)
            ·
              refine ⟨52572538448958715953675029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35048358965972477302450019 52572538448958715953675029)
              ·
                refine ⟨2464337739794939810328517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52572538448958715953675029 2464337739794939810328517)
                ·
                  refine ⟨462063326211551214436597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464337739794939810328517 462063326211551214436597)
                  ·
                    rfl

theorem cell22_4049393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_4049393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049393 prefixEnd_4049393 := by exact prefixLift 4049393
  have htrace : WordTrace (prefixWord ++ tailWord_4049393) baseStart_4049393 baseEnd_4049393 := by
    simpa [prefixWord, tailWord_4049393, baseEnd_4049393] using wordTrace_append hprefix tailTrace_4049393
  have hstable : (prefixWord ++ tailWord_4049393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049393).length < 2 ^ (prefixWord ++ tailWord_4049393).sum := by decide
  have hdescent : baseEnd_4049393 < baseStart_4049393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049440 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_4049440 : Nat := 118140960795 + 4049440 * 2 ^ 59
def prefixEnd_4049440 : Nat := 4983230072969 + 3 ^ 40 * 4049440 * 2
def baseEnd_4049440 : Nat := 1386206067695161187384647

theorem tailTrace_4049440 : CollatzResearch.WordTrace tailWord_4049440 prefixEnd_4049440 1386206067695161187384647 := by
  unfold tailWord_4049440
  simp only [CollatzResearch.WordTrace]
  refine ⟨73847605224788972068436887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98463473633051962757915849 73847605224788972068436887)
  ·
    refine ⟨110771407837183458102655331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73847605224788972068436887 110771407837183458102655331)
    ·
      refine ⟨166157111755775187153982997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110771407837183458102655331 166157111755775187153982997)
      ·
        refine ⟨7788614613551961897842953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166157111755775187153982997 7788614613551961897842953)
        ·
          refine ⟨5841460960163971423382215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7788614613551961897842953 5841460960163971423382215)
          ·
            refine ⟨8762191440245957135073323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841460960163971423382215 8762191440245957135073323)
            ·
              refine ⟨13143287160368935702609985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762191440245957135073323 13143287160368935702609985)
              ·
                refine ⟨9857465370276701776957489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13143287160368935702609985 9857465370276701776957489)
                ·
                  refine ⟨7393099027707526332718117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857465370276701776957489 7393099027707526332718117)
                  ·
                    refine ⟨1386206067695161187384647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7393099027707526332718117 1386206067695161187384647)
                    ·
                      rfl

theorem cell22_4049440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_4049440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049440 prefixEnd_4049440 := by exact prefixLift 4049440
  have htrace : WordTrace (prefixWord ++ tailWord_4049440) baseStart_4049440 baseEnd_4049440 := by
    simpa [prefixWord, tailWord_4049440, baseEnd_4049440] using wordTrace_append hprefix tailTrace_4049440
  have hstable : (prefixWord ++ tailWord_4049440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049440).length < 2 ^ (prefixWord ++ tailWord_4049440).sum := by decide
  have hdescent : baseEnd_4049440 < baseStart_4049440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049444 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_4049444 : Nat := 118140960795 + 4049444 * 2 ^ 59
def prefixEnd_4049444 : Nat := 4983230072969 + 3 ^ 40 * 4049444 * 2
def baseEnd_4049444 : Nat := 462069145658968836761545

theorem tailTrace_4049444 : CollatzResearch.WordTrace tailWord_4049444 prefixEnd_4049444 462069145658968836761545 := by
  unfold tailWord_4049444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73847678170781726410009693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98463570894375635213346257 73847678170781726410009693)
  ·
    refine ⟨27692879314043147403753635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73847678170781726410009693 27692879314043147403753635)
    ·
      refine ⟨41539318971064721105630453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27692879314043147403753635 41539318971064721105630453)
      ·
        refine ⟨3894311153537317603652855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41539318971064721105630453 3894311153537317603652855)
        ·
          refine ⟨5841466730305976405479283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894311153537317603652855 5841466730305976405479283)
          ·
            refine ⟨8762200095458964608218925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841466730305976405479283 8762200095458964608218925)
            ·
              refine ⟨3285825035797111728082097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8762200095458964608218925 3285825035797111728082097)
              ·
                refine ⟨2464368776847833796061573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285825035797111728082097 2464368776847833796061573)
                ·
                  refine ⟨462069145658968836761545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464368776847833796061573 462069145658968836761545)
                  ·
                    rfl

theorem cell22_4049444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_4049444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049444 prefixEnd_4049444 := by exact prefixLift 4049444
  have htrace : WordTrace (prefixWord ++ tailWord_4049444) baseStart_4049444 baseEnd_4049444 := by
    simpa [prefixWord, tailWord_4049444, baseEnd_4049444] using wordTrace_append hprefix tailTrace_4049444
  have hstable : (prefixWord ++ tailWord_4049444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049444).length < 2 ^ (prefixWord ++ tailWord_4049444).sum := by decide
  have hdescent : baseEnd_4049444 < baseStart_4049444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049481 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_4049481 : Nat := 118140960795 + 4049481 * 2 ^ 59
def prefixEnd_4049481 : Nat := 4983230072969 + 3 ^ 40 * 4049481 * 2
def baseEnd_4049481 : Nat := 1386220102833050747109521

theorem tailTrace_4049481 : CollatzResearch.WordTrace tailWord_4049481 prefixEnd_4049481 1386220102833050747109521 := by
  unfold tailWord_4049481
  simp only [CollatzResearch.WordTrace]
  refine ⟨147696705842429408139116297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98464470561619605426077531 147696705842429408139116297)
  ·
    refine ⟨110772529381822056104337223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147696705842429408139116297 110772529381822056104337223)
    ·
      refine ⟨166158794072733084156505835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110772529381822056104337223 166158794072733084156505835)
      ·
        refine ⟨249238191109099626234758753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166158794072733084156505835 249238191109099626234758753)
        ·
          refine ⟨186928643331824719676069065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249238191109099626234758753 186928643331824719676069065)
          ·
            refine ⟨140196482498868539757051799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186928643331824719676069065 140196482498868539757051799)
            ·
              refine ⟨210294723748302809635577699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140196482498868539757051799 210294723748302809635577699)
              ·
                refine ⟨315442085622454214453366549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210294723748302809635577699 315442085622454214453366549)
                ·
                  refine ⟨14786347763552541302501557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 315442085622454214453366549 14786347763552541302501557)
                  ·
                    refine ⟨1386220102833050747109521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14786347763552541302501557 1386220102833050747109521)
                    ·
                      rfl

theorem cell22_4049481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_4049481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049481 prefixEnd_4049481 := by exact prefixLift 4049481
  have htrace : WordTrace (prefixWord ++ tailWord_4049481) baseStart_4049481 baseEnd_4049481 := by
    simpa [prefixWord, tailWord_4049481, baseEnd_4049481] using wordTrace_append hprefix tailTrace_4049481
  have hstable : (prefixWord ++ tailWord_4049481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049481).length < 2 ^ (prefixWord ++ tailWord_4049481).sum := by decide
  have hdescent : baseEnd_4049481 < baseStart_4049481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049543 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_4049543 : Nat := 118140960795 + 4049543 * 2 ^ 59
def prefixEnd_4049543 : Nat := 4983230072969 + 3 ^ 40 * 4049543 * 2
def baseEnd_4049543 : Nat := 1386241326700103252059331

theorem tailTrace_4049543 : CollatzResearch.WordTrace tailWord_4049543 prefixEnd_4049543 1386241326700103252059331 := by
  unfold tailWord_4049543
  simp only [CollatzResearch.WordTrace]
  refine ⟨147698967168204792727873283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98465978112136528485248855 147698967168204792727873283)
  ·
    refine ⟨221548450752307189091809925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147698967168204792727873283 221548450752307189091809925)
    ·
      refine ⟨41540334516057597954714361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221548450752307189091809925 41540334516057597954714361)
      ·
        refine ⟨31155250887043198466035771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41540334516057597954714361 31155250887043198466035771)
        ·
          refine ⟨46732876330564797699053657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31155250887043198466035771 46732876330564797699053657)
          ·
            refine ⟨35049657247923598274290243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46732876330564797699053657 35049657247923598274290243)
            ·
              refine ⟨52574485871885397411435365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35049657247923598274290243 52574485871885397411435365)
              ·
                refine ⟨9857716100978512014644131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52574485871885397411435365 9857716100978512014644131)
                ·
                  refine ⟨14786574151467768021966197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9857716100978512014644131 14786574151467768021966197)
                  ·
                    refine ⟨1386241326700103252059331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14786574151467768021966197 1386241326700103252059331)
                    ·
                      rfl

theorem cell22_4049543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_4049543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049543 prefixEnd_4049543 := by exact prefixLift 4049543
  have htrace : WordTrace (prefixWord ++ tailWord_4049543) baseStart_4049543 baseEnd_4049543 := by
    simpa [prefixWord, tailWord_4049543, baseEnd_4049543] using wordTrace_append hprefix tailTrace_4049543
  have hstable : (prefixWord ++ tailWord_4049543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049543).length < 2 ^ (prefixWord ++ tailWord_4049543).sum := by decide
  have hdescent : baseEnd_4049543 < baseStart_4049543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049560 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_4049560 : Nat := 118140960795 + 4049560 * 2 ^ 59
def prefixEnd_4049560 : Nat := 4983230072969 + 3 ^ 40 * 4049560 * 2
def baseEnd_4049560 : Nat := 1386247146147520874384279

theorem tailTrace_4049560 : CollatzResearch.WordTrace tailWord_4049560 prefixEnd_4049560 1386247146147520874384279 := by
  unfold tailWord_4049560
  simp only [CollatzResearch.WordTrace]
  refine ⟨73849793604571602315621067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98466391472762136420828089 73849793604571602315621067)
  ·
    refine ⟨110774690406857403473431601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73849793604571602315621067 110774690406857403473431601)
    ·
      refine ⟨83081017805143052605073701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110774690406857403473431601 83081017805143052605073701)
      ·
        refine ⟨15577690838464322363451319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83081017805143052605073701 15577690838464322363451319)
        ·
          refine ⟨23366536257696483545176979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15577690838464322363451319 23366536257696483545176979)
          ·
            refine ⟨35049804386544725317765469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23366536257696483545176979 35049804386544725317765469)
            ·
              refine ⟨13143676644954271994162051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35049804386544725317765469 13143676644954271994162051)
              ·
                refine ⟨19715514967431407991243077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13143676644954271994162051 19715514967431407991243077)
                ·
                  refine ⟨3696659056393388998358077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19715514967431407991243077 3696659056393388998358077)
                  ·
                    refine ⟨1386247146147520874384279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696659056393388998358077 1386247146147520874384279)
                    ·
                      rfl

theorem cell22_4049560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_4049560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049560 prefixEnd_4049560 := by exact prefixLift 4049560
  have htrace : WordTrace (prefixWord ++ tailWord_4049560) baseStart_4049560 baseEnd_4049560 := by
    simpa [prefixWord, tailWord_4049560, baseEnd_4049560] using wordTrace_append hprefix tailTrace_4049560
  have hstable : (prefixWord ++ tailWord_4049560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049560).length < 2 ^ (prefixWord ++ tailWord_4049560).sum := by decide
  have hdescent : baseEnd_4049560 < baseStart_4049560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049562 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_4049562 : Nat := 118140960795 + 4049562 * 2 ^ 59
def prefixEnd_4049562 : Nat := 4983230072969 + 3 ^ 40 * 4049562 * 2
def baseEnd_4049562 : Nat := 462082610262797845278091

theorem tailTrace_4049562 : CollatzResearch.WordTrace tailWord_4049562 prefixEnd_4049562 462082610262797845278091 := by
  unfold tailWord_4049562
  simp only [CollatzResearch.WordTrace]
  refine ⟨36924915038783989743203735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98466440103423972648543293 36924915038783989743203735)
  ·
    refine ⟨55387372558175984614805603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36924915038783989743203735 55387372558175984614805603)
    ·
      refine ⟨83081058837263976922208405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55387372558175984614805603 83081058837263976922208405)
      ·
        refine ⟨3894424632996748918228519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83081058837263976922208405 3894424632996748918228519)
        ·
          refine ⟨5841636949495123377342779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894424632996748918228519 5841636949495123377342779)
          ·
            refine ⟨8762455424242685066014169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5841636949495123377342779 8762455424242685066014169)
            ·
              refine ⟨6571841568182013799510627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8762455424242685066014169 6571841568182013799510627)
              ·
                refine ⟨9857762352273020699265941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6571841568182013799510627 9857762352273020699265941)
                ·
                  refine ⟨462082610262797845278091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9857762352273020699265941 462082610262797845278091)
                  ·
                    rfl

theorem cell22_4049562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_4049562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049562 prefixEnd_4049562 := by exact prefixLift 4049562
  have htrace : WordTrace (prefixWord ++ tailWord_4049562) baseStart_4049562 baseEnd_4049562 := by
    simpa [prefixWord, tailWord_4049562, baseEnd_4049562] using wordTrace_append hprefix tailTrace_4049562
  have hstable : (prefixWord ++ tailWord_4049562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049562).length < 2 ^ (prefixWord ++ tailWord_4049562).sum := by decide
  have hdescent : baseEnd_4049562 < baseStart_4049562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049695 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_4049695 : Nat := 118140960795 + 4049695 * 2 ^ 59
def prefixEnd_4049695 : Nat := 4983230072969 + 3 ^ 40 * 4049695 * 2
def baseEnd_4049695 : Nat := 1386293359406425522258865

theorem tailTrace_4049695 : CollatzResearch.WordTrace tailWord_4049695 prefixEnd_4049695 1386293359406425522258865 := by
  unfold tailWord_4049695
  simp only [CollatzResearch.WordTrace]
  refine ⟨147704511063654122687406539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98469674042436081791604359 147704511063654122687406539)
  ·
    refine ⟨221556766595481184031109809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147704511063654122687406539 221556766595481184031109809)
    ·
      refine ⟨166167574946610888023332357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221556766595481184031109809 166167574946610888023332357)
      ·
        refine ⟨31156420302489541504374817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166167574946610888023332357 31156420302489541504374817)
        ·
          refine ⟨23367315226867156128281113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31156420302489541504374817 23367315226867156128281113)
          ·
            refine ⟨17525486420150367096210835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23367315226867156128281113 17525486420150367096210835)
            ·
              refine ⟨26288229630225550644316253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17525486420150367096210835 26288229630225550644316253)
              ·
                refine ⟨9858086111334581491618595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26288229630225550644316253 9858086111334581491618595)
                ·
                  refine ⟨14787129167001872237427893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858086111334581491618595 14787129167001872237427893)
                  ·
                    refine ⟨1386293359406425522258865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14787129167001872237427893 1386293359406425522258865)
                    ·
                      rfl

theorem cell22_4049695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_4049695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049695 prefixEnd_4049695 := by exact prefixLift 4049695
  have htrace : WordTrace (prefixWord ++ tailWord_4049695) baseStart_4049695 baseEnd_4049695 := by
    simpa [prefixWord, tailWord_4049695, baseEnd_4049695] using wordTrace_append hprefix tailTrace_4049695
  have hstable : (prefixWord ++ tailWord_4049695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049695).length < 2 ^ (prefixWord ++ tailWord_4049695).sum := by decide
  have hdescent : baseEnd_4049695 < baseStart_4049695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049815 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 8]
def baseStart_4049815 : Nat := 118140960795 + 4049815 * 2 ^ 59
def prefixEnd_4049815 : Nat := 4983230072969 + 3 ^ 40 * 4049815 * 2
def baseEnd_4049815 : Nat := 462111479286261736419499

theorem tailTrace_4049815 : CollatzResearch.WordTrace tailWord_4049815 prefixEnd_4049815 462111479286261736419499 := by
  unfold tailWord_4049815
  simp only [CollatzResearch.WordTrace]
  refine ⟨147708887823219383181774899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98472591882146255454516599 147708887823219383181774899)
  ·
    refine ⟨221563331734829074772662349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147708887823219383181774899 221563331734829074772662349)
    ·
      refine ⟨83086249400560903039748381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221563331734829074772662349 83086249400560903039748381)
      ·
        refine ⟨31157343525210338639905643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83086249400560903039748381 31157343525210338639905643)
        ·
          refine ⟨46736015287815507959858465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31157343525210338639905643 46736015287815507959858465)
          ·
            refine ⟨35052011465861630969893849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46736015287815507959858465 35052011465861630969893849)
            ·
              refine ⟨26289008599396223227420387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35052011465861630969893849 26289008599396223227420387)
              ·
                refine ⟨39433512899094334841130581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26289008599396223227420387 39433512899094334841130581)
                ·
                  refine ⟨462111479286261736419499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39433512899094334841130581 462111479286261736419499)
                  ·
                    rfl

theorem cell22_4049815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_4049815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049815 prefixEnd_4049815 := by exact prefixLift 4049815
  have htrace : WordTrace (prefixWord ++ tailWord_4049815) baseStart_4049815 baseEnd_4049815 := by
    simpa [prefixWord, tailWord_4049815, baseEnd_4049815] using wordTrace_append hprefix tailTrace_4049815
  have hstable : (prefixWord ++ tailWord_4049815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049815).length < 2 ^ (prefixWord ++ tailWord_4049815).sum := by decide
  have hdescent : baseEnd_4049815 < baseStart_4049815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049847 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 4, 3]
def baseStart_4049847 : Nat := 118140960795 + 4049847 * 2 ^ 59
def prefixEnd_4049847 : Nat := 4983230072969 + 3 ^ 40 * 4049847 * 2
def baseEnd_4049847 : Nat := 1386345392112747792458399

theorem tailTrace_4049847 : CollatzResearch.WordTrace tailWord_4049847 prefixEnd_4049847 1386345392112747792458399 := by
  unfold tailWord_4049847
  simp only [CollatzResearch.WordTrace]
  refine ⟨147710054959103452646939795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98473369972735635097959863 147710054959103452646939795)
  ·
    refine ⟨221565082438655178970409693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147710054959103452646939795 221565082438655178970409693)
    ·
      refine ⟨83086905914495692113903635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221565082438655178970409693 83086905914495692113903635)
      ·
        refine ⟨124630358871743538170855453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83086905914495692113903635 124630358871743538170855453)
        ·
          refine ⟨46736384576903826814070795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124630358871743538170855453 46736384576903826814070795)
          ·
            refine ⟨70104576865355740221106193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46736384576903826814070795 70104576865355740221106193)
            ·
              refine ⟨52578432649016805165829645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70104576865355740221106193 52578432649016805165829645)
              ·
                refine ⟨19716912243381301937186117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52578432649016805165829645 19716912243381301937186117)
                ·
                  refine ⟨3696921045633994113222397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19716912243381301937186117 3696921045633994113222397)
                  ·
                    refine ⟨1386345392112747792458399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696921045633994113222397 1386345392112747792458399)
                    ·
                      rfl

theorem cell22_4049847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_4049847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049847 prefixEnd_4049847 := by exact prefixLift 4049847
  have htrace : WordTrace (prefixWord ++ tailWord_4049847) baseStart_4049847 baseEnd_4049847 := by
    simpa [prefixWord, tailWord_4049847, baseEnd_4049847] using wordTrace_append hprefix tailTrace_4049847
  have hstable : (prefixWord ++ tailWord_4049847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049847).length < 2 ^ (prefixWord ++ tailWord_4049847).sum := by decide
  have hdescent : baseEnd_4049847 < baseStart_4049847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049849 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 4]
def baseStart_4049849 : Nat := 118140960795 + 4049849 * 2 ^ 59
def prefixEnd_4049849 : Nat := 4983230072969 + 3 ^ 40 * 4049849 * 2
def baseEnd_4049849 : Nat := 462115358917873484636131

theorem tailTrace_4049849 : CollatzResearch.WordTrace tailWord_4049849 prefixEnd_4049849 462115358917873484636131 := by
  unfold tailWord_4049849
  simp only [CollatzResearch.WordTrace]
  refine ⟨147710127905096206988512601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98473418603397471325675067 147710127905096206988512601)
  ·
    refine ⟨110782595928822155241384451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147710127905096206988512601 110782595928822155241384451)
    ·
      refine ⟨166173893893233232862076677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110782595928822155241384451 166173893893233232862076677)
      ·
        refine ⟨31157605104981231161639377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166173893893233232862076677 31157605104981231161639377)
        ·
          refine ⟨23368203828735923371229533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31157605104981231161639377 23368203828735923371229533)
          ·
            refine ⟨8763076435775971264211075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23368203828735923371229533 8763076435775971264211075)
            ·
              refine ⟨13144614653663956896316613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763076435775971264211075 13144614653663956896316613)
              ·
                refine ⟨2464615247561991918059365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13144614653663956896316613 2464615247561991918059365)
                ·
                  refine ⟨462115358917873484636131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464615247561991918059365 462115358917873484636131)
                  ·
                    rfl

theorem cell22_4049849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_4049849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049849 prefixEnd_4049849 := by exact prefixLift 4049849
  have htrace : WordTrace (prefixWord ++ tailWord_4049849) baseStart_4049849 baseEnd_4049849 := by
    simpa [prefixWord, tailWord_4049849, baseEnd_4049849] using wordTrace_append hprefix tailTrace_4049849
  have hstable : (prefixWord ++ tailWord_4049849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049849).length < 2 ^ (prefixWord ++ tailWord_4049849).sum := by decide
  have hdescent : baseEnd_4049849 < baseStart_4049849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049864 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_4049864 : Nat := 118140960795 + 4049864 * 2 ^ 59
def prefixEnd_4049864 : Nat := 4983230072969 + 3 ^ 40 * 4049864 * 2
def baseEnd_4049864 : Nat := 1386351211560165414783347

theorem tailTrace_4049864 : CollatzResearch.WordTrace tailWord_4049864 prefixEnd_4049864 1386351211560165414783347 := by
  unfold tailWord_4049864
  simp only [CollatzResearch.WordTrace]
  refine ⟨73855337500020932275154323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98473783333361243033539097 73855337500020932275154323)
  ·
    refine ⟨110783006250031398412731485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73855337500020932275154323 110783006250031398412731485)
    ·
      refine ⟨41543627343761774404774307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110783006250031398412731485 41543627343761774404774307)
      ·
        refine ⟨62315441015642661607161461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41543627343761774404774307 62315441015642661607161461)
        ·
          refine ⟨5842072595216499525671387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62315441015642661607161461 5842072595216499525671387)
          ·
            refine ⟨8763108892824749288507081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842072595216499525671387 8763108892824749288507081)
            ·
              refine ⟨6572331669618561966380311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8763108892824749288507081 6572331669618561966380311)
              ·
                refine ⟨9858497504427842949570467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572331669618561966380311 9858497504427842949570467)
                ·
                  refine ⟨14787746256641764424355701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858497504427842949570467 14787746256641764424355701)
                  ·
                    refine ⟨1386351211560165414783347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14787746256641764424355701 1386351211560165414783347)
                    ·
                      rfl

theorem cell22_4049864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_4049864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049864 prefixEnd_4049864 := by exact prefixLift 4049864
  have htrace : WordTrace (prefixWord ++ tailWord_4049864) baseStart_4049864 baseEnd_4049864 := by
    simpa [prefixWord, tailWord_4049864, baseEnd_4049864] using wordTrace_append hprefix tailTrace_4049864
  have hstable : (prefixWord ++ tailWord_4049864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049864).length < 2 ^ (prefixWord ++ tailWord_4049864).sum := by decide
  have hdescent : baseEnd_4049864 < baseStart_4049864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4049943 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 1, 3]
def baseStart_4049943 : Nat := 118140960795 + 4049943 * 2 ^ 59
def prefixEnd_4049943 : Nat := 4983230072969 + 3 ^ 40 * 4049943 * 2
def baseEnd_4049943 : Nat := 1386378254874635542058105

theorem tailTrace_4049943 : CollatzResearch.WordTrace tailWord_4049943 prefixEnd_4049943 1386378254874635542058105 := by
  unfold tailWord_4049943
  simp only [CollatzResearch.WordTrace]
  refine ⟨147713556366755661042434483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98475704244503774028289655 147713556366755661042434483)
  ·
    refine ⟨221570334550133491563651725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147713556366755661042434483 221570334550133491563651725)
    ·
      refine ⟨83088875456300059336369397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221570334550133491563651725 83088875456300059336369397)
      ·
        refine ⟨7789582074028130562784631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83088875456300059336369397 7789582074028130562784631)
        ·
          refine ⟨11684373111042195844176947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789582074028130562784631 11684373111042195844176947)
          ·
            refine ⟨17526559666563293766265421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684373111042195844176947 17526559666563293766265421)
            ·
              refine ⟨6572459874961235162349533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17526559666563293766265421 6572459874961235162349533)
              ·
                refine ⟨2464672453110463185881075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6572459874961235162349533 2464672453110463185881075)
                ·
                  refine ⟨3697008679665694778821613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464672453110463185881075 3697008679665694778821613)
                  ·
                    refine ⟨1386378254874635542058105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697008679665694778821613 1386378254874635542058105)
                    ·
                      rfl

theorem cell22_4049943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_4049943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4049943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4049943 prefixEnd_4049943 := by exact prefixLift 4049943
  have htrace : WordTrace (prefixWord ++ tailWord_4049943) baseStart_4049943 baseEnd_4049943 := by
    simpa [prefixWord, tailWord_4049943, baseEnd_4049943] using wordTrace_append hprefix tailTrace_4049943
  have hstable : (prefixWord ++ tailWord_4049943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4049943).length < 2 ^ (prefixWord ++ tailWord_4049943).sum := by decide
  have hdescent : baseEnd_4049943 < baseStart_4049943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4049943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050016 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_4050016 : Nat := 118140960795 + 4050016 * 2 ^ 59
def prefixEnd_4050016 : Nat := 4983230072969 + 3 ^ 40 * 4050016 * 2
def baseEnd_4050016 : Nat := 1386403244266487684982881

theorem tailTrace_4050016 : CollatzResearch.WordTrace tailWord_4050016 prefixEnd_4050016 1386403244266487684982881 := by
  unfold tailWord_4050016
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858109447745597254920951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98477479263660796339894601 73858109447745597254920951)
  ·
    refine ⟨110787164171618395882381427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73858109447745597254920951 110787164171618395882381427)
    ·
      refine ⟨166180746257427593823572141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110787164171618395882381427 166180746257427593823572141)
      ·
        refine ⟨62317779846535347683839553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166180746257427593823572141 62317779846535347683839553)
        ·
          refine ⟨46738334884901510762879665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62317779846535347683839553 46738334884901510762879665)
          ·
            refine ⟨35053751163676133072159749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46738334884901510762879665 35053751163676133072159749)
            ·
              refine ⟨6572578343189274951029953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35053751163676133072159749 6572578343189274951029953)
              ·
                refine ⟨4929433757391956213272465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6572578343189274951029953 4929433757391956213272465)
                ·
                  refine ⟨3697075318043967159954349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929433757391956213272465 3697075318043967159954349)
                  ·
                    refine ⟨1386403244266487684982881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697075318043967159954349 1386403244266487684982881)
                    ·
                      rfl

theorem cell22_4050016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_4050016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050016 prefixEnd_4050016 := by exact prefixLift 4050016
  have htrace : WordTrace (prefixWord ++ tailWord_4050016) baseStart_4050016 baseEnd_4050016 := by
    simpa [prefixWord, tailWord_4050016, baseEnd_4050016] using wordTrace_append hprefix tailTrace_4050016
  have hstable : (prefixWord ++ tailWord_4050016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050016).length < 2 ^ (prefixWord ++ tailWord_4050016).sum := by decide
  have hdescent : baseEnd_4050016 < baseStart_4050016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050018 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_4050018 : Nat := 118140960795 + 4050018 * 2 ^ 59
def prefixEnd_4050018 : Nat := 4983230072969 + 3 ^ 40 * 4050018 * 2
def baseEnd_4050018 : Nat := 462134642969120115477625

theorem tailTrace_4050018 : CollatzResearch.WordTrace tailWord_4050018 prefixEnd_4050018 462134642969120115477625 := by
  unfold tailWord_4050018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36929072960370987212853677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98477527894322632567609805 36929072960370987212853677)
  ·
    refine ⟨13848402360139120204820129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36929072960370987212853677 13848402360139120204820129)
    ·
      refine ⟨10386301770104340153615097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13848402360139120204820129 10386301770104340153615097)
      ·
        refine ⟨7789726327578255115211323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386301770104340153615097 7789726327578255115211323)
        ·
          refine ⟨11684589491367382672816985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7789726327578255115211323 11684589491367382672816985)
          ·
            refine ⟨8763442118525537004612739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11684589491367382672816985 8763442118525537004612739)
            ·
              refine ⟨13145163177788305506919109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763442118525537004612739 13145163177788305506919109)
              ·
                refine ⟨2464718095835307282547333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13145163177788305506919109 2464718095835307282547333)
                ·
                  refine ⟨462134642969120115477625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2464718095835307282547333 462134642969120115477625)
                  ·
                    rfl

theorem cell22_4050018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_4050018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050018 prefixEnd_4050018 := by exact prefixLift 4050018
  have htrace : WordTrace (prefixWord ++ tailWord_4050018) baseStart_4050018 baseEnd_4050018 := by
    simpa [prefixWord, tailWord_4050018, baseEnd_4050018] using wordTrace_append hprefix tailTrace_4050018
  have hstable : (prefixWord ++ tailWord_4050018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050018).length < 2 ^ (prefixWord ++ tailWord_4050018).sum := by decide
  have hdescent : baseEnd_4050018 < baseStart_4050018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050029 : List Nat := [1, 5, 1, 1, 2, 2, 3, 7]
def baseStart_4050029 : Nat := 118140960795 + 4050029 * 2 ^ 59
def prefixEnd_4050029 : Nat := 4983230072969 + 3 ^ 40 * 4050029 * 2
def baseEnd_4050029 : Nat := 154045299381351109378649

theorem tailTrace_4050029 : CollatzResearch.WordTrace tailWord_4050029 prefixEnd_4050029 154045299381351109378649 := by
  unfold tailWord_4050029
  simp only [CollatzResearch.WordTrace]
  refine ⟨147716693044444097730065141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98477795362962731820043427 147716693044444097730065141)
  ·
    refine ⟨13848439972916634162193607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147716693044444097730065141 13848439972916634162193607)
    ·
      refine ⟨20772659959374951243290411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13848439972916634162193607 20772659959374951243290411)
      ·
        refine ⟨31158989939062426864935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20772659959374951243290411 31158989939062426864935617)
        ·
          refine ⟨23369242454296820148701713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31158989939062426864935617 23369242454296820148701713)
          ·
            refine ⟨17526931840722615111526285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23369242454296820148701713 17526931840722615111526285)
            ·
              refine ⟨6572599440270980666822357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17526931840722615111526285 6572599440270980666822357)
              ·
                refine ⟨154045299381351109378649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6572599440270980666822357 154045299381351109378649)
                ·
                  rfl

theorem cell22_4050029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 7].length) (baseStart_4050029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050029 prefixEnd_4050029 := by exact prefixLift 4050029
  have htrace : WordTrace (prefixWord ++ tailWord_4050029) baseStart_4050029 baseEnd_4050029 := by
    simpa [prefixWord, tailWord_4050029, baseEnd_4050029] using wordTrace_append hprefix tailTrace_4050029
  have hstable : (prefixWord ++ tailWord_4050029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050029).length < 2 ^ (prefixWord ++ tailWord_4050029).sum := by decide
  have hdescent : baseEnd_4050029 < baseStart_4050029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050078 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4050078 : Nat := 118140960795 + 4050078 * 2 ^ 59
def prefixEnd_4050078 : Nat := 4983230072969 + 3 ^ 40 * 4050078 * 2
def baseEnd_4050078 : Nat := 1386424468133540189932691

theorem tailTrace_4050078 : CollatzResearch.WordTrace tailWord_4050078 prefixEnd_4050078 1386424468133540189932691 := by
  unfold tailWord_4050078
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464810027658322387324861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98478986814177719399065925 18464810027658322387324861)
  ·
    refine ⟨6924303760371870895246823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18464810027658322387324861 6924303760371870895246823)
    ·
      refine ⟨10386455640557806342870235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924303760371870895246823 10386455640557806342870235)
      ·
        refine ⟨15579683460836709514305353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386455640557806342870235 15579683460836709514305353)
        ·
          refine ⟨11684762595627532135729015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15579683460836709514305353 11684762595627532135729015)
          ·
            refine ⟨17527143893441298203593523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11684762595627532135729015 17527143893441298203593523)
            ·
              refine ⟨26290715840161947305390285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17527143893441298203593523 26290715840161947305390285)
              ·
                refine ⟨9859018440060730239521357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26290715840161947305390285 9859018440060730239521357)
                ·
                  refine ⟨3697131915022773839820509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9859018440060730239521357 3697131915022773839820509)
                  ·
                    refine ⟨1386424468133540189932691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697131915022773839820509 1386424468133540189932691)
                    ·
                      rfl

theorem cell22_4050078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4050078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050078 prefixEnd_4050078 := by exact prefixLift 4050078
  have htrace : WordTrace (prefixWord ++ tailWord_4050078) baseStart_4050078 baseEnd_4050078 := by
    simpa [prefixWord, tailWord_4050078, baseEnd_4050078] using wordTrace_append hprefix tailTrace_4050078
  have hstable : (prefixWord ++ tailWord_4050078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050078).length < 2 ^ (prefixWord ++ tailWord_4050078).sum := by decide
  have hdescent : baseEnd_4050078 < baseStart_4050078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050112 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 1, 3]
def baseStart_4050112 : Nat := 118140960795 + 4050112 * 2 ^ 59
def prefixEnd_4050112 : Nat := 4983230072969 + 3 ^ 40 * 4050112 * 2
def baseEnd_4050112 : Nat := 1386436107028375434582587

theorem tailTrace_4050112 : CollatzResearch.WordTrace tailWord_4050112 prefixEnd_4050112 1386436107028375434582587 := by
  unfold tailWord_4050112
  simp only [CollatzResearch.WordTrace]
  refine ⟨73859860151571701452668295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98479813535428935270224393 73859860151571701452668295)
  ·
    refine ⟨110789790227357552179002443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73859860151571701452668295 110789790227357552179002443)
    ·
      refine ⟨166184685341036328268503665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110789790227357552179002443 166184685341036328268503665)
      ·
        refine ⟨124638514005777246201377749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166184685341036328268503665 124638514005777246201377749)
        ·
          refine ⟨2921215172010404207844791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124638514005777246201377749 2921215172010404207844791)
          ·
            refine ⟨4381822758015606311767187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921215172010404207844791 4381822758015606311767187)
            ·
              refine ⟨6572734137023409467650781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381822758015606311767187 6572734137023409467650781)
              ·
                refine ⟨2464775301383778550369043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6572734137023409467650781 2464775301383778550369043)
                ·
                  refine ⟨3697162952075667825553565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464775301383778550369043 3697162952075667825553565)
                  ·
                    refine ⟨1386436107028375434582587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697162952075667825553565 1386436107028375434582587)
                    ·
                      rfl

theorem cell22_4050112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_4050112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050112 prefixEnd_4050112 := by exact prefixLift 4050112
  have htrace : WordTrace (prefixWord ++ tailWord_4050112) baseStart_4050112 baseEnd_4050112 := by
    simpa [prefixWord, tailWord_4050112, baseEnd_4050112] using wordTrace_append hprefix tailTrace_4050112
  have hstable : (prefixWord ++ tailWord_4050112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050112).length < 2 ^ (prefixWord ++ tailWord_4050112).sum := by decide
  have hdescent : baseEnd_4050112 < baseStart_4050112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050209 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 9]
def baseStart_4050209 : Nat := 118140960795 + 4050209 * 2 ^ 59
def prefixEnd_4050209 : Nat := 4983230072969 + 3 ^ 40 * 4050209 * 2
def baseEnd_4050209 : Nat := 462156437370233171635763

theorem tailTrace_4050209 : CollatzResearch.WordTrace tailWord_4050209 prefixEnd_4050209 462156437370233171635763 := by
  unfold tailWord_4050209
  simp only [CollatzResearch.WordTrace]
  refine ⟨147723258183791988471617681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98482172122527992314411787 147723258183791988471617681)
  ·
    refine ⟨110792443637843991353713261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147723258183791988471617681 110792443637843991353713261)
    ·
      refine ⟨41547166364191496757642473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110792443637843991353713261 41547166364191496757642473)
      ·
        refine ⟨31160374773143622568231855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41547166364191496757642473 31160374773143622568231855)
        ·
          refine ⟨46740562159715433852347783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31160374773143622568231855 46740562159715433852347783)
          ·
            refine ⟨70110843239573150778521675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46740562159715433852347783 70110843239573150778521675)
            ·
              refine ⟨105166264859359726167782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70110843239573150778521675 105166264859359726167782513)
              ·
                refine ⟨78874698644519794625836885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105166264859359726167782513 78874698644519794625836885)
                ·
                  refine ⟨462156437370233171635763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78874698644519794625836885 462156437370233171635763)
                  ·
                    rfl

theorem cell22_4050209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_4050209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050209 prefixEnd_4050209 := by exact prefixLift 4050209
  have htrace : WordTrace (prefixWord ++ tailWord_4050209) baseStart_4050209 baseEnd_4050209 := by
    simpa [prefixWord, tailWord_4050209, baseEnd_4050209] using wordTrace_append hprefix tailTrace_4050209
  have hstable : (prefixWord ++ tailWord_4050209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050209).length < 2 ^ (prefixWord ++ tailWord_4050209).sum := by decide
  have hdescent : baseEnd_4050209 < baseStart_4050209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050213 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_4050213 : Nat := 118140960795 + 4050213 * 2 ^ 59
def prefixEnd_4050213 : Nat := 4983230072969 + 3 ^ 40 * 4050213 * 2
def baseEnd_4050213 : Nat := 1386470681392444837807277

theorem tailTrace_4050213 : CollatzResearch.WordTrace tailWord_4050213 prefixEnd_4050213 1386470681392444837807277 := by
  unfold tailWord_4050213
  simp only [CollatzResearch.WordTrace]
  refine ⟨147723404075777497154763293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98482269383851664769842195 147723404075777497154763293)
  ·
    refine ⟨55396276528416561433036235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147723404075777497154763293 55396276528416561433036235)
    ·
      refine ⟨83094414792624842149554353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55396276528416561433036235 83094414792624842149554353)
      ·
        refine ⟨62320811094468631612165765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83094414792624842149554353 62320811094468631612165765)
        ·
          refine ⟨11685152080212868427281081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62320811094468631612165765 11685152080212868427281081)
          ·
            refine ⟨8763864060159651320460811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11685152080212868427281081 8763864060159651320460811)
            ·
              refine ⟨13145796090239476980691217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763864060159651320460811 13145796090239476980691217)
              ·
                refine ⟨9859347067679607735518413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13145796090239476980691217 9859347067679607735518413)
                ·
                  refine ⟨3697255150379852900819405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9859347067679607735518413 3697255150379852900819405)
                  ·
                    refine ⟨1386470681392444837807277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697255150379852900819405 1386470681392444837807277)
                    ·
                      rfl

theorem cell22_4050213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_4050213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050213 prefixEnd_4050213 := by exact prefixLift 4050213
  have htrace : WordTrace (prefixWord ++ tailWord_4050213) baseStart_4050213 baseEnd_4050213 := by
    simpa [prefixWord, tailWord_4050213, baseEnd_4050213] using wordTrace_append hprefix tailTrace_4050213
  have hstable : (prefixWord ++ tailWord_4050213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050213).length < 2 ^ (prefixWord ++ tailWord_4050213).sum := by decide
  have hdescent : baseEnd_4050213 < baseStart_4050213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050224 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_4050224 : Nat := 118140960795 + 4050224 * 2 ^ 59
def prefixEnd_4050224 : Nat := 4983230072969 + 3 ^ 40 * 4050224 * 2
def baseEnd_4050224 : Nat := 1386474446917244475782243

theorem tailTrace_4050224 : CollatzResearch.WordTrace tailWord_4050224 prefixEnd_4050224 1386474446917244475782243 := by
  unfold tailWord_4050224
  simp only [CollatzResearch.WordTrace]
  refine ⟨73861902639368823016706863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98482536852491764022275817 73861902639368823016706863)
  ·
    refine ⟨110792853959053234525060295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73861902639368823016706863 110792853959053234525060295)
    ·
      refine ⟨166189280938579851787590443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110792853959053234525060295 166189280938579851787590443)
      ·
        refine ⟨249283921407869777681385665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166189280938579851787590443 249283921407869777681385665)
        ·
          refine ⟨186962941055902333261039249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249283921407869777681385665 186962941055902333261039249)
          ·
            refine ⟨140222205791926749945779437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186962941055902333261039249 140222205791926749945779437)
            ·
              refine ⟨52583327171972531229667289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140222205791926749945779437 52583327171972531229667289)
              ·
                refine ⟨39437495378979398422250467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52583327171972531229667289 39437495378979398422250467)
                ·
                  refine ⟨59156243068469097633375701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39437495378979398422250467 59156243068469097633375701)
                  ·
                    refine ⟨1386474446917244475782243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59156243068469097633375701 1386474446917244475782243)
                    ·
                      rfl

theorem cell22_4050224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_4050224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050224 prefixEnd_4050224 := by exact prefixLift 4050224
  have htrace : WordTrace (prefixWord ++ tailWord_4050224) baseStart_4050224 baseEnd_4050224 := by
    simpa [prefixWord, tailWord_4050224, baseEnd_4050224] using wordTrace_append hprefix tailTrace_4050224
  have hstable : (prefixWord ++ tailWord_4050224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050224).length < 2 ^ (prefixWord ++ tailWord_4050224).sum := by decide
  have hdescent : baseEnd_4050224 < baseStart_4050224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050305 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 6]
def baseStart_4050305 : Nat := 118140960795 + 4050305 * 2 ^ 59
def prefixEnd_4050305 : Nat := 4983230072969 + 3 ^ 40 * 4050305 * 2
def baseEnd_4050305 : Nat := 462167391624195754835665

theorem tailTrace_4050305 : CollatzResearch.WordTrace tailWord_4050305 prefixEnd_4050305 462167391624195754835665 := by
  unfold tailWord_4050305
  simp only [CollatzResearch.WordTrace]
  refine ⟨147726759591444196867112369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98484506394296131244741579 147726759591444196867112369)
  ·
    refine ⟨110795069693583147650334277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147726759591444196867112369 110795069693583147650334277)
    ·
      refine ⟨20774075567546840184437677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110795069693583147650334277 20774075567546840184437677)
      ·
        refine ⟨7790278337830065069164129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20774075567546840184437677 7790278337830065069164129)
        ·
          refine ⟨5842708753372548801873097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7790278337830065069164129 5842708753372548801873097)
          ·
            refine ⟨4382031565029411601404823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5842708753372548801873097 4382031565029411601404823)
            ·
              refine ⟨6573047347544117402107235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382031565029411601404823 6573047347544117402107235)
              ·
                refine ⟨9859571021316176103160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573047347544117402107235 9859571021316176103160853)
                ·
                  refine ⟨462167391624195754835665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9859571021316176103160853 462167391624195754835665)
                  ·
                    rfl

theorem cell22_4050305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_4050305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050305 prefixEnd_4050305 := by exact prefixLift 4050305
  have htrace : WordTrace (prefixWord ++ tailWord_4050305) baseStart_4050305 baseEnd_4050305 := by
    simpa [prefixWord, tailWord_4050305, baseEnd_4050305] using wordTrace_append hprefix tailTrace_4050305
  have hstable : (prefixWord ++ tailWord_4050305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050305).length < 2 ^ (prefixWord ++ tailWord_4050305).sum := by decide
  have hdescent : baseEnd_4050305 < baseStart_4050305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050316 : List Nat := [2, 2, 1, 2, 1, 3, 4, 7]
def baseStart_4050316 : Nat := 118140960795 + 4050316 * 2 ^ 59
def prefixEnd_4050316 : Nat := 4983230072969 + 3 ^ 40 * 4050316 * 2
def baseEnd_4050316 : Nat := 154056215599709655831329

theorem tailTrace_4050316 : CollatzResearch.WordTrace tailWord_4050316 prefixEnd_4050316 154056215599709655831329 := by
  unfold tailWord_4050316
  simp only [CollatzResearch.WordTrace]
  refine ⟨73863580397202172872881401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98484773862936230497175201 73863580397202172872881401)
  ·
    refine ⟨55397685297901629654661051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73863580397202172872881401 55397685297901629654661051)
    ·
      refine ⟨83096527946852444481991577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55397685297901629654661051 83096527946852444481991577)
      ·
        refine ⟨62322395960139333361493683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83096527946852444481991577 62322395960139333361493683)
        ·
          refine ⟨93483593940209000042240525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62322395960139333361493683 93483593940209000042240525)
          ·
            refine ⟨35056347727578375015840197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93483593940209000042240525 35056347727578375015840197)
            ·
              refine ⟨6573065198920945315470037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35056347727578375015840197 6573065198920945315470037)
              ·
                refine ⟨154056215599709655831329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6573065198920945315470037 154056215599709655831329)
                ·
                  rfl

theorem cell22_4050316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_4050316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050316 prefixEnd_4050316 := by exact prefixLift 4050316
  have htrace : WordTrace (prefixWord ++ tailWord_4050316) baseStart_4050316 baseEnd_4050316 := by
    simpa [prefixWord, tailWord_4050316, baseEnd_4050316] using wordTrace_append hprefix tailTrace_4050316
  have hstable : (prefixWord ++ tailWord_4050316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050316).length < 2 ^ (prefixWord ++ tailWord_4050316).sum := by decide
  have hdescent : baseEnd_4050316 < baseStart_4050316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050378 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_4050378 : Nat := 118140960795 + 4050378 * 2 ^ 59
def prefixEnd_4050378 : Nat := 4983230072969 + 3 ^ 40 * 4050378 * 2
def baseEnd_4050378 : Nat := 462175721421479802477257

theorem tailTrace_4050378 : CollatzResearch.WordTrace tailWord_4050378 prefixEnd_4050378 462175721421479802477257 := by
  unfold tailWord_4050378
  simp only [CollatzResearch.WordTrace]
  refine ⟨36932355530044932583629947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98486281413453153556346525 36932355530044932583629947)
  ·
    refine ⟨55398533295067398875444921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36932355530044932583629947 55398533295067398875444921)
    ·
      refine ⟨41548899971300549156583691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55398533295067398875444921 41548899971300549156583691)
      ·
        refine ⟨62323349956950823734875537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41548899971300549156583691 62323349956950823734875537)
        ·
          refine ⟨46742512467713117801156653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62323349956950823734875537 46742512467713117801156653)
          ·
            refine ⟨17528442175392419175433745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46742512467713117801156653 17528442175392419175433745)
            ·
              refine ⟨13146331631544314381575309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17528442175392419175433745 13146331631544314381575309)
              ·
                refine ⟨4929874361829117893090741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13146331631544314381575309 4929874361829117893090741)
                ·
                  refine ⟨462175721421479802477257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4929874361829117893090741 462175721421479802477257)
                  ·
                    rfl

theorem cell22_4050378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_4050378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050378 prefixEnd_4050378 := by exact prefixLift 4050378
  have htrace : WordTrace (prefixWord ++ tailWord_4050378) baseStart_4050378 baseEnd_4050378 := by
    simpa [prefixWord, tailWord_4050378, baseEnd_4050378] using wordTrace_append hprefix tailTrace_4050378
  have hstable : (prefixWord ++ tailWord_4050378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050378).length < 2 ^ (prefixWord ++ tailWord_4050378).sum := by decide
  have hdescent : baseEnd_4050378 < baseStart_4050378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050453 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_4050453 : Nat := 118140960795 + 4050453 * 2 ^ 59
def prefixEnd_4050453 : Nat := 4983230072969 + 3 ^ 40 * 4050453 * 2
def baseEnd_4050453 : Nat := 1386552838297164211806541

theorem tailTrace_4050453 : CollatzResearch.WordTrace tailWord_4050453 prefixEnd_4050453 1386552838297164211806541 := by
  unfold tailWord_4050453
  simp only [CollatzResearch.WordTrace]
  refine ⟨147732157594908018143500013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98488105063272012095666675 147732157594908018143500013)
  ·
    refine ⟨55399559098090506803812505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147732157594908018143500013 55399559098090506803812505)
    ·
      refine ⟨41549669323567880102859379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55399559098090506803812505 41549669323567880102859379)
      ·
        refine ⟨62324503985351820154289069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41549669323567880102859379 62324503985351820154289069)
        ·
          refine ⟨23371688994506932557858401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62324503985351820154289069 23371688994506932557858401)
          ·
            refine ⟨17528766745880199418393801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23371688994506932557858401 17528766745880199418393801)
            ·
              refine ⟨13146575059410149563795351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17528766745880199418393801 13146575059410149563795351)
              ·
                refine ⟨19719862589115224345693027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13146575059410149563795351 19719862589115224345693027)
                ·
                  refine ⟨29579793883672836518539541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19719862589115224345693027 29579793883672836518539541)
                  ·
                    refine ⟨1386552838297164211806541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29579793883672836518539541 1386552838297164211806541)
                    ·
                      rfl

theorem cell22_4050453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_4050453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050453 prefixEnd_4050453 := by exact prefixLift 4050453
  have htrace : WordTrace (prefixWord ++ tailWord_4050453) baseStart_4050453 baseEnd_4050453 := by
    simpa [prefixWord, tailWord_4050453, baseEnd_4050453] using wordTrace_append hprefix tailTrace_4050453
  have hstable : (prefixWord ++ tailWord_4050453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050453).length < 2 ^ (prefixWord ++ tailWord_4050453).sum := by decide
  have hdescent : baseEnd_4050453 < baseStart_4050453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050489 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_4050489 : Nat := 118140960795 + 4050489 * 2 ^ 59
def prefixEnd_4050489 : Nat := 4983230072969 + 3 ^ 40 * 4050489 * 2
def baseEnd_4050489 : Nat := 1386565161832872117906431

theorem tailTrace_4050489 : CollatzResearch.WordTrace tailWord_4050489 prefixEnd_4050489 1386565161832872117906431 := by
  unfold tailWord_4050489
  simp only [CollatzResearch.WordTrace]
  refine ⟨147733470622777596291810521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98488980415185064194540347 147733470622777596291810521)
  ·
    refine ⟨110800102967083197218857891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147733470622777596291810521 110800102967083197218857891)
    ·
      refine ⟨166200154450624795828286837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110800102967083197218857891 166200154450624795828286837)
      ·
        refine ⟨15581264479746074608901891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166200154450624795828286837 15581264479746074608901891)
        ·
          refine ⟨23371896719619111913352837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581264479746074608901891 23371896719619111913352837)
          ·
            refine ⟨4382230634928583483753657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23371896719619111913352837 4382230634928583483753657)
            ·
              refine ⟨3286672976196437612815243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382230634928583483753657 3286672976196437612815243)
              ·
                refine ⟨4930009464294656419222865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286672976196437612815243 4930009464294656419222865)
                ·
                  refine ⟨3697507098220992314417149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930009464294656419222865 3697507098220992314417149)
                  ·
                    refine ⟨1386565161832872117906431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697507098220992314417149 1386565161832872117906431)
                    ·
                      rfl

theorem cell22_4050489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_4050489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050489 prefixEnd_4050489 := by exact prefixLift 4050489
  have htrace : WordTrace (prefixWord ++ tailWord_4050489) baseStart_4050489 baseEnd_4050489 := by
    simpa [prefixWord, tailWord_4050489, baseEnd_4050489] using wordTrace_append hprefix tailTrace_4050489
  have hstable : (prefixWord ++ tailWord_4050489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050489).length < 2 ^ (prefixWord ++ tailWord_4050489).sum := by decide
  have hdescent : baseEnd_4050489 < baseStart_4050489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050517 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_4050517 : Nat := 118140960795 + 4050517 * 2 ^ 59
def prefixEnd_4050517 : Nat := 4983230072969 + 3 ^ 40 * 4050517 * 2
def baseEnd_4050517 : Nat := 1386574746805089378206345

theorem tailTrace_4050517 : CollatzResearch.WordTrace tailWord_4050517 prefixEnd_4050517 1386574746805089378206345 := by
  unfold tailWord_4050517
  simp only [CollatzResearch.WordTrace]
  refine ⟨147734491866676157073829805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98489661244450771382553203 147734491866676157073829805)
  ·
    refine ⟨55400434450003558902686177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147734491866676157073829805 55400434450003558902686177)
    ·
      refine ⟨41550325837502669177014633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55400434450003558902686177 41550325837502669177014633)
      ·
        refine ⟨31162744378127001882760975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41550325837502669177014633 31162744378127001882760975)
        ·
          refine ⟨46744116567190502824141463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31162744378127001882760975 46744116567190502824141463)
          ·
            refine ⟨70116174850785754236212195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46744116567190502824141463 70116174850785754236212195)
            ·
              refine ⟨105174262276178631354318293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70116174850785754236212195 105174262276178631354318293)
              ·
                refine ⟨2465021772097936672366835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105174262276178631354318293 2465021772097936672366835)
                ·
                  refine ⟨3697532658146905008550253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465021772097936672366835 3697532658146905008550253)
                  ·
                    refine ⟨1386574746805089378206345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697532658146905008550253 1386574746805089378206345)
                    ·
                      rfl

theorem cell22_4050517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_4050517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050517 prefixEnd_4050517 := by exact prefixLift 4050517
  have htrace : WordTrace (prefixWord ++ tailWord_4050517) baseStart_4050517 baseEnd_4050517 := by
    simpa [prefixWord, tailWord_4050517, baseEnd_4050517] using wordTrace_append hprefix tailTrace_4050517
  have hstable : (prefixWord ++ tailWord_4050517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050517).length < 2 ^ (prefixWord ++ tailWord_4050517).sum := by decide
  have hdescent : baseEnd_4050517 < baseStart_4050517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050528 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_4050528 : Nat := 118140960795 + 4050528 * 2 ^ 59
def prefixEnd_4050528 : Nat := 4983230072969 + 3 ^ 40 * 4050528 * 2
def baseEnd_4050528 : Nat := 1386578512329889016181311

theorem tailTrace_4050528 : CollatzResearch.WordTrace tailWord_4050528 prefixEnd_4050528 1386578512329889016181311 := by
  unfold tailWord_4050528
  simp only [CollatzResearch.WordTrace]
  refine ⟨73867446534818152976240119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98489928713090870634986825 73867446534818152976240119)
  ·
    refine ⟨110801169802227229464360179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73867446534818152976240119 110801169802227229464360179)
    ·
      refine ⟨166201754703340844196540269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110801169802227229464360179 166201754703340844196540269)
      ·
        refine ⟨62325658013752816573702601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166201754703340844196540269 62325658013752816573702601)
        ·
          refine ⟨46744243510314612430276951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62325658013752816573702601 46744243510314612430276951)
          ·
            refine ⟨70116365265471918645415427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46744243510314612430276951 70116365265471918645415427)
            ·
              refine ⟨105174547898207877968123141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70116365265471918645415427 105174547898207877968123141)
              ·
                refine ⟨19720227730913977119023089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105174547898207877968123141 19720227730913977119023089)
                ·
                  refine ⟨14790170798185482839267317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19720227730913977119023089 14790170798185482839267317)
                  ·
                    refine ⟨1386578512329889016181311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14790170798185482839267317 1386578512329889016181311)
                    ·
                      rfl

theorem cell22_4050528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_4050528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050528 prefixEnd_4050528 := by exact prefixLift 4050528
  have htrace : WordTrace (prefixWord ++ tailWord_4050528) baseStart_4050528 baseEnd_4050528 := by
    simpa [prefixWord, tailWord_4050528, baseEnd_4050528] using wordTrace_append hprefix tailTrace_4050528
  have hstable : (prefixWord ++ tailWord_4050528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050528).length < 2 ^ (prefixWord ++ tailWord_4050528).sum := by decide
  have hdescent : baseEnd_4050528 < baseStart_4050528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050560 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_4050560 : Nat := 118140960795 + 4050560 * 2 ^ 59
def prefixEnd_4050560 : Nat := 4983230072969 + 3 ^ 40 * 4050560 * 2
def baseEnd_4050560 : Nat := 1386589466583851599381213

theorem tailTrace_4050560 : CollatzResearch.WordTrace tailWord_4050560 prefixEnd_4050560 1386589466583851599381213 := by
  unfold tailWord_4050560
  simp only [CollatzResearch.WordTrace]
  refine ⟨73868030102760187708822567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98490706803680250278430089 73868030102760187708822567)
  ·
    refine ⟨110802045154140281563233851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73868030102760187708822567 110802045154140281563233851)
    ·
      refine ⟨166203067731210422344850777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110802045154140281563233851 166203067731210422344850777)
      ·
        refine ⟨124652300798407816758638083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166203067731210422344850777 124652300798407816758638083)
        ·
          refine ⟨186978451197611725137957125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124652300798407816758638083 186978451197611725137957125)
          ·
            refine ⟨35058459599552198463366961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186978451197611725137957125 35058459599552198463366961)
            ·
              refine ⟨26293844699664148847525221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35058459599552198463366961 26293844699664148847525221)
              ·
                refine ⟨4930095881187027908910979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26293844699664148847525221 4930095881187027908910979)
                ·
                  refine ⟨7395143821780541863366469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930095881187027908910979 7395143821780541863366469)
                  ·
                    refine ⟨1386589466583851599381213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395143821780541863366469 1386589466583851599381213)
                    ·
                      rfl

theorem cell22_4050560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_4050560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050560 prefixEnd_4050560 := by exact prefixLift 4050560
  have htrace : WordTrace (prefixWord ++ tailWord_4050560) baseStart_4050560 baseEnd_4050560 := by
    simpa [prefixWord, tailWord_4050560, baseEnd_4050560] using wordTrace_append hprefix tailTrace_4050560
  have hstable : (prefixWord ++ tailWord_4050560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050560).length < 2 ^ (prefixWord ++ tailWord_4050560).sum := by decide
  have hdescent : baseEnd_4050560 < baseStart_4050560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050592 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_4050592 : Nat := 118140960795 + 4050592 * 2 ^ 59
def prefixEnd_4050592 : Nat := 4983230072969 + 3 ^ 40 * 4050592 * 2
def baseEnd_4050592 : Nat := 462200140279271394193705

theorem tailTrace_4050592 : CollatzResearch.WordTrace tailWord_4050592 prefixEnd_4050592 462200140279271394193705 := by
  unfold tailWord_4050592
  simp only [CollatzResearch.WordTrace]
  refine ⟨73868613670702222441405015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98491484894269629921873353 73868613670702222441405015)
  ·
    refine ⟨110802920506053333662107523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73868613670702222441405015 110802920506053333662107523)
    ·
      refine ⟨166204380759080000493161285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110802920506053333662107523 166204380759080000493161285)
      ·
        refine ⟨31163321392327500092467741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166204380759080000493161285 31163321392327500092467741)
        ·
          refine ⟨11686245522122812534675403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31163321392327500092467741 11686245522122812534675403)
          ·
            refine ⟨17529368283184218802013105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11686245522122812534675403 17529368283184218802013105)
            ·
              refine ⟨13147026212388164101509829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17529368283184218802013105 13147026212388164101509829)
              ·
                refine ⟨2465067414822780769033093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13147026212388164101509829 2465067414822780769033093)
                ·
                  refine ⟨462200140279271394193705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465067414822780769033093 462200140279271394193705)
                  ·
                    rfl

theorem cell22_4050592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_4050592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050592 prefixEnd_4050592 := by exact prefixLift 4050592
  have htrace : WordTrace (prefixWord ++ tailWord_4050592) baseStart_4050592 baseEnd_4050592 := by
    simpa [prefixWord, tailWord_4050592, baseEnd_4050592] using wordTrace_append hprefix tailTrace_4050592
  have hstable : (prefixWord ++ tailWord_4050592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050592).length < 2 ^ (prefixWord ++ tailWord_4050592).sum := by decide
  have hdescent : baseEnd_4050592 < baseStart_4050592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050605 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4050605 : Nat := 118140960795 + 4050605 * 2 ^ 59
def prefixEnd_4050605 : Nat := 4983230072969 + 3 ^ 40 * 4050605 * 2
def baseEnd_4050605 : Nat := 1386604871003486482006075

theorem tailTrace_4050605 : CollatzResearch.WordTrace tailWord_4050605 prefixEnd_4050605 1386604871003486482006075 := by
  unfold tailWord_4050605
  simp only [CollatzResearch.WordTrace]
  refine ⟨147737701490357348103033269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98491800993571565402022179 147737701490357348103033269)
  ·
    refine ⟨13850409514721001384659369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147737701490357348103033269 13850409514721001384659369)
    ·
      refine ⟨10387807136040751038494527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13850409514721001384659369 10387807136040751038494527)
      ·
        refine ⟨15581710704061126557741791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387807136040751038494527 15581710704061126557741791)
        ·
          refine ⟨23372566056091689836612687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581710704061126557741791 23372566056091689836612687)
          ·
            refine ⟨35058849084137534754919031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372566056091689836612687 35058849084137534754919031)
            ·
              refine ⟨52588273626206302132378547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35058849084137534754919031 52588273626206302132378547)
              ·
                refine ⟨78882410439309453198567821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52588273626206302132378547 78882410439309453198567821)
                ·
                  refine ⟨29580903914741044949462933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78882410439309453198567821 29580903914741044949462933)
                  ·
                    refine ⟨1386604871003486482006075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29580903914741044949462933 1386604871003486482006075)
                    ·
                      rfl

theorem cell22_4050605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4050605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050605 prefixEnd_4050605 := by exact prefixLift 4050605
  have htrace : WordTrace (prefixWord ++ tailWord_4050605) baseStart_4050605 baseEnd_4050605 := by
    simpa [prefixWord, tailWord_4050605, baseEnd_4050605] using wordTrace_append hprefix tailTrace_4050605
  have hstable : (prefixWord ++ tailWord_4050605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050605).length < 2 ^ (prefixWord ++ tailWord_4050605).sum := by decide
  have hdescent : baseEnd_4050605 < baseStart_4050605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050620 : List Nat := [2, 2, 2, 3, 1, 3, 1, 8]
def baseStart_4050620 : Nat := 118140960795 + 4050620 * 2 ^ 59
def prefixEnd_4050620 : Nat := 4983230072969 + 3 ^ 40 * 4050620 * 2
def baseEnd_4050620 : Nat := 154067778423336826986781

theorem tailTrace_4050620 : CollatzResearch.WordTrace tailWord_4050620 prefixEnd_4050620 154067778423336826986781 := by
  unfold tailWord_4050620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73869124292651502832414657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98492165723535337109886209 73869124292651502832414657)
  ·
    refine ⟨55401843219488627124310993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73869124292651502832414657 55401843219488627124310993)
    ·
      refine ⟨41551382414616470343233245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55401843219488627124310993 41551382414616470343233245)
      ·
        refine ⟨15581768405481176378712467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41551382414616470343233245 15581768405481176378712467)
        ·
          refine ⟨23372652608221764568068701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581768405481176378712467 23372652608221764568068701)
          ·
            refine ⟨8764744728083161713025763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23372652608221764568068701 8764744728083161713025763)
            ·
              refine ⟨13147117092124742569538645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764744728083161713025763 13147117092124742569538645)
              ·
                refine ⟨154067778423336826986781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13147117092124742569538645 154067778423336826986781)
                ·
                  rfl

theorem cell22_4050620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_4050620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050620 prefixEnd_4050620 := by exact prefixLift 4050620
  have htrace : WordTrace (prefixWord ++ tailWord_4050620) baseStart_4050620 baseEnd_4050620 := by
    simpa [prefixWord, tailWord_4050620, baseEnd_4050620] using wordTrace_append hprefix tailTrace_4050620
  have hstable : (prefixWord ++ tailWord_4050620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050620).length < 2 ^ (prefixWord ++ tailWord_4050620).sum := by decide
  have hdescent : baseEnd_4050620 < baseStart_4050620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050635 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 5, 3]
def baseStart_4050635 : Nat := 118140960795 + 4050635 * 2 ^ 59
def prefixEnd_4050635 : Nat := 4983230072969 + 3 ^ 40 * 4050635 * 2
def baseEnd_4050635 : Nat := 1386615140616576403755983

theorem tailTrace_4050635 : CollatzResearch.WordTrace tailWord_4050635 prefixEnd_4050635 1386615140616576403755983 := by
  unfold tailWord_4050635
  simp only [CollatzResearch.WordTrace]
  refine ⟨147738795680248663226625359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98492530453499108817750239 147738795680248663226625359)
  ·
    refine ⟨221608193520372994839938039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147738795680248663226625359 221608193520372994839938039)
    ·
      refine ⟨332412290280559492259907059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221608193520372994839938039 332412290280559492259907059)
      ·
        refine ⟨498618435420839238389860589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332412290280559492259907059 498618435420839238389860589)
        ·
          refine ⟨186981913282814714396197721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498618435420839238389860589 186981913282814714396197721)
          ·
            refine ⟨140236434962111035797148291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186981913282814714396197721 140236434962111035797148291)
            ·
              refine ⟨210354652443166553695722437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140236434962111035797148291 210354652443166553695722437)
              ·
                refine ⟨39441497333093728817947957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210354652443166553695722437 39441497333093728817947957)
                ·
                  refine ⟨3697640374977537076682621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39441497333093728817947957 3697640374977537076682621)
                  ·
                    refine ⟨1386615140616576403755983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697640374977537076682621 1386615140616576403755983)
                    ·
                      rfl

theorem cell22_4050635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3].length) (baseStart_4050635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050635 prefixEnd_4050635 := by exact prefixLift 4050635
  have htrace : WordTrace (prefixWord ++ tailWord_4050635) baseStart_4050635 baseEnd_4050635 := by
    simpa [prefixWord, tailWord_4050635, baseEnd_4050635] using wordTrace_append hprefix tailTrace_4050635
  have hstable : (prefixWord ++ tailWord_4050635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050635).length < 2 ^ (prefixWord ++ tailWord_4050635).sum := by decide
  have hdescent : baseEnd_4050635 < baseStart_4050635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050637 : List Nat := [1, 6, 2, 1, 1, 1, 10]
def baseStart_4050637 : Nat := 118140960795 + 4050637 * 2 ^ 59
def prefixEnd_4050637 : Nat := 4983230072969 + 3 ^ 40 * 4050637 * 2
def baseEnd_4050637 : Nat := 51356141676201817229851

theorem tailTrace_4050637 : CollatzResearch.WordTrace tailWord_4050637 prefixEnd_4050637 51356141676201817229851 := by
  unfold tailWord_4050637
  simp only [CollatzResearch.WordTrace]
  refine ⟨147738868626241417568198165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98492579084160945045465443 147738868626241417568198165)
  ·
    refine ⟨6925259466855066448509289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147738868626241417568198165 6925259466855066448509289)
    ·
      refine ⟨5193944600141299836381967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6925259466855066448509289 5193944600141299836381967)
      ·
        refine ⟨7790916900211949754572951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193944600141299836381967 7790916900211949754572951)
        ·
          refine ⟨11686375350317924631859427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790916900211949754572951 11686375350317924631859427)
          ·
            refine ⟨17529563025476886947789141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11686375350317924631859427 17529563025476886947789141)
            ·
              refine ⟨51356141676201817229851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17529563025476886947789141 51356141676201817229851)
              ·
                rfl

theorem cell22_4050637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 10].length) (baseStart_4050637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050637 prefixEnd_4050637 := by exact prefixLift 4050637
  have htrace : WordTrace (prefixWord ++ tailWord_4050637) baseStart_4050637 baseEnd_4050637 := by
    simpa [prefixWord, tailWord_4050637, baseEnd_4050637] using wordTrace_append hprefix tailTrace_4050637
  have hstable : (prefixWord ++ tailWord_4050637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050637).length < 2 ^ (prefixWord ++ tailWord_4050637).sum := by decide
  have hdescent : baseEnd_4050637 < baseStart_4050637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050694 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4050694 : Nat := 118140960795 + 4050694 * 2 ^ 59
def prefixEnd_4050694 : Nat := 4983230072969 + 3 ^ 40 * 4050694 * 2
def baseEnd_4050694 : Nat := 462211779174106638843601

theorem tailTrace_4050694 : CollatzResearch.WordTrace tailWord_4050694 prefixEnd_4050694 462211779174106638843601 := by
  unfold tailWord_4050694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616904612094841134469473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98493965058023277535348757 4616904612094841134469473)
  ·
    refine ⟨3462678459071130850852105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4616904612094841134469473 3462678459071130850852105)
    ·
      refine ⟨2597008844303348138139079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3462678459071130850852105 2597008844303348138139079)
      ·
        refine ⟨3895513266455022207208619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597008844303348138139079 3895513266455022207208619)
        ·
          refine ⟨5843269899682533310812929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3895513266455022207208619 5843269899682533310812929)
          ·
            refine ⟨4382452424761899983109697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5843269899682533310812929 4382452424761899983109697)
            ·
              refine ⟨3286839318571424987332273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382452424761899983109697 3286839318571424987332273)
              ·
                refine ⟨2465129488928568740499205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286839318571424987332273 2465129488928568740499205)
                ·
                  refine ⟨462211779174106638843601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465129488928568740499205 462211779174106638843601)
                  ·
                    rfl

theorem cell22_4050694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4050694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050694 prefixEnd_4050694 := by exact prefixLift 4050694
  have htrace : WordTrace (prefixWord ++ tailWord_4050694) baseStart_4050694 baseEnd_4050694 := by
    simpa [prefixWord, tailWord_4050694, baseEnd_4050694] using wordTrace_append hprefix tailTrace_4050694
  have hstable : (prefixWord ++ tailWord_4050694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050694).length < 2 ^ (prefixWord ++ tailWord_4050694).sum := by decide
  have hdescent : baseEnd_4050694 < baseStart_4050694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050744 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_4050744 : Nat := 118140960795 + 4050744 * 2 ^ 59
def prefixEnd_4050744 : Nat := 4983230072969 + 3 ^ 40 * 4050744 * 2
def baseEnd_4050744 : Nat := 462217484514712150926883

theorem tailTrace_4050744 : CollatzResearch.WordTrace tailWord_4050744 prefixEnd_4050744 462217484514712150926883 := by
  unfold tailWord_4050744
  simp only [CollatzResearch.WordTrace]
  refine ⟨73871385618426887421171643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98495180824569183228228857 73871385618426887421171643)
  ·
    refine ⟨110807078427640331131757465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73871385618426887421171643 110807078427640331131757465)
    ·
      refine ⟨83105308820730248348818099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110807078427640331131757465 83105308820730248348818099)
      ·
        refine ⟨124657963231095372523227149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83105308820730248348818099 124657963231095372523227149)
        ·
          refine ⟨46746736211660764696210181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124657963231095372523227149 46746736211660764696210181)
          ·
            refine ⟨8765013039686393380539409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46746736211660764696210181 8765013039686393380539409)
            ·
              refine ⟨6573759779764795035404557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765013039686393380539409 6573759779764795035404557)
              ·
                refine ⟨2465159917411798138276709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6573759779764795035404557 2465159917411798138276709)
                ·
                  refine ⟨462217484514712150926883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465159917411798138276709 462217484514712150926883)
                  ·
                    rfl

theorem cell22_4050744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_4050744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050744 prefixEnd_4050744 := by exact prefixLift 4050744
  have htrace : WordTrace (prefixWord ++ tailWord_4050744) baseStart_4050744 baseEnd_4050744 := by
    simpa [prefixWord, tailWord_4050744, baseEnd_4050744] using wordTrace_append hprefix tailTrace_4050744
  have hstable : (prefixWord ++ tailWord_4050744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050744).length < 2 ^ (prefixWord ++ tailWord_4050744).sum := by decide
  have hdescent : baseEnd_4050744 < baseStart_4050744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050746 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 1, 4]
def baseStart_4050746 : Nat := 118140960795 + 4050746 * 2 ^ 59
def prefixEnd_4050746 : Nat := 4983230072969 + 3 ^ 40 * 4050746 * 2
def baseEnd_4050746 : Nat := 1386653138185009114230643

theorem tailTrace_4050746 : CollatzResearch.WordTrace tailWord_4050746 prefixEnd_4050746 1386653138185009114230643 := by
  unfold tailWord_4050746
  simp only [CollatzResearch.WordTrace]
  refine ⟨36935711045711632295979023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98495229455231019455944061 36935711045711632295979023)
  ·
    refine ⟨55403566568567448443968535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36935711045711632295979023 55403566568567448443968535)
    ·
      refine ⟨83105349852851172665952803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55403566568567448443968535 83105349852851172665952803)
      ·
        refine ⟨124658024779276758998929205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83105349852851172665952803 124658024779276758998929205)
        ·
          refine ⟨11686689823057196156149613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124658024779276758998929205 11686689823057196156149613)
          ·
            refine ⟨4382508683646448558556105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11686689823057196156149613 4382508683646448558556105)
            ·
              refine ⟨3286881512734836418917079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382508683646448558556105 3286881512734836418917079)
              ·
                refine ⟨4930322269102254628375619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286881512734836418917079 4930322269102254628375619)
                ·
                  refine ⟨7395483403653381942563429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930322269102254628375619 7395483403653381942563429)
                  ·
                    refine ⟨1386653138185009114230643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395483403653381942563429 1386653138185009114230643)
                    ·
                      rfl

theorem cell22_4050746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_4050746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050746 prefixEnd_4050746 := by exact prefixLift 4050746
  have htrace : WordTrace (prefixWord ++ tailWord_4050746) baseStart_4050746 baseEnd_4050746 := by
    simpa [prefixWord, tailWord_4050746, baseEnd_4050746] using wordTrace_append hprefix tailTrace_4050746
  have hstable : (prefixWord ++ tailWord_4050746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050746).length < 2 ^ (prefixWord ++ tailWord_4050746).sum := by decide
  have hdescent : baseEnd_4050746 < baseStart_4050746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050755 : List Nat := [1, 1, 1, 3, 1, 6, 9]
def baseStart_4050755 : Nat := 118140960795 + 4050755 * 2 ^ 59
def prefixEnd_4050755 : Nat := 4983230072969 + 3 ^ 40 * 4050755 * 2
def baseEnd_4050755 : Nat := 51357637743293929287245

theorem tailTrace_4050755 : CollatzResearch.WordTrace tailWord_4050755 prefixEnd_4050755 51357637743293929287245 := by
  unfold tailWord_4050755
  simp only [CollatzResearch.WordTrace]
  refine ⟨147743172439813923720993719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98495448293209282480662479 147743172439813923720993719)
  ·
    refine ⟨221614758659720885581490579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147743172439813923720993719 221614758659720885581490579)
    ·
      refine ⟨332422137989581328372235869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221614758659720885581490579 332422137989581328372235869)
      ·
        refine ⟨124658301746092998139588451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332422137989581328372235869 124658301746092998139588451)
        ·
          refine ⟨186987452619139497209382677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124658301746092998139588451 186987452619139497209382677)
          ·
            refine ⟨8765036841522163931689813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186987452619139497209382677 8765036841522163931689813)
            ·
              refine ⟨51357637743293929287245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8765036841522163931689813 51357637743293929287245)
              ·
                rfl

theorem cell22_4050755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 9].length) (baseStart_4050755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050755 prefixEnd_4050755 := by exact prefixLift 4050755
  have htrace : WordTrace (prefixWord ++ tailWord_4050755) baseStart_4050755 baseEnd_4050755 := by
    simpa [prefixWord, tailWord_4050755, baseEnd_4050755] using wordTrace_append hprefix tailTrace_4050755
  have hstable : (prefixWord ++ tailWord_4050755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050755).length < 2 ^ (prefixWord ++ tailWord_4050755).sum := by decide
  have hdescent : baseEnd_4050755 < baseStart_4050755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050759 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 2, 3]
def baseStart_4050759 : Nat := 118140960795 + 4050759 * 2 ^ 59
def prefixEnd_4050759 : Nat := 4983230072969 + 3 ^ 40 * 4050759 * 2
def baseEnd_4050759 : Nat := 1386657588350681413655603

theorem tailTrace_4050759 : CollatzResearch.WordTrace tailWord_4050759 prefixEnd_4050759 1386657588350681413655603 := by
  unfold tailWord_4050759
  simp only [CollatzResearch.WordTrace]
  refine ⟨147743318331799432404139331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98495545554532954936092887 147743318331799432404139331)
  ·
    refine ⟨221614977497699148606208997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147743318331799432404139331 221614977497699148606208997)
    ·
      refine ⟨41552808280818590363664187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221614977497699148606208997 41552808280818590363664187)
      ·
        refine ⟨62329212421227885545496281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41552808280818590363664187 62329212421227885545496281)
        ·
          refine ⟨46746909315920914159122211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62329212421227885545496281 46746909315920914159122211)
          ·
            refine ⟨70120363973881371238683317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46746909315920914159122211 70120363973881371238683317)
            ·
              refine ⟨6573784122551378553626561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70120363973881371238683317 6573784122551378553626561)
              ·
                refine ⟨4930338091913533915219921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573784122551378553626561 4930338091913533915219921)
                ·
                  refine ⟨3697753568935150436414941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930338091913533915219921 3697753568935150436414941)
                  ·
                    refine ⟨1386657588350681413655603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697753568935150436414941 1386657588350681413655603)
                    ·
                      rfl

theorem cell22_4050759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_4050759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050759 prefixEnd_4050759 := by exact prefixLift 4050759
  have htrace : WordTrace (prefixWord ++ tailWord_4050759) baseStart_4050759 baseEnd_4050759 := by
    simpa [prefixWord, tailWord_4050759, baseEnd_4050759] using wordTrace_append hprefix tailTrace_4050759
  have hstable : (prefixWord ++ tailWord_4050759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050759).length < 2 ^ (prefixWord ++ tailWord_4050759).sum := by decide
  have hdescent : baseEnd_4050759 < baseStart_4050759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050806 : List Nat := [5, 1, 1, 3, 3, 1, 8]
def baseStart_4050806 : Nat := 118140960795 + 4050806 * 2 ^ 59
def prefixEnd_4050806 : Nat := 4983230072969 + 3 ^ 40 * 4050806 * 2
def baseEnd_4050806 : Nat := 51358284348562553990017

theorem tailTrace_4050806 : CollatzResearch.WordTrace tailWord_4050806 prefixEnd_4050806 51358284348562553990017 := by
  unfold tailWord_4050806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234064535164322464443767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98496688375086106287400181 9234064535164322464443767)
  ·
    refine ⟨13851096802746483696665651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234064535164322464443767 13851096802746483696665651)
    ·
      refine ⟨20776645204119725544998477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851096802746483696665651 20776645204119725544998477)
      ·
        refine ⟨7791241951544897079374429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20776645204119725544998477 7791241951544897079374429)
        ·
          refine ⟨2921715731829336404765411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7791241951544897079374429 2921715731829336404765411)
          ·
            refine ⟨4382573597744004607148117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921715731829336404765411 4382573597744004607148117)
            ·
              refine ⟨51358284348562553990017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4382573597744004607148117 51358284348562553990017)
              ·
                rfl

theorem cell22_4050806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 8].length) (baseStart_4050806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050806 prefixEnd_4050806 := by exact prefixLift 4050806
  have htrace : WordTrace (prefixWord ++ tailWord_4050806) baseStart_4050806 baseEnd_4050806 := by
    simpa [prefixWord, tailWord_4050806, baseEnd_4050806] using wordTrace_append hprefix tailTrace_4050806
  have hstable : (prefixWord ++ tailWord_4050806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050806).length < 2 ^ (prefixWord ++ tailWord_4050806).sum := by decide
  have hdescent : baseEnd_4050806 < baseStart_4050806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050868 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4050868 : Nat := 118140960795 + 4050868 * 2 ^ 59
def prefixEnd_4050868 : Nat := 4983230072969 + 3 ^ 40 * 4050868 * 2
def baseEnd_4050868 : Nat := 462231633759413820893423

theorem tailTrace_4050868 : CollatzResearch.WordTrace tailWord_4050868 prefixEnd_4050868 462231633759413820893423 := by
  unfold tailWord_4050868
  simp only [CollatzResearch.WordTrace]
  refine ⟨73873646944202272009928629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98498195925603029346571505 73873646944202272009928629)
  ·
    refine ⟨6925654401018963000930809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73873646944202272009928629 6925654401018963000930809)
    ·
      refine ⟨5194240800764222250698107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6925654401018963000930809 5194240800764222250698107)
      ·
        refine ⟨7791361201146333376047161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194240800764222250698107 7791361201146333376047161)
        ·
          refine ⟨5843520900859750032035371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7791361201146333376047161 5843520900859750032035371)
          ·
            refine ⟨8765281351289625048053057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843520900859750032035371 8765281351289625048053057)
            ·
              refine ⟨6573961013467218786039793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765281351289625048053057 6573961013467218786039793)
              ·
                refine ⟨4930470760100414089529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573961013467218786039793 4930470760100414089529845)
                ·
                  refine ⟨462231633759413820893423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4930470760100414089529845 462231633759413820893423)
                  ·
                    rfl

theorem cell22_4050868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4050868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050868 prefixEnd_4050868 := by exact prefixLift 4050868
  have htrace : WordTrace (prefixWord ++ tailWord_4050868) baseStart_4050868 baseEnd_4050868 := by
    simpa [prefixWord, tailWord_4050868, baseEnd_4050868] using wordTrace_append hprefix tailTrace_4050868
  have hstable : (prefixWord ++ tailWord_4050868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050868).length < 2 ^ (prefixWord ++ tailWord_4050868).sum := by decide
  have hdescent : baseEnd_4050868 < baseStart_4050868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050879 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 4]
def baseStart_4050879 : Nat := 118140960795 + 4050879 * 2 ^ 59
def prefixEnd_4050879 : Nat := 4983230072969 + 3 ^ 40 * 4050879 * 2
def baseEnd_4050879 : Nat := 462232888934347033551745

theorem tailTrace_4050879 : CollatzResearch.WordTrace tailWord_4050879 prefixEnd_4050879 462232888934347033551745 := by
  unfold tailWord_4050879
  simp only [CollatzResearch.WordTrace]
  refine ⟨147747695091364692898507691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98498463394243128599005127 147747695091364692898507691)
  ·
    refine ⟨221621542637047039347761537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147747695091364692898507691 221621542637047039347761537)
    ·
      refine ⟨166216156977785279510821153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221621542637047039347761537 166216156977785279510821153)
      ·
        refine ⟨124662117733338959633115865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166216156977785279510821153 124662117733338959633115865)
        ·
          refine ⟨93496588300004219724836899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124662117733338959633115865 93496588300004219724836899)
          ·
            refine ⟨140244882450006329587255349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93496588300004219724836899 140244882450006329587255349)
            ·
              refine ⟨13147957729688093398805189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140244882450006329587255349 13147957729688093398805189)
              ·
                refine ⟨2465242074316517512275973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13147957729688093398805189 2465242074316517512275973)
                ·
                  refine ⟨462232888934347033551745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465242074316517512275973 462232888934347033551745)
                  ·
                    rfl

theorem cell22_4050879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 4].length) (baseStart_4050879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050879 prefixEnd_4050879 := by exact prefixLift 4050879
  have htrace : WordTrace (prefixWord ++ tailWord_4050879) baseStart_4050879 baseEnd_4050879 := by
    simpa [prefixWord, tailWord_4050879, baseEnd_4050879] using wordTrace_append hprefix tailTrace_4050879
  have hstable : (prefixWord ++ tailWord_4050879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050879).length < 2 ^ (prefixWord ++ tailWord_4050879).sum := by decide
  have hdescent : baseEnd_4050879 < baseStart_4050879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050894 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_4050894 : Nat := 118140960795 + 4050894 * 2 ^ 59
def prefixEnd_4050894 : Nat := 4983230072969 + 3 ^ 40 * 4050894 * 2
def baseEnd_4050894 : Nat := 1386703801609586061530189

theorem tailTrace_4050894 : CollatzResearch.WordTrace tailWord_4050894 prefixEnd_4050894 1386703801609586061530189 := by
  unfold tailWord_4050894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468530273288793807537967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98498828124206900306869157 18468530273288793807537967)
  ·
    refine ⟨27702795409933190711306951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18468530273288793807537967 27702795409933190711306951)
    ·
      refine ⟨41554193114899786066960427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27702795409933190711306951 41554193114899786066960427)
      ·
        refine ⟨62331289672349679100440641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41554193114899786066960427 62331289672349679100440641)
        ·
          refine ⟨46748467254262259325330481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62331289672349679100440641 46748467254262259325330481)
          ·
            refine ⟨35061350440696694493997861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46748467254262259325330481 35061350440696694493997861)
            ·
              refine ⟨6574003207630630217624599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35061350440696694493997861 6574003207630630217624599)
              ·
                refine ⟨9861004811445945326436899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574003207630630217624599 9861004811445945326436899)
                ·
                  refine ⟨14791507217168917989655349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861004811445945326436899 14791507217168917989655349)
                  ·
                    refine ⟨1386703801609586061530189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14791507217168917989655349 1386703801609586061530189)
                    ·
                      rfl

theorem cell22_4050894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_4050894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050894 prefixEnd_4050894 := by exact prefixLift 4050894
  have htrace : WordTrace (prefixWord ++ tailWord_4050894) baseStart_4050894 baseEnd_4050894 := by
    simpa [prefixWord, tailWord_4050894, baseEnd_4050894] using wordTrace_append hprefix tailTrace_4050894
  have hstable : (prefixWord ++ tailWord_4050894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050894).length < 2 ^ (prefixWord ++ tailWord_4050894).sum := by decide
  have hdescent : baseEnd_4050894 < baseStart_4050894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4050939 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 3, 3]
def baseStart_4050939 : Nat := 118140960795 + 4050939 * 2 ^ 59
def prefixEnd_4050939 : Nat := 4983230072969 + 3 ^ 40 * 4050939 * 2
def baseEnd_4050939 : Nat := 1386719206029220944155051

theorem tailTrace_4050939 : CollatzResearch.WordTrace tailWord_4050939 prefixEnd_4050939 1386719206029220944155051 := by
  unfold tailWord_4050939
  simp only [CollatzResearch.WordTrace]
  refine ⟨147749883471147323145691871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98499922314098215430461247 147749883471147323145691871)
  ·
    refine ⟨221624825206720984718537807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147749883471147323145691871 221624825206720984718537807)
    ·
      refine ⟨332437237810081477077806711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221624825206720984718537807 332437237810081477077806711)
      ·
        refine ⟨498655856715122215616710067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332437237810081477077806711 498655856715122215616710067)
        ·
          refine ⟨747983785072683323425065101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498655856715122215616710067 747983785072683323425065101)
          ·
            refine ⟨280493919402256246284399413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 747983785072683323425065101 280493919402256246284399413)
            ·
              refine ⟨26296304943961523089162445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280493919402256246284399413 26296304943961523089162445)
              ·
                refine ⟨9861114353985571158435917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26296304943961523089162445 9861114353985571158435917)
                ·
                  refine ⟨3697917882744589184413469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9861114353985571158435917 3697917882744589184413469)
                  ·
                    refine ⟨1386719206029220944155051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697917882744589184413469 1386719206029220944155051)
                    ·
                      rfl

theorem cell22_4050939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3].length) (baseStart_4050939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4050939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4050939 prefixEnd_4050939 := by exact prefixLift 4050939
  have htrace : WordTrace (prefixWord ++ tailWord_4050939) baseStart_4050939 baseEnd_4050939 := by
    simpa [prefixWord, tailWord_4050939, baseEnd_4050939] using wordTrace_append hprefix tailTrace_4050939
  have hstable : (prefixWord ++ tailWord_4050939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4050939).length < 2 ^ (prefixWord ++ tailWord_4050939).sum := by decide
  have hdescent : baseEnd_4050939 < baseStart_4050939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4050939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051029 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_4051029 : Nat := 118140960795 + 4051029 * 2 ^ 59
def prefixEnd_4051029 : Nat := 4983230072969 + 3 ^ 40 * 4051029 * 2
def baseEnd_4051029 : Nat := 1386750014868490709404775

theorem tailTrace_4051029 : CollatzResearch.WordTrace tailWord_4051029 prefixEnd_4051029 1386750014868490709404775 := by
  unfold tailWord_4051029
  simp only [CollatzResearch.WordTrace]
  refine ⟨147753166040821268516468141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98502110693880845677645427 147753166040821268516468141)
  ·
    refine ⟨55407437265307975693675553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147753166040821268516468141 55407437265307975693675553)
    ·
      refine ⟨41555577948980981770256665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55407437265307975693675553 41555577948980981770256665)
      ·
        refine ⟨31166683461735736327692499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41555577948980981770256665 31166683461735736327692499)
        ·
          refine ⟨46750025192603604491538749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31166683461735736327692499 46750025192603604491538749)
          ·
            refine ⟨17531259447226351684327031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46750025192603604491538749 17531259447226351684327031)
            ·
              refine ⟨26296889170839527526490547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17531259447226351684327031 26296889170839527526490547)
              ·
                refine ⟨39445333756259291289735821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26296889170839527526490547 39445333756259291289735821)
                ·
                  refine ⟨14792000158597234233650933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39445333756259291289735821 14792000158597234233650933)
                  ·
                    refine ⟨1386750014868490709404775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14792000158597234233650933 1386750014868490709404775)
                    ·
                      rfl

theorem cell22_4051029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_4051029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051029 prefixEnd_4051029 := by exact prefixLift 4051029
  have htrace : WordTrace (prefixWord ++ tailWord_4051029) baseStart_4051029 baseEnd_4051029 := by
    simpa [prefixWord, tailWord_4051029, baseEnd_4051029] using wordTrace_append hprefix tailTrace_4051029
  have hstable : (prefixWord ++ tailWord_4051029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051029).length < 2 ^ (prefixWord ++ tailWord_4051029).sum := by decide
  have hdescent : baseEnd_4051029 < baseStart_4051029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051076 : List Nat := [2, 3, 2, 1, 2, 1, 5, 6]
def baseStart_4051076 : Nat := 118140960795 + 4051076 * 2 ^ 59
def prefixEnd_4051076 : Nat := 4983230072969 + 3 ^ 40 * 4051076 * 2
def baseEnd_4051076 : Nat := 154085122658777583719959

theorem tailTrace_4051076 : CollatzResearch.WordTrace tailWord_4051076 prefixEnd_4051076 154085122658777583719959 := by
  unfold tailWord_4051076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73877440135825497771714541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98503253514433997028952721 73877440135825497771714541)
  ·
    refine ⟨27704040050934561664392953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73877440135825497771714541 27704040050934561664392953)
    ·
      refine ⟨20778030038200921248294715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27704040050934561664392953 20778030038200921248294715)
      ·
        refine ⟨31167045057301381872442073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20778030038200921248294715 31167045057301381872442073)
        ·
          refine ⟨23375283792976036404331555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31167045057301381872442073 23375283792976036404331555)
          ·
            refine ⟨35062925689464054606497333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23375283792976036404331555 35062925689464054606497333)
            ·
              refine ⟨3287149283387255119359125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35062925689464054606497333 3287149283387255119359125)
              ·
                refine ⟨154085122658777583719959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3287149283387255119359125 154085122658777583719959)
                ·
                  rfl

theorem cell22_4051076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_4051076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051076 prefixEnd_4051076 := by exact prefixLift 4051076
  have htrace : WordTrace (prefixWord ++ tailWord_4051076) baseStart_4051076 baseEnd_4051076 := by
    simpa [prefixWord, tailWord_4051076, baseEnd_4051076] using wordTrace_append hprefix tailTrace_4051076
  have hstable : (prefixWord ++ tailWord_4051076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051076).length < 2 ^ (prefixWord ++ tailWord_4051076).sum := by decide
  have hdescent : baseEnd_4051076 < baseStart_4051076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051151 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 1, 4]
def baseStart_4051151 : Nat := 118140960795 + 4051151 * 2 ^ 59
def prefixEnd_4051151 : Nat := 4983230072969 + 3 ^ 40 * 4051151 * 2
def baseEnd_4051151 : Nat := 1386791777961723057854401

theorem tailTrace_4051151 : CollatzResearch.WordTrace tailWord_4051151 prefixEnd_4051151 1386791777961723057854401 := by
  unfold tailWord_4051151
  simp only [CollatzResearch.WordTrace]
  refine ⟨147757615746379283352409307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98505077164252855568272871 147757615746379283352409307)
  ·
    refine ⟨221636423619568925028613961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147757615746379283352409307 221636423619568925028613961)
    ·
      refine ⟨166227317714676693771460471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221636423619568925028613961 166227317714676693771460471)
      ·
        refine ⟨249340976572015040657190707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166227317714676693771460471 249340976572015040657190707)
        ·
          refine ⟨374011464858022560985786061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249340976572015040657190707 374011464858022560985786061)
          ·
            refine ⟨140254299321758460369669773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374011464858022560985786061 140254299321758460369669773)
            ·
              refine ⟨52595362245659422638626165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140254299321758460369669773 52595362245659422638626165)
              ·
                refine ⟨4930815210530570872371203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52595362245659422638626165 4930815210530570872371203)
                ·
                  refine ⟨7396222815795856308556805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930815210530570872371203 7396222815795856308556805)
                  ·
                    refine ⟨1386791777961723057854401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396222815795856308556805 1386791777961723057854401)
                    ·
                      rfl

theorem cell22_4051151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_4051151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051151 prefixEnd_4051151 := by exact prefixLift 4051151
  have htrace : WordTrace (prefixWord ++ tailWord_4051151) baseStart_4051151 baseEnd_4051151 := by
    simpa [prefixWord, tailWord_4051151, baseEnd_4051151] using wordTrace_append hprefix tailTrace_4051151
  have hstable : (prefixWord ++ tailWord_4051151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051151).length < 2 ^ (prefixWord ++ tailWord_4051151).sum := by decide
  have hdescent : baseEnd_4051151 < baseStart_4051151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051198 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_4051198 : Nat := 118140960795 + 4051198 * 2 ^ 59
def prefixEnd_4051198 : Nat := 4983230072969 + 3 ^ 40 * 4051198 * 2
def baseEnd_4051198 : Nat := 1386807867022230601929257

theorem tailTrace_4051198 : CollatzResearch.WordTrace tailWord_4051198 prefixEnd_4051198 1386807867022230601929257 := by
  unfold tailWord_4051198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18469916247151126297421281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98506219984806006919580165 18469916247151126297421281)
  ·
    refine ⟨13852437185363344723065961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18469916247151126297421281 13852437185363344723065961)
    ·
      refine ⟨10389327889022508542299471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13852437185363344723065961 10389327889022508542299471)
      ·
        refine ⟨15583991833533762813449207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389327889022508542299471 15583991833533762813449207)
        ·
          refine ⟨23375987750300644220173811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15583991833533762813449207 23375987750300644220173811)
          ·
            refine ⟨35063981625450966330260717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23375987750300644220173811 35063981625450966330260717)
            ·
              refine ⟨13148993109544112373847769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35063981625450966330260717 13148993109544112373847769)
              ·
                refine ⟨9861744832158084280385827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13148993109544112373847769 9861744832158084280385827)
                ·
                  refine ⟨14792617248237126420578741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861744832158084280385827 14792617248237126420578741)
                  ·
                    refine ⟨1386807867022230601929257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14792617248237126420578741 1386807867022230601929257)
                    ·
                      rfl

theorem cell22_4051198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_4051198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051198 prefixEnd_4051198 := by exact prefixLift 4051198
  have htrace : WordTrace (prefixWord ++ tailWord_4051198) baseStart_4051198 baseEnd_4051198 := by
    simpa [prefixWord, tailWord_4051198, baseEnd_4051198] using wordTrace_append hprefix tailTrace_4051198
  have hstable : (prefixWord ++ tailWord_4051198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051198).length < 2 ^ (prefixWord ++ tailWord_4051198).sum := by decide
  have hdescent : baseEnd_4051198 < baseStart_4051198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051202 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_4051202 : Nat := 118140960795 + 4051202 * 2 ^ 59
def prefixEnd_4051202 : Nat := 4983230072969 + 3 ^ 40 * 4051202 * 2
def baseEnd_4051202 : Nat := 1386809236303975924829245

theorem tailTrace_4051202 : CollatzResearch.WordTrace tailWord_4051202 prefixEnd_4051202 1386809236303975924829245 := by
  unfold tailWord_4051202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939868967298629765628965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98506317246129679375010573 36939868967298629765628965)
  ·
    refine ⟨6926225431368493081055431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36939868967298629765628965 6926225431368493081055431)
    ·
      refine ⟨10389338147052739621583147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926225431368493081055431 10389338147052739621583147)
      ·
        refine ⟨15584007220579109432374721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389338147052739621583147 15584007220579109432374721)
        ·
          refine ⟨11688005415434332074281041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15584007220579109432374721 11688005415434332074281041)
          ·
            refine ⟨8766004061575749055710781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11688005415434332074281041 8766004061575749055710781)
            ·
              refine ⟨3287251523090905895891543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8766004061575749055710781 3287251523090905895891543)
              ·
                refine ⟨4930877284636358843837315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287251523090905895891543 4930877284636358843837315)
                ·
                  refine ⟨7396315926954538265755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930877284636358843837315 7396315926954538265755973)
                  ·
                    refine ⟨1386809236303975924829245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396315926954538265755973 1386809236303975924829245)
                    ·
                      rfl

theorem cell22_4051202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_4051202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051202 prefixEnd_4051202 := by exact prefixLift 4051202
  have htrace : WordTrace (prefixWord ++ tailWord_4051202) baseStart_4051202 baseEnd_4051202 := by
    simpa [prefixWord, tailWord_4051202, baseEnd_4051202] using wordTrace_append hprefix tailTrace_4051202
  have hstable : (prefixWord ++ tailWord_4051202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051202).length < 2 ^ (prefixWord ++ tailWord_4051202).sum := by decide
  have hdescent : baseEnd_4051202 < baseStart_4051202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051271 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_4051271 : Nat := 118140960795 + 4051271 * 2 ^ 59
def prefixEnd_4051271 : Nat := 4983230072969 + 3 ^ 40 * 4051271 * 2
def baseEnd_4051271 : Nat := 1386832856414082744854033

theorem tailTrace_4051271 : CollatzResearch.WordTrace tailWord_4051271 prefixEnd_4051271 1386832856414082744854033 := by
  unfold tailWord_4051271
  simp only [CollatzResearch.WordTrace]
  refine ⟨147761992505944543846777667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98507995003963029231185111 147761992505944543846777667)
  ·
    refine ⟨221642988758916815770166501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147761992505944543846777667 221642988758916815770166501)
    ·
      refine ⟨41558060392296902956906219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221642988758916815770166501 41558060392296902956906219)
      ·
        refine ⟨62337090588445354435359329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41558060392296902956906219 62337090588445354435359329)
        ·
          refine ⟨46752817941334015826519497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62337090588445354435359329 46752817941334015826519497)
          ·
            refine ⟨35064613456000511869889623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46752817941334015826519497 35064613456000511869889623)
            ·
              refine ⟨52596920184000767804834435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35064613456000511869889623 52596920184000767804834435)
              ·
                refine ⟨78895380276001151707251653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52596920184000767804834435 78895380276001151707251653)
                ·
                  refine ⟨14792883801750215945109685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78895380276001151707251653 14792883801750215945109685)
                  ·
                    refine ⟨1386832856414082744854033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14792883801750215945109685 1386832856414082744854033)
                    ·
                      rfl

theorem cell22_4051271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4051271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051271 prefixEnd_4051271 := by exact prefixLift 4051271
  have htrace : WordTrace (prefixWord ++ tailWord_4051271) baseStart_4051271 baseEnd_4051271 := by
    simpa [prefixWord, tailWord_4051271, baseEnd_4051271] using wordTrace_append hprefix tailTrace_4051271
  have hstable : (prefixWord ++ tailWord_4051271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051271).length < 2 ^ (prefixWord ++ tailWord_4051271).sum := by decide
  have hdescent : baseEnd_4051271 < baseStart_4051271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051380 : List Nat := [2, 5, 2, 2, 11]
def baseStart_4051380 : Nat := 118140960795 + 4051380 * 2 ^ 59
def prefixEnd_4051380 : Nat := 4983230072969 + 3 ^ 40 * 4051380 * 2
def baseEnd_4051380 : Nat := 5707284647496472402793

theorem tailTrace_4051380 : CollatzResearch.WordTrace tailWord_4051380 prefixEnd_4051380 5707284647496472402793 := by
  unfold tailWord_4051380
  simp only [CollatzResearch.WordTrace]
  refine ⟨73882984031274827731247797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98510645375033103641663729 73882984031274827731247797)
  ·
    refine ⟨6926529752932015099804481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73882984031274827731247797 6926529752932015099804481)
    ·
      refine ⟨5194897314699011324853361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6926529752932015099804481 5194897314699011324853361)
      ·
        refine ⟨3896172986024258493640021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5194897314699011324853361 3896172986024258493640021)
        ·
          refine ⟨5707284647496472402793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3896172986024258493640021 5707284647496472402793)
          ·
            rfl

theorem cell22_4051380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 11].length) (baseStart_4051380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051380 prefixEnd_4051380 := by exact prefixLift 4051380
  have htrace : WordTrace (prefixWord ++ tailWord_4051380) baseStart_4051380 baseEnd_4051380 := by
    simpa [prefixWord, tailWord_4051380, baseEnd_4051380] using wordTrace_append hprefix tailTrace_4051380
  have hstable : (prefixWord ++ tailWord_4051380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051380).length < 2 ^ (prefixWord ++ tailWord_4051380).sum := by decide
  have hdescent : baseEnd_4051380 < baseStart_4051380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051412 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4051412 : Nat := 118140960795 + 4051412 * 2 ^ 59
def prefixEnd_4051412 : Nat := 4983230072969 + 3 ^ 40 * 4051412 * 2
def baseEnd_4051412 : Nat := 1386881123595605377078601

theorem tailTrace_4051412 : CollatzResearch.WordTrace tailWord_4051412 prefixEnd_4051412 1386881123595605377078601 := by
  unfold tailWord_4051412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73883567599216862463830245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98511423465622483285106993 73883567599216862463830245)
  ·
    refine ⟨13853168924853161711968171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73883567599216862463830245 13853168924853161711968171)
    ·
      refine ⟨20779753387279742567952257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13853168924853161711968171 20779753387279742567952257)
      ·
        refine ⟨15584815040459806925964193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20779753387279742567952257 15584815040459806925964193)
        ·
          refine ⟨11688611280344855194473145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15584815040459806925964193 11688611280344855194473145)
          ·
            refine ⟨8766458460258641395854859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11688611280344855194473145 8766458460258641395854859)
            ·
              refine ⟨13149687690387962093782289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766458460258641395854859 13149687690387962093782289)
              ·
                refine ⟨9862265767790971570336717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13149687690387962093782289 9862265767790971570336717)
                ·
                  refine ⟨3698349662921614338876269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9862265767790971570336717 3698349662921614338876269)
                  ·
                    refine ⟨1386881123595605377078601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698349662921614338876269 1386881123595605377078601)
                    ·
                      rfl

theorem cell22_4051412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4051412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051412 prefixEnd_4051412 := by exact prefixLift 4051412
  have htrace : WordTrace (prefixWord ++ tailWord_4051412) baseStart_4051412 baseEnd_4051412 := by
    simpa [prefixWord, tailWord_4051412, baseEnd_4051412] using wordTrace_append hprefix tailTrace_4051412
  have hstable : (prefixWord ++ tailWord_4051412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051412).length < 2 ^ (prefixWord ++ tailWord_4051412).sum := by decide
  have hdescent : baseEnd_4051412 < baseStart_4051412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051470 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_4051470 : Nat := 118140960795 + 4051470 * 2 ^ 59
def prefixEnd_4051470 : Nat := 4983230072969 + 3 ^ 40 * 4051470 * 2
def baseEnd_4051470 : Nat := 462300326060304186376141

theorem tailTrace_4051470 : CollatzResearch.WordTrace tailWord_4051470 prefixEnd_4051470 462300326060304186376141 := by
  unfold tailWord_4051470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18471156329027950104158983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98512833754815733888847909 18471156329027950104158983)
  ·
    refine ⟨27706734493541925156238475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18471156329027950104158983 27706734493541925156238475)
    ·
      refine ⟨41560101740312887734357713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27706734493541925156238475 41560101740312887734357713)
      ·
        refine ⟨31170076305234665800768285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41560101740312887734357713 31170076305234665800768285)
        ·
          refine ⟨11688778614462999675288107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31170076305234665800768285 11688778614462999675288107)
          ·
            refine ⟨17533167921694499512932161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688778614462999675288107 17533167921694499512932161)
            ·
              refine ⟨13149875941270874634699121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17533167921694499512932161 13149875941270874634699121)
              ·
                refine ⟨9862406955953155976024341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13149875941270874634699121 9862406955953155976024341)
                ·
                  refine ⟨462300326060304186376141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9862406955953155976024341 462300326060304186376141)
                  ·
                    rfl

theorem cell22_4051470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_4051470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051470 prefixEnd_4051470 := by exact prefixLift 4051470
  have htrace : WordTrace (prefixWord ++ tailWord_4051470) baseStart_4051470 baseEnd_4051470 := by
    simpa [prefixWord, tailWord_4051470, baseEnd_4051470] using wordTrace_append hprefix tailTrace_4051470
  have hstable : (prefixWord ++ tailWord_4051470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051470).length < 2 ^ (prefixWord ++ tailWord_4051470).sum := by decide
  have hdescent : baseEnd_4051470 < baseStart_4051470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051483 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_4051483 : Nat := 118140960795 + 4051483 * 2 ^ 59
def prefixEnd_4051483 : Nat := 4983230072969 + 3 ^ 40 * 4051483 * 2
def baseEnd_4051483 : Nat := 1386905428346584858553383

theorem tailTrace_4051483 : CollatzResearch.WordTrace tailWord_4051483 prefixEnd_4051483 1386905428346584858553383 := by
  unfold tailWord_4051483
  simp only [CollatzResearch.WordTrace]
  refine ⟨147769724781176504053495103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98513149854117669368996735 147769724781176504053495103)
  ·
    refine ⟨221654587171764756080242655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147769724781176504053495103 221654587171764756080242655)
    ·
      refine ⟨332481880757647134120363983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221654587171764756080242655 332481880757647134120363983)
      ·
        refine ⟨498722821136470701180545975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332481880757647134120363983 498722821136470701180545975)
        ·
          refine ⟨748084231704706051770818963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498722821136470701180545975 748084231704706051770818963)
          ·
            refine ⟨1122126347557059077656228445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748084231704706051770818963 1122126347557059077656228445)
            ·
              refine ⟨420797380333897154121085667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122126347557059077656228445 420797380333897154121085667)
              ·
                refine ⟨631196070500845731181628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420797380333897154121085667 631196070500845731181628501)
                ·
                  refine ⟨7396828951181785912284709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 631196070500845731181628501 7396828951181785912284709)
                  ·
                    refine ⟨1386905428346584858553383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396828951181785912284709 1386905428346584858553383)
                    ·
                      rfl

theorem cell22_4051483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_4051483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051483 prefixEnd_4051483 := by exact prefixLift 4051483
  have htrace : WordTrace (prefixWord ++ tailWord_4051483) baseStart_4051483 baseEnd_4051483 := by
    simpa [prefixWord, tailWord_4051483, baseEnd_4051483] using wordTrace_append hprefix tailTrace_4051483
  have hstable : (prefixWord ++ tailWord_4051483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051483).length < 2 ^ (prefixWord ++ tailWord_4051483).sum := by decide
  have hdescent : baseEnd_4051483 < baseStart_4051483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051607 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 1, 4]
def baseStart_4051607 : Nat := 118140960795 + 4051607 * 2 ^ 59
def prefixEnd_4051607 : Nat := 4983230072969 + 3 ^ 40 * 4051607 * 2
def baseEnd_4051607 : Nat := 1386947876080689868453003

theorem tailTrace_4051607 : CollatzResearch.WordTrace tailWord_4051607 prefixEnd_4051607 1386947876080689868453003 := by
  unfold tailWord_4051607
  simp only [CollatzResearch.WordTrace]
  refine ⟨147774247432727273231009075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98516164955151515487339383 147774247432727273231009075)
  ·
    refine ⟨221661371149090909846513613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147774247432727273231009075 221661371149090909846513613)
    ·
      refine ⟨83123014180909091192442605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221661371149090909846513613 83123014180909091192442605)
      ·
        refine ⟨31171130317840909197165977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83123014180909091192442605 31171130317840909197165977)
        ·
          refine ⟨23378347738380681897874483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31171130317840909197165977 23378347738380681897874483)
          ·
            refine ⟨35067521607571022846811725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23378347738380681897874483 35067521607571022846811725)
            ·
              refine ⟨13150320602839133567554397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35067521607571022846811725 13150320602839133567554397)
              ·
                refine ⟨4931370226064675087832899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13150320602839133567554397 4931370226064675087832899)
                ·
                  refine ⟨7397055339097012631749349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931370226064675087832899 7397055339097012631749349)
                  ·
                    refine ⟨1386947876080689868453003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397055339097012631749349 1386947876080689868453003)
                    ·
                      rfl

theorem cell22_4051607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_4051607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051607 prefixEnd_4051607 := by exact prefixLift 4051607
  have htrace : WordTrace (prefixWord ++ tailWord_4051607) baseStart_4051607 baseEnd_4051607 := by
    simpa [prefixWord, tailWord_4051607, baseEnd_4051607] using wordTrace_append hprefix tailTrace_4051607
  have hstable : (prefixWord ++ tailWord_4051607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051607).length < 2 ^ (prefixWord ++ tailWord_4051607).sum := by decide
  have hdescent : baseEnd_4051607 < baseStart_4051607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051635 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_4051635 : Nat := 118140960795 + 4051635 * 2 ^ 59
def prefixEnd_4051635 : Nat := 4983230072969 + 3 ^ 40 * 4051635 * 2
def baseEnd_4051635 : Nat := 1386957461052907128752917

theorem tailTrace_4051635 : CollatzResearch.WordTrace tailWord_4051635 prefixEnd_4051635 1386957461052907128752917 := by
  unfold tailWord_4051635
  simp only [CollatzResearch.WordTrace]
  refine ⟨147775268676625834013028359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98516845784417222675352239 147775268676625834013028359)
  ·
    refine ⟨221662903014938751019542539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147775268676625834013028359 221662903014938751019542539)
    ·
      refine ⟨332494354522408126529313809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221662903014938751019542539 332494354522408126529313809)
      ·
        refine ⟨249370765891806094896985357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332494354522408126529313809 249370765891806094896985357)
        ·
          refine ⟨93514037209427285586369509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249370765891806094896985357 93514037209427285586369509)
          ·
            refine ⟨17533881976767616047444283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93514037209427285586369509 17533881976767616047444283)
            ·
              refine ⟨26300822965151424071166425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17533881976767616047444283 26300822965151424071166425)
              ·
                refine ⟨19725617223863568053374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26300822965151424071166425 19725617223863568053374819)
                ·
                  refine ⟨29588425835795352080062229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19725617223863568053374819 29588425835795352080062229)
                  ·
                    refine ⟨1386957461052907128752917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29588425835795352080062229 1386957461052907128752917)
                    ·
                      rfl

theorem cell22_4051635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_4051635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051635 prefixEnd_4051635 := by exact prefixLift 4051635
  have htrace : WordTrace (prefixWord ++ tailWord_4051635) baseStart_4051635 baseEnd_4051635 := by
    simpa [prefixWord, tailWord_4051635, baseEnd_4051635] using wordTrace_append hprefix tailTrace_4051635
  have hstable : (prefixWord ++ tailWord_4051635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051635).length < 2 ^ (prefixWord ++ tailWord_4051635).sum := by decide
  have hdescent : baseEnd_4051635 < baseStart_4051635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051652 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_4051652 : Nat := 118140960795 + 4051652 * 2 ^ 59
def prefixEnd_4051652 : Nat := 4983230072969 + 3 ^ 40 * 4051652 * 2
def baseEnd_4051652 : Nat := 1386963280500324751077865

theorem tailTrace_4051652 : CollatzResearch.WordTrace tailWord_4051652 prefixEnd_4051652 1386963280500324751077865 := by
  unfold tailWord_4051652
  simp only [CollatzResearch.WordTrace]
  refine ⟨73887944358782122958198605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98517259145042830610931473 73887944358782122958198605)
  ·
    refine ⟨27707979134543296109324477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73887944358782122958198605 27707979134543296109324477)
    ·
      refine ⟨10390492175453736040996679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27707979134543296109324477 10390492175453736040996679)
      ·
        refine ⟨15585738263180604061495019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10390492175453736040996679 15585738263180604061495019)
        ·
          refine ⟨23378607394770906092242529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15585738263180604061495019 23378607394770906092242529)
          ·
            refine ⟨17533955546078179569181897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23378607394770906092242529 17533955546078179569181897)
            ·
              refine ⟨13150466659558634676886423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17533955546078179569181897 13150466659558634676886423)
              ·
                refine ⟨19725699989337952015329635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13150466659558634676886423 19725699989337952015329635)
                ·
                  refine ⟨29588549984006928022994453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19725699989337952015329635 29588549984006928022994453)
                  ·
                    refine ⟨1386963280500324751077865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29588549984006928022994453 1386963280500324751077865)
                    ·
                      rfl

theorem cell22_4051652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_4051652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051652 prefixEnd_4051652 := by exact prefixLift 4051652
  have htrace : WordTrace (prefixWord ++ tailWord_4051652) baseStart_4051652 baseEnd_4051652 := by
    simpa [prefixWord, tailWord_4051652, baseEnd_4051652] using wordTrace_append hprefix tailTrace_4051652
  have hstable : (prefixWord ++ tailWord_4051652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051652).length < 2 ^ (prefixWord ++ tailWord_4051652).sum := by decide
  have hdescent : baseEnd_4051652 < baseStart_4051652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051680 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_4051680 : Nat := 118140960795 + 4051680 * 2 ^ 59
def prefixEnd_4051680 : Nat := 4983230072969 + 3 ^ 40 * 4051680 * 2
def baseEnd_4051680 : Nat := 1386972865472542011377779

theorem tailTrace_4051680 : CollatzResearch.WordTrace tailWord_4051680 prefixEnd_4051680 1386972865472542011377779 := by
  unfold tailWord_4051680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73888454980731403349208247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98517939974308537798944329 73888454980731403349208247)
  ·
    refine ⟨110832682471097105023812371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73888454980731403349208247 110832682471097105023812371)
    ·
      refine ⟨166249023706645657535718557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110832682471097105023812371 166249023706645657535718557)
      ·
        refine ⟨62343383889992121575894459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166249023706645657535718557 62343383889992121575894459)
        ·
          refine ⟨93515075834988182363841689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62343383889992121575894459 93515075834988182363841689)
          ·
            refine ⟨70136306876241136772881267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93515075834988182363841689 70136306876241136772881267)
            ·
              refine ⟨105204460314361705159321901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70136306876241136772881267 105204460314361705159321901)
              ·
                refine ⟨39451672617885639434745713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105204460314361705159321901 39451672617885639434745713)
                ·
                  refine ⟨29588754463414229576059285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39451672617885639434745713 29588754463414229576059285)
                  ·
                    refine ⟨1386972865472542011377779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29588754463414229576059285 1386972865472542011377779)
                    ·
                      rfl

theorem cell22_4051680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_4051680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051680 prefixEnd_4051680 := by exact prefixLift 4051680
  have htrace : WordTrace (prefixWord ++ tailWord_4051680) baseStart_4051680 baseEnd_4051680 := by
    simpa [prefixWord, tailWord_4051680, baseEnd_4051680] using wordTrace_append hprefix tailTrace_4051680
  have hstable : (prefixWord ++ tailWord_4051680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051680).length < 2 ^ (prefixWord ++ tailWord_4051680).sum := by decide
  have hdescent : baseEnd_4051680 < baseStart_4051680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051688 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_4051688 : Nat := 118140960795 + 4051688 * 2 ^ 59
def prefixEnd_4051688 : Nat := 4983230072969 + 3 ^ 40 * 4051688 * 2
def baseEnd_4051688 : Nat := 1386975604036032657177755

theorem tailTrace_4051688 : CollatzResearch.WordTrace tailWord_4051688 prefixEnd_4051688 1386975604036032657177755 := by
  unfold tailWord_4051688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73888600872716912032353859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98518134496955882709805145 73888600872716912032353859)
  ·
    refine ⟨110832901309075368048530789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73888600872716912032353859 110832901309075368048530789)
    ·
      refine ⟨20781168995451631509099523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110832901309075368048530789 20781168995451631509099523)
      ·
        refine ⟨31171753493177447263649285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20781168995451631509099523 31171753493177447263649285)
        ·
          refine ⟨5844703779970771361934241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31171753493177447263649285 5844703779970771361934241)
          ·
            refine ⟨4383527834978078521450681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5844703779970771361934241 4383527834978078521450681)
            ·
              refine ⟨3287645876233558891088011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4383527834978078521450681 3287645876233558891088011)
              ·
                refine ⟨4931468814350338336632017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287645876233558891088011 4931468814350338336632017)
                ·
                  refine ⟨3698601610762753752474013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931468814350338336632017 3698601610762753752474013)
                  ·
                    refine ⟨1386975604036032657177755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698601610762753752474013 1386975604036032657177755)
                    ·
                      rfl

theorem cell22_4051688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_4051688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051688 prefixEnd_4051688 := by exact prefixLift 4051688
  have htrace : WordTrace (prefixWord ++ tailWord_4051688) baseStart_4051688 baseEnd_4051688 := by
    simpa [prefixWord, tailWord_4051688, baseEnd_4051688] using wordTrace_append hprefix tailTrace_4051688
  have hstable : (prefixWord ++ tailWord_4051688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051688).length < 2 ^ (prefixWord ++ tailWord_4051688).sum := by decide
  have hdescent : baseEnd_4051688 < baseStart_4051688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051716 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_4051716 : Nat := 118140960795 + 4051716 * 2 ^ 59
def prefixEnd_4051716 : Nat := 4983230072969 + 3 ^ 40 * 4051716 * 2
def baseEnd_4051716 : Nat := 1386985189008249917477669

theorem tailTrace_4051716 : CollatzResearch.WordTrace tailWord_4051716 prefixEnd_4051716 1386985189008249917477669 := by
  unfold tailWord_4051716
  simp only [CollatzResearch.WordTrace]
  refine ⟨73889111494666192423363501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98518815326221589897818001 73889111494666192423363501)
  ·
    refine ⟨27708416810499822158761313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73889111494666192423363501 27708416810499822158761313)
    ·
      refine ⟨20781312607874866619070985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27708416810499822158761313 20781312607874866619070985)
      ·
        refine ⟨15585984455906149964303239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20781312607874866619070985 15585984455906149964303239)
        ·
          refine ⟨23378976683859224946454859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15585984455906149964303239 23378976683859224946454859)
          ·
            refine ⟨35068465025788837419682289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23378976683859224946454859 35068465025788837419682289)
            ·
              refine ⟨26301348769341628064761717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35068465025788837419682289 26301348769341628064761717)
              ·
                refine ⟨2465751447125777631071411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26301348769341628064761717 2465751447125777631071411)
                ·
                  refine ⟨3698627170688666446607117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465751447125777631071411 3698627170688666446607117)
                  ·
                    refine ⟨1386985189008249917477669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698627170688666446607117 1386985189008249917477669)
                    ·
                      rfl

theorem cell22_4051716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_4051716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051716 prefixEnd_4051716 := by exact prefixLift 4051716
  have htrace : WordTrace (prefixWord ++ tailWord_4051716) baseStart_4051716 baseEnd_4051716 := by
    simpa [prefixWord, tailWord_4051716, baseEnd_4051716] using wordTrace_append hprefix tailTrace_4051716
  have hstable : (prefixWord ++ tailWord_4051716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051716).length < 2 ^ (prefixWord ++ tailWord_4051716).sum := by decide
  have hdescent : baseEnd_4051716 < baseStart_4051716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051780 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_4051780 : Nat := 118140960795 + 4051780 * 2 ^ 59
def prefixEnd_4051780 : Nat := 4983230072969 + 3 ^ 40 * 4051780 * 2
def baseEnd_4051780 : Nat := 462335699172058361292491

theorem tailTrace_4051780 : CollatzResearch.WordTrace tailWord_4051780 prefixEnd_4051780 462335699172058361292491 := by
  unfold tailWord_4051780
  simp only [CollatzResearch.WordTrace]
  refine ⟨73890278630550261888528397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98520371507400349184704529 73890278630550261888528397)
  ·
    refine ⟨27708854486456348208198149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73890278630550261888528397 27708854486456348208198149)
    ·
      refine ⟨5195410216210565289037153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27708854486456348208198149 5195410216210565289037153)
      ·
        refine ⟨3896557662157923966777865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5195410216210565289037153 3896557662157923966777865)
        ·
          refine ⟨2922418246618442975083399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3896557662157923966777865 2922418246618442975083399)
          ·
            refine ⟨4383627369927664462625099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922418246618442975083399 4383627369927664462625099)
            ·
              refine ⟨6575441054891496693937649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383627369927664462625099 6575441054891496693937649)
              ·
                refine ⟨4931580791168622520453237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6575441054891496693937649 4931580791168622520453237)
                ·
                  refine ⟨462335699172058361292491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4931580791168622520453237 462335699172058361292491)
                  ·
                    rfl

theorem cell22_4051780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_4051780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051780 prefixEnd_4051780 := by exact prefixLift 4051780
  have htrace : WordTrace (prefixWord ++ tailWord_4051780) baseStart_4051780 baseEnd_4051780 := by
    simpa [prefixWord, tailWord_4051780, baseEnd_4051780] using wordTrace_append hprefix tailTrace_4051780
  have hstable : (prefixWord ++ tailWord_4051780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051780).length < 2 ^ (prefixWord ++ tailWord_4051780).sum := by decide
  have hdescent : baseEnd_4051780 < baseStart_4051780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051804 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4051804 : Nat := 118140960795 + 4051804 * 2 ^ 59
def prefixEnd_4051804 : Nat := 4983230072969 + 3 ^ 40 * 4051804 * 2
def baseEnd_4051804 : Nat := 1387015313206647021277399

theorem tailTrace_4051804 : CollatzResearch.WordTrace tailWord_4051804 prefixEnd_4051804 1387015313206647021277399 := by
  unfold tailWord_4051804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73890716306506787937965233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98520955075342383917286977 73890716306506787937965233)
  ·
    refine ⟨55418037229880090953473925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73890716306506787937965233 55418037229880090953473925)
    ·
      refine ⟨10390881980602517053776361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55418037229880090953473925 10390881980602517053776361)
      ·
        refine ⟨7793161485451887790332271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10390881980602517053776361 7793161485451887790332271)
        ·
          refine ⟨11689742228177831685498407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793161485451887790332271 11689742228177831685498407)
          ·
            refine ⟨17534613342266747528247611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689742228177831685498407 17534613342266747528247611)
            ·
              refine ⟨26301920013400121292371417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17534613342266747528247611 26301920013400121292371417)
              ·
                refine ⟨19726440010050090969278563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26301920013400121292371417 19726440010050090969278563)
                ·
                  refine ⟨29589660015075136453917845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19726440010050090969278563 29589660015075136453917845)
                  ·
                    refine ⟨1387015313206647021277399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29589660015075136453917845 1387015313206647021277399)
                    ·
                      rfl

theorem cell22_4051804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4051804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051804 prefixEnd_4051804 := by exact prefixLift 4051804
  have htrace : WordTrace (prefixWord ++ tailWord_4051804) baseStart_4051804 baseEnd_4051804 := by
    simpa [prefixWord, tailWord_4051804, baseEnd_4051804] using wordTrace_append hprefix tailTrace_4051804
  have hstable : (prefixWord ++ tailWord_4051804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051804).length < 2 ^ (prefixWord ++ tailWord_4051804).sum := by decide
  have hdescent : baseEnd_4051804 < baseStart_4051804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051838 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_4051838 : Nat := 118140960795 + 4051838 * 2 ^ 59
def prefixEnd_4051838 : Nat := 4983230072969 + 3 ^ 40 * 4051838 * 2
def baseEnd_4051838 : Nat := 1387026952101482265927295

theorem tailTrace_4051838 : CollatzResearch.WordTrace tailWord_4051838 prefixEnd_4051838 1387026952101482265927295 := by
  unfold tailWord_4051838
  simp only [CollatzResearch.WordTrace]
  refine ⟨18472834086861299960333521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98521781796593599788445445 18472834086861299960333521)
  ·
    refine ⟨13854625565145974970250141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18472834086861299960333521 13854625565145974970250141)
    ·
      refine ⟨5195484586929740613843803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13854625565145974970250141 5195484586929740613843803)
      ·
        refine ⟨7793226880394610920765705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195484586929740613843803 7793226880394610920765705)
        ·
          refine ⟨5844920160295958190574279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7793226880394610920765705 5844920160295958190574279)
          ·
            refine ⟨8767380240443937285861419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844920160295958190574279 8767380240443937285861419)
            ·
              refine ⟨13151070360665905928792129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8767380240443937285861419 13151070360665905928792129)
              ·
                refine ⟨9863302770499429446594097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13151070360665905928792129 9863302770499429446594097)
                ·
                  refine ⟨7397477077874572084945573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9863302770499429446594097 7397477077874572084945573)
                  ·
                    refine ⟨1387026952101482265927295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397477077874572084945573 1387026952101482265927295)
                    ·
                      rfl

theorem cell22_4051838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_4051838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051838 prefixEnd_4051838 := by exact prefixLift 4051838
  have htrace : WordTrace (prefixWord ++ tailWord_4051838) baseStart_4051838 baseEnd_4051838 := by
    simpa [prefixWord, tailWord_4051838, baseEnd_4051838] using wordTrace_append hprefix tailTrace_4051838
  have hstable : (prefixWord ++ tailWord_4051838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051838).length < 2 ^ (prefixWord ++ tailWord_4051838).sum := by decide
  have hdescent : baseEnd_4051838 < baseStart_4051838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051842 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_4051842 : Nat := 118140960795 + 4051842 * 2 ^ 59
def prefixEnd_4051842 : Nat := 4983230072969 + 3 ^ 40 * 4051842 * 2
def baseEnd_4051842 : Nat := 462342773794409196275761

theorem tailTrace_4051842 : CollatzResearch.WordTrace tailWord_4051842 prefixEnd_4051842 462342773794409196275761 := by
  unfold tailWord_4051842
  simp only [CollatzResearch.WordTrace]
  refine ⟨36945704646718977091453445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98521879057917272243875853 36945704646718977091453445)
  ·
    refine ⟨6927319621259808204647521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36945704646718977091453445 6927319621259808204647521)
    ·
      refine ⟨5195489715944856153485641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6927319621259808204647521 5195489715944856153485641)
      ·
        refine ⟨3896617286958642115114231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5195489715944856153485641 3896617286958642115114231)
        ·
          refine ⟨5844925930437963172671347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896617286958642115114231 5844925930437963172671347)
          ·
            refine ⟨8767388895656944759007021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844925930437963172671347 8767388895656944759007021)
            ·
              refine ⟨3287770835871354284627633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8767388895656944759007021 3287770835871354284627633)
              ·
                refine ⟨2465828126903515713470725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3287770835871354284627633 2465828126903515713470725)
                ·
                  refine ⟨462342773794409196275761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465828126903515713470725 462342773794409196275761)
                  ·
                    rfl

theorem cell22_4051842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_4051842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051842 prefixEnd_4051842 := by exact prefixLift 4051842
  have htrace : WordTrace (prefixWord ++ tailWord_4051842) baseStart_4051842 baseEnd_4051842 := by
    simpa [prefixWord, tailWord_4051842, baseEnd_4051842] using wordTrace_append hprefix tailTrace_4051842
  have hstable : (prefixWord ++ tailWord_4051842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051842).length < 2 ^ (prefixWord ++ tailWord_4051842).sum := by decide
  have hdescent : baseEnd_4051842 < baseStart_4051842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051851 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 1, 3]
def baseStart_4051851 : Nat := 118140960795 + 4051851 * 2 ^ 59
def prefixEnd_4051851 : Nat := 4983230072969 + 3 ^ 40 * 4051851 * 2
def baseEnd_4051851 : Nat := 1387031402267154565352255

theorem tailTrace_4051851 : CollatzResearch.WordTrace tailWord_4051851 prefixEnd_4051851 1387031402267154565352255 := by
  unfold tailWord_4051851
  simp only [CollatzResearch.WordTrace]
  refine ⟨147783146843843302902891407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98522097895895535268594271 147783146843843302902891407)
  ·
    refine ⟨221674720265764954354337111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147783146843843302902891407 221674720265764954354337111)
    ·
      refine ⟨332512080398647431531505667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221674720265764954354337111 332512080398647431531505667)
      ·
        refine ⟨498768120597971147297258501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332512080398647431531505667 498768120597971147297258501)
        ·
          refine ⟨93519022612119590118235969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498768120597971147297258501 93519022612119590118235969)
          ·
            refine ⟨70139266959089692588676977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93519022612119590118235969 70139266959089692588676977)
            ·
              refine ⟨52604450219317269441507733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70139266959089692588676977 52604450219317269441507733)
              ·
                refine ⟨2465833604030497005070675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52604450219317269441507733 2465833604030497005070675)
                ·
                  refine ⟨3698750406045745507606013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465833604030497005070675 3698750406045745507606013)
                  ·
                    refine ⟨1387031402267154565352255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698750406045745507606013 1387031402267154565352255)
                    ·
                      rfl

theorem cell22_4051851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 3].length) (baseStart_4051851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051851 prefixEnd_4051851 := by exact prefixLift 4051851
  have htrace : WordTrace (prefixWord ++ tailWord_4051851) baseStart_4051851 baseEnd_4051851 := by
    simpa [prefixWord, tailWord_4051851, baseEnd_4051851] using wordTrace_append hprefix tailTrace_4051851
  have hstable : (prefixWord ++ tailWord_4051851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051851).length < 2 ^ (prefixWord ++ tailWord_4051851).sum := by decide
  have hdescent : baseEnd_4051851 < baseStart_4051851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051926 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4051926 : Nat := 118140960795 + 4051926 * 2 ^ 59
def prefixEnd_4051926 : Nat := 4983230072969 + 3 ^ 40 * 4051926 * 2
def baseEnd_4051926 : Nat := 462352358766626456575675

theorem tailTrace_4051926 : CollatzResearch.WordTrace tailWord_4051926 prefixEnd_4051926 462352358766626456575675 := by
  unfold tailWord_4051926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236617644910724419491977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98523921545714393807914421 9236617644910724419491977)
  ·
    refine ⟨6927463233683043314618983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9236617644910724419491977 6927463233683043314618983)
    ·
      refine ⟨10391194850524564971928475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927463233683043314618983 10391194850524564971928475)
      ·
        refine ⟨15586792275786847457892713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391194850524564971928475 15586792275786847457892713)
        ·
          refine ⟨11690094206840135593419535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15586792275786847457892713 11690094206840135593419535)
          ·
            refine ⟨17535141310260203390129303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690094206840135593419535 17535141310260203390129303)
            ·
              refine ⟨26302711965390305085193955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17535141310260203390129303 26302711965390305085193955)
              ·
                refine ⟨39454067948085457627790933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26302711965390305085193955 39454067948085457627790933)
                ·
                  refine ⟨462352358766626456575675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39454067948085457627790933 462352358766626456575675)
                  ·
                    rfl

theorem cell22_4051926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4051926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051926 prefixEnd_4051926 := by exact prefixLift 4051926
  have htrace : WordTrace (prefixWord ++ tailWord_4051926) baseStart_4051926 baseEnd_4051926 := by
    simpa [prefixWord, tailWord_4051926, baseEnd_4051926] using wordTrace_append hprefix tailTrace_4051926
  have hstable : (prefixWord ++ tailWord_4051926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051926).length < 2 ^ (prefixWord ++ tailWord_4051926).sum := by decide
  have hdescent : baseEnd_4051926 < baseStart_4051926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051939 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_4051939 : Nat := 118140960795 + 4051939 * 2 ^ 59
def prefixEnd_4051939 : Nat := 4983230072969 + 3 ^ 40 * 4051939 * 2
def baseEnd_4051939 : Nat := 1387061526465551669151985

theorem tailTrace_4051939 : CollatzResearch.WordTrace tailWord_4051939 prefixEnd_4051939 1387061526465551669151985 := by
  unfold tailWord_4051939
  simp only [CollatzResearch.WordTrace]
  refine ⟨147786356467524493932094871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98524237645016329288063247 147786356467524493932094871)
  ·
    refine ⟨221679534701286740898142307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147786356467524493932094871 221679534701286740898142307)
    ·
      refine ⟨332519302051930111347213461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221679534701286740898142307 332519302051930111347213461)
      ·
        refine ⟨15586842283684223969400631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 332519302051930111347213461 15586842283684223969400631)
        ·
          refine ⟨23380263425526335954100947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15586842283684223969400631 23380263425526335954100947)
          ·
            refine ⟨35070395138289503931151421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23380263425526335954100947 35070395138289503931151421)
            ·
              refine ⟨13151398176858563974181783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35070395138289503931151421 13151398176858563974181783)
              ·
                refine ⟨19727097265287845961272675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13151398176858563974181783 19727097265287845961272675)
                ·
                  refine ⟨29590645897931768941909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19727097265287845961272675 29590645897931768941909013)
                  ·
                    refine ⟨1387061526465551669151985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29590645897931768941909013 1387061526465551669151985)
                    ·
                      rfl

theorem cell22_4051939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_4051939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051939 prefixEnd_4051939 := by exact prefixLift 4051939
  have htrace : WordTrace (prefixWord ++ tailWord_4051939) baseStart_4051939 baseEnd_4051939 := by
    simpa [prefixWord, tailWord_4051939, baseEnd_4051939] using wordTrace_append hprefix tailTrace_4051939
  have hstable : (prefixWord ++ tailWord_4051939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051939).length < 2 ^ (prefixWord ++ tailWord_4051939).sum := by decide
  have hdescent : baseEnd_4051939 < baseStart_4051939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051943 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 4]
def baseStart_4051943 : Nat := 118140960795 + 4051943 * 2 ^ 59
def prefixEnd_4051943 : Nat := 4983230072969 + 3 ^ 40 * 4051943 * 2
def baseEnd_4051943 : Nat := 462354298582432330683991

theorem tailTrace_4051943 : CollatzResearch.WordTrace tailWord_4051943 prefixEnd_4051943 462354298582432330683991 := by
  unfold tailWord_4051943
  simp only [CollatzResearch.WordTrace]
  refine ⟨147786502359510002615240483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98524334906340001743493655 147786502359510002615240483)
  ·
    refine ⟨221679753539265003922860725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147786502359510002615240483 221679753539265003922860725)
    ·
      refine ⟨20782476894306094117768193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221679753539265003922860725 20782476894306094117768193)
      ·
        refine ⟨15586857670729570588326145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20782476894306094117768193 15586857670729570588326145)
        ·
          refine ⟨11690143253047177941244609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15586857670729570588326145 11690143253047177941244609)
          ·
            refine ⟨8767607439785383455933457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11690143253047177941244609 8767607439785383455933457)
            ·
              refine ⟨6575705579839037591950093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8767607439785383455933457 6575705579839037591950093)
              ·
                refine ⟨2465889592439639096981285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6575705579839037591950093 2465889592439639096981285)
                ·
                  refine ⟨462354298582432330683991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2465889592439639096981285 462354298582432330683991)
                  ·
                    rfl

theorem cell22_4051943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 4].length) (baseStart_4051943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051943 prefixEnd_4051943 := by exact prefixLift 4051943
  have htrace : WordTrace (prefixWord ++ tailWord_4051943) baseStart_4051943 baseEnd_4051943 := by
    simpa [prefixWord, tailWord_4051943, baseEnd_4051943] using wordTrace_append hprefix tailTrace_4051943
  have hstable : (prefixWord ++ tailWord_4051943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051943).length < 2 ^ (prefixWord ++ tailWord_4051943).sum := by decide
  have hdescent : baseEnd_4051943 < baseStart_4051943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051958 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_4051958 : Nat := 118140960795 + 4051958 * 2 ^ 59
def prefixEnd_4051958 : Nat := 4983230072969 + 3 ^ 40 * 4051958 * 2
def baseEnd_4051958 : Nat := 1387068030553841952926927

theorem tailTrace_4051958 : CollatzResearch.WordTrace tailWord_4051958 prefixEnd_4051958 1387068030553841952926927 := by
  unfold tailWord_4051958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236690590903478761064783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98524699636303773451357685 9236690590903478761064783)
  ·
    refine ⟨13855035886355218141597175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9236690590903478761064783 13855035886355218141597175)
    ·
      refine ⟨20782553829532827212395763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855035886355218141597175 20782553829532827212395763)
      ·
        refine ⟨31173830744299240818593645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20782553829532827212395763 31173830744299240818593645)
        ·
          refine ⟨11690186529112215306972617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31173830744299240818593645 11690186529112215306972617)
          ·
            refine ⟨8767639896834161480229463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11690186529112215306972617 8767639896834161480229463)
            ·
              refine ⟨13151459845251242220344195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8767639896834161480229463 13151459845251242220344195)
              ·
                refine ⟨19727189767876863330516293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13151459845251242220344195 19727189767876863330516293)
                ·
                  refine ⟨3698848081476911874471805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19727189767876863330516293 3698848081476911874471805)
                  ·
                    refine ⟨1387068030553841952926927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698848081476911874471805 1387068030553841952926927)
                    ·
                      rfl

theorem cell22_4051958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_4051958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051958 prefixEnd_4051958 := by exact prefixLift 4051958
  have htrace : WordTrace (prefixWord ++ tailWord_4051958) baseStart_4051958 baseEnd_4051958 := by
    simpa [prefixWord, tailWord_4051958, baseEnd_4051958] using wordTrace_append hprefix tailTrace_4051958
  have hstable : (prefixWord ++ tailWord_4051958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051958).length < 2 ^ (prefixWord ++ tailWord_4051958).sum := by decide
  have hdescent : baseEnd_4051958 < baseStart_4051958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4051999 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 7]
def baseStart_4051999 : Nat := 118140960795 + 4051999 * 2 ^ 59
def prefixEnd_4051999 : Nat := 4983230072969 + 3 ^ 40 * 4051999 * 2
def baseEnd_4051999 : Nat := 462360688563910504217267

theorem tailTrace_4051999 : CollatzResearch.WordTrace tailWord_4051999 prefixEnd_4051999 462360688563910504217267 := by
  unfold tailWord_4051999
  simp only [CollatzResearch.WordTrace]
  refine ⟨147788544847307124179279051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98525696564871416119519367 147788544847307124179279051)
  ·
    refine ⟨221682817270960686268918577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147788544847307124179279051 221682817270960686268918577)
    ·
      refine ⟨166262112953220514701688933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221682817270960686268918577 166262112953220514701688933)
      ·
        refine ⟨31174146178728846506566675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166262112953220514701688933 31174146178728846506566675)
        ·
          refine ⟨46761219268093269759850013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31174146178728846506566675 46761219268093269759850013)
          ·
            refine ⟨17535457225534976159943755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46761219268093269759850013 17535457225534976159943755)
            ·
              refine ⟨26303185838302464239915633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17535457225534976159943755 26303185838302464239915633)
              ·
                refine ⟨19727389378726848179936725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26303185838302464239915633 19727389378726848179936725)
                ·
                  refine ⟨462360688563910504217267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19727389378726848179936725 462360688563910504217267)
                  ·
                    rfl

theorem cell22_4051999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_4051999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4051999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4051999 prefixEnd_4051999 := by exact prefixLift 4051999
  have htrace : WordTrace (prefixWord ++ tailWord_4051999) baseStart_4051999 baseEnd_4051999 := by
    simpa [prefixWord, tailWord_4051999, baseEnd_4051999] using wordTrace_append hprefix tailTrace_4051999
  have hstable : (prefixWord ++ tailWord_4051999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4051999).length < 2 ^ (prefixWord ++ tailWord_4051999).sum := by decide
  have hdescent : baseEnd_4051999 < baseStart_4051999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4051999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052020 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_4052020 : Nat := 118140960795 + 4052020 * 2 ^ 59
def prefixEnd_4052020 : Nat := 4983230072969 + 3 ^ 40 * 4052020 * 2
def baseEnd_4052020 : Nat := 1387089254420894457876737

theorem tailTrace_4052020 : CollatzResearch.WordTrace tailWord_4052020 prefixEnd_4052020 1387089254420894457876737 := by
  unfold tailWord_4052020
  simp only [CollatzResearch.WordTrace]
  refine ⟨73894655390115522382896757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98526207186820696510529009 73894655390115522382896757)
  ·
    refine ⟨6927623942823330223396571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73894655390115522382896757 6927623942823330223396571)
    ·
      refine ⟨10391435914234995335094857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927623942823330223396571 10391435914234995335094857)
      ·
        refine ⟨7793576935676246501321143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10391435914234995335094857 7793576935676246501321143)
        ·
          refine ⟨11690365403514369751981715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793576935676246501321143 11690365403514369751981715)
          ·
            refine ⟨17535548105271554627972573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690365403514369751981715 17535548105271554627972573)
            ·
              refine ⟨6575830539476832985489715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17535548105271554627972573 6575830539476832985489715)
              ·
                refine ⟨9863745809215249478234573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575830539476832985489715 9863745809215249478234573)
                ·
                  refine ⟨3698904678455718554337965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9863745809215249478234573 3698904678455718554337965)
                  ·
                    refine ⟨1387089254420894457876737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698904678455718554337965 1387089254420894457876737)
                    ·
                      rfl

theorem cell22_4052020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_4052020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052020 prefixEnd_4052020 := by exact prefixLift 4052020
  have htrace : WordTrace (prefixWord ++ tailWord_4052020) baseStart_4052020 baseEnd_4052020 := by
    simpa [prefixWord, tailWord_4052020, baseEnd_4052020] using wordTrace_append hprefix tailTrace_4052020
  have hstable : (prefixWord ++ tailWord_4052020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052020).length < 2 ^ (prefixWord ++ tailWord_4052020).sum := by decide
  have hdescent : baseEnd_4052020 < baseStart_4052020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052033 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 5]
def baseStart_4052033 : Nat := 118140960795 + 4052033 * 2 ^ 59
def prefixEnd_4052033 : Nat := 4983230072969 + 3 ^ 40 * 4052033 * 2
def baseEnd_4052033 : Nat := 462364568195522252433899

theorem tailTrace_4052033 : CollatzResearch.WordTrace tailWord_4052033 prefixEnd_4052033 462364568195522252433899 := by
  unfold tailWord_4052033
  simp only [CollatzResearch.WordTrace]
  refine ⟨147789784929183947986016753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98526523286122631990677835 147789784929183947986016753)
  ·
    refine ⟨110842338696887960989512565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147789784929183947986016753 110842338696887960989512565)
    ·
      refine ⟨10391469252833246342766803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110842338696887960989512565 10391469252833246342766803)
      ·
        refine ⟨15587203879249869514150205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391469252833246342766803 15587203879249869514150205)
        ·
          refine ⟨5845201454718701067806327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15587203879249869514150205 5845201454718701067806327)
          ·
            refine ⟨8767802182078051601709491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845201454718701067806327 8767802182078051601709491)
            ·
              refine ⟨13151703273117077402564237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8767802182078051601709491 13151703273117077402564237)
              ·
                refine ⟨4931888727418904025961589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13151703273117077402564237 4931888727418904025961589)
                ·
                  refine ⟨462364568195522252433899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4931888727418904025961589 462364568195522252433899)
                  ·
                    rfl

theorem cell22_4052033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_4052033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052033 prefixEnd_4052033 := by exact prefixLift 4052033
  have htrace : WordTrace (prefixWord ++ tailWord_4052033) baseStart_4052033 baseEnd_4052033 := by
    simpa [prefixWord, tailWord_4052033, baseEnd_4052033] using wordTrace_append hprefix tailTrace_4052033
  have hstable : (prefixWord ++ tailWord_4052033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052033).length < 2 ^ (prefixWord ++ tailWord_4052033).sum := by decide
  have hdescent : baseEnd_4052033 < baseStart_4052033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052044 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_4052044 : Nat := 118140960795 + 4052044 * 2 ^ 59
def prefixEnd_4052044 : Nat := 4983230072969 + 3 ^ 40 * 4052044 * 2
def baseEnd_4052044 : Nat := 462365823370455465092221

theorem tailTrace_4052044 : CollatzResearch.WordTrace tailWord_4052044 prefixEnd_4052044 462365823370455465092221 := by
  unfold tailWord_4052044
  simp only [CollatzResearch.WordTrace]
  refine ⟨73895093066072048432333593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98526790754762731243111457 73895093066072048432333593)
  ·
    refine ⟨55421319799554036324250195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73895093066072048432333593 55421319799554036324250195)
    ·
      refine ⟨83131979699331054486375293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55421319799554036324250195 83131979699331054486375293)
      ·
        refine ⟨31174492387249145432390735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83131979699331054486375293 31174492387249145432390735)
        ·
          refine ⟨46761738580873718148586103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31174492387249145432390735 46761738580873718148586103)
          ·
            refine ⟨70142607871310577222879155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46761738580873718148586103 70142607871310577222879155)
            ·
              refine ⟨105213911806965865834318733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70142607871310577222879155 105213911806965865834318733)
              ·
                refine ⟨39455216927612199687869525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105213911806965865834318733 39455216927612199687869525)
                ·
                  refine ⟨462365823370455465092221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39455216927612199687869525 462365823370455465092221)
                  ·
                    rfl

theorem cell22_4052044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_4052044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052044 prefixEnd_4052044 := by exact prefixLift 4052044
  have htrace : WordTrace (prefixWord ++ tailWord_4052044) baseStart_4052044 baseEnd_4052044 := by
    simpa [prefixWord, tailWord_4052044, baseEnd_4052044] using wordTrace_append hprefix tailTrace_4052044
  have hstable : (prefixWord ++ tailWord_4052044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052044).length < 2 ^ (prefixWord ++ tailWord_4052044).sum := by decide
  have hdescent : baseEnd_4052044 < baseStart_4052044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052046 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_4052046 : Nat := 118140960795 + 4052046 * 2 ^ 59
def prefixEnd_4052046 : Nat := 4983230072969 + 3 ^ 40 * 4052046 * 2
def baseEnd_4052046 : Nat := 1387098154752239056726657

theorem tailTrace_4052046 : CollatzResearch.WordTrace tailWord_4052046 prefixEnd_4052046 1387098154752239056726657 := by
  unfold tailWord_4052046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473782384767106400779999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98526839385424567470826661 18473782384767106400779999)
  ·
    refine ⟨27710673577150659601169999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18473782384767106400779999 27710673577150659601169999)
    ·
      refine ⟨41566010365725989401754999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27710673577150659601169999 41566010365725989401754999)
      ·
        refine ⟨62349015548588984102632499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41566010365725989401754999 62349015548588984102632499)
        ·
          refine ⟨93523523322883476153948749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62349015548588984102632499 93523523322883476153948749)
          ·
            refine ⟨35071321246081303557730781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93523523322883476153948749 35071321246081303557730781)
            ·
              refine ⟨13151745467280488834149043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35071321246081303557730781 13151745467280488834149043)
              ·
                refine ⟨19727618200920733251223565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13151745467280488834149043 19727618200920733251223565)
                ·
                  refine ⟨7397856825345274969208837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19727618200920733251223565 7397856825345274969208837)
                  ·
                    refine ⟨1387098154752239056726657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397856825345274969208837 1387098154752239056726657)
                    ·
                      rfl

theorem cell22_4052046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_4052046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052046 prefixEnd_4052046 := by exact prefixLift 4052046
  have htrace : WordTrace (prefixWord ++ tailWord_4052046) baseStart_4052046 baseEnd_4052046 := by
    simpa [prefixWord, tailWord_4052046, baseEnd_4052046] using wordTrace_append hprefix tailTrace_4052046
  have hstable : (prefixWord ++ tailWord_4052046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052046).length < 2 ^ (prefixWord ++ tailWord_4052046).sum := by decide
  have hdescent : baseEnd_4052046 < baseStart_4052046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052063 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 1, 4]
def baseStart_4052063 : Nat := 118140960795 + 4052063 * 2 ^ 59
def prefixEnd_4052063 : Nat := 4983230072969 + 3 ^ 40 * 4052063 * 2
def baseEnd_4052063 : Nat := 1387103974199656679051605

theorem tailTrace_4052063 : CollatzResearch.WordTrace tailWord_4052063 prefixEnd_4052063 1387103974199656679051605 := by
  unfold tailWord_4052063
  simp only [CollatzResearch.WordTrace]
  refine ⟨147790879119075263109608843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98527252746050175406405895 147790879119075263109608843)
  ·
    refine ⟨221686318678612894664413265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147790879119075263109608843 221686318678612894664413265)
    ·
      refine ⟨166264739008959670998309949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221686318678612894664413265 166264739008959670998309949)
      ·
        refine ⟨62349277128359876624366231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166264739008959670998309949 62349277128359876624366231)
        ·
          refine ⟨93523915692539814936549347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62349277128359876624366231 93523915692539814936549347)
          ·
            refine ⟨140285873538809722404824021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93523915692539814936549347 140285873538809722404824021)
            ·
              refine ⟨3287950161065852868863063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140285873538809722404824021 3287950161065852868863063)
              ·
                refine ⟨4931925241598779303294595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287950161065852868863063 4931925241598779303294595)
                ·
                  refine ⟨7397887862398168954941893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931925241598779303294595 7397887862398168954941893)
                  ·
                    refine ⟨1387103974199656679051605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397887862398168954941893 1387103974199656679051605)
                    ·
                      rfl

theorem cell22_4052063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 4].length) (baseStart_4052063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052063 prefixEnd_4052063 := by exact prefixLift 4052063
  have htrace : WordTrace (prefixWord ++ tailWord_4052063) baseStart_4052063 baseEnd_4052063 := by
    simpa [prefixWord, tailWord_4052063, baseEnd_4052063] using wordTrace_append hprefix tailTrace_4052063
  have hstable : (prefixWord ++ tailWord_4052063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052063).length < 2 ^ (prefixWord ++ tailWord_4052063).sum := by decide
  have hdescent : baseEnd_4052063 < baseStart_4052063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052093 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_4052093 : Nat := 118140960795 + 4052093 * 2 ^ 59
def prefixEnd_4052093 : Nat := 4983230072969 + 3 ^ 40 * 4052093 * 2
def baseEnd_4052093 : Nat := 1387114243812746600801513

theorem tailTrace_4052093 : CollatzResearch.WordTrace tailWord_4052093 prefixEnd_4052093 1387114243812746600801513 := by
  unfold tailWord_4052093
  simp only [CollatzResearch.WordTrace]
  refine ⟨147791973308966578233200933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98527982205977718822133955 147791973308966578233200933)
  ·
    refine ⟨27710994995431233418725175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147791973308966578233200933 27710994995431233418725175)
    ·
      refine ⟨41566492493146850128087763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27710994995431233418725175 41566492493146850128087763)
      ·
        refine ⟨62349738739720275192131645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41566492493146850128087763 62349738739720275192131645)
        ·
          refine ⟨23381152027395103197049367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62349738739720275192131645 23381152027395103197049367)
          ·
            refine ⟨35071728041092654795574051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23381152027395103197049367 35071728041092654795574051)
            ·
              refine ⟨52607592061638982193361077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35071728041092654795574051 52607592061638982193361077)
              ·
                refine ⟨4931961755778654580627601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52607592061638982193361077 4931961755778654580627601)
                ·
                  refine ⟨3698971316833990935470701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931961755778654580627601 3698971316833990935470701)
                  ·
                    refine ⟨1387114243812746600801513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698971316833990935470701 1387114243812746600801513)
                    ·
                      rfl

theorem cell22_4052093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_4052093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052093 prefixEnd_4052093 := by exact prefixLift 4052093
  have htrace : WordTrace (prefixWord ++ tailWord_4052093) baseStart_4052093 baseEnd_4052093 := by
    simpa [prefixWord, tailWord_4052093, baseEnd_4052093] using wordTrace_append hprefix tailTrace_4052093
  have hstable : (prefixWord ++ tailWord_4052093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052093).length < 2 ^ (prefixWord ++ tailWord_4052093).sum := by decide
  have hdescent : baseEnd_4052093 < baseStart_4052093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052127 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 2, 3]
def baseStart_4052127 : Nat := 118140960795 + 4052127 * 2 ^ 59
def prefixEnd_4052127 : Nat := 4983230072969 + 3 ^ 40 * 4052127 * 2
def baseEnd_4052127 : Nat := 1387125882707581845451409

theorem tailTrace_4052127 : CollatzResearch.WordTrace tailWord_4052127 prefixEnd_4052127 1387125882707581845451409 := by
  unfold tailWord_4052127
  simp only [CollatzResearch.WordTrace]
  refine ⟨147793213390843402039938635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98528808927228934693292423 147793213390843402039938635)
  ·
    refine ⟨221689820086265103059907953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147793213390843402039938635 221689820086265103059907953)
    ·
      refine ⟨166267365064698827294930965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221689820086265103059907953 166267365064698827294930965)
      ·
        refine ⟨7793782737407757529449889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166267365064698827294930965 7793782737407757529449889)
        ·
          refine ⟨5845337053055818147087417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7793782737407757529449889 5845337053055818147087417)
          ·
            refine ⟨4384002789791863610315563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845337053055818147087417 4384002789791863610315563)
            ·
              refine ⟨6576004184687795415473345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384002789791863610315563 6576004184687795415473345)
              ·
                refine ⟨4932003138515846561605009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576004184687795415473345 4932003138515846561605009)
                ·
                  refine ⟨3699002353886884921203757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932003138515846561605009 3699002353886884921203757)
                  ·
                    refine ⟨1387125882707581845451409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699002353886884921203757 1387125882707581845451409)
                    ·
                      rfl

theorem cell22_4052127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_4052127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052127 prefixEnd_4052127 := by exact prefixLift 4052127
  have htrace : WordTrace (prefixWord ++ tailWord_4052127) baseStart_4052127 baseEnd_4052127 := by
    simpa [prefixWord, tailWord_4052127, baseEnd_4052127] using wordTrace_append hprefix tailTrace_4052127
  have hstable : (prefixWord ++ tailWord_4052127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052127).length < 2 ^ (prefixWord ++ tailWord_4052127).sum := by decide
  have hdescent : baseEnd_4052127 < baseStart_4052127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052189 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_4052189 : Nat := 118140960795 + 4052189 * 2 ^ 59
def prefixEnd_4052189 : Nat := 4983230072969 + 3 ^ 40 * 4052189 * 2
def baseEnd_4052189 : Nat := 1387147106574634350401219

theorem tailTrace_4052189 : CollatzResearch.WordTrace tailWord_4052189 prefixEnd_4052189 1387147106574634350401219 := by
  unfold tailWord_4052189
  simp only [CollatzResearch.WordTrace]
  refine ⟨147795474716618786628695621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98530316477745857752463747 147795474716618786628695621)
  ·
    refine ⟨27711651509366022492880429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147795474716618786628695621 27711651509366022492880429)
    ·
      refine ⟨10391869316012258434830161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27711651509366022492880429 10391869316012258434830161)
      ·
        refine ⟨7793901987009193826122621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10391869316012258434830161 7793901987009193826122621)
        ·
          refine ⟨2922713245128447684795983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7793901987009193826122621 2922713245128447684795983)
          ·
            refine ⟨4384069867692671527193975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2922713245128447684795983 4384069867692671527193975)
            ·
              refine ⟨6576104801539007290790963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384069867692671527193975 6576104801539007290790963)
              ·
                refine ⟨9864157202308510936186445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576104801539007290790963 9864157202308510936186445)
                ·
                  refine ⟨3699058950865691601069917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9864157202308510936186445 3699058950865691601069917)
                  ·
                    refine ⟨1387147106574634350401219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699058950865691601069917 1387147106574634350401219)
                    ·
                      rfl

theorem cell22_4052189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_4052189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052189 prefixEnd_4052189 := by exact prefixLift 4052189
  have htrace : WordTrace (prefixWord ++ tailWord_4052189) baseStart_4052189 baseEnd_4052189 := by
    simpa [prefixWord, tailWord_4052189, baseEnd_4052189] using wordTrace_append hprefix tailTrace_4052189
  have hstable : (prefixWord ++ tailWord_4052189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052189).length < 2 ^ (prefixWord ++ tailWord_4052189).sum := by decide
  have hdescent : baseEnd_4052189 < baseStart_4052189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052228 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_4052228 : Nat := 118140960795 + 4052228 * 2 ^ 59
def prefixEnd_4052228 : Nat := 4983230072969 + 3 ^ 40 * 4052228 * 2
def baseEnd_4052228 : Nat := 1387160457071651248676099

theorem tailTrace_4052228 : CollatzResearch.WordTrace tailWord_4052228 prefixEnd_4052228 1387160457071651248676099 := by
  unfold tailWord_4052228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73898448581738748144682669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98531264775651664192910225 73898448581738748144682669)
  ·
    refine ⟨27711918218152030554256001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73898448581738748144682669 27711918218152030554256001)
    ·
      refine ⟨20783938663614022915692001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27711918218152030554256001 20783938663614022915692001)
      ·
        refine ⟨15587953997710517186769001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20783938663614022915692001 15587953997710517186769001)
        ·
          refine ⟨11690965498282887890076751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15587953997710517186769001 11690965498282887890076751)
          ·
            refine ⟨17536448247424331835115127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690965498282887890076751 17536448247424331835115127)
            ·
              refine ⟨26304672371136497752672691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17536448247424331835115127 26304672371136497752672691)
              ·
                refine ⟨39457008556704746629009037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26304672371136497752672691 39457008556704746629009037)
                ·
                  refine ⟨14796378208764279985878389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39457008556704746629009037 14796378208764279985878389)
                  ·
                    refine ⟨1387160457071651248676099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796378208764279985878389 1387160457071651248676099)
                    ·
                      rfl

theorem cell22_4052228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_4052228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052228 prefixEnd_4052228 := by exact prefixLift 4052228
  have htrace : WordTrace (prefixWord ++ tailWord_4052228) baseStart_4052228 baseEnd_4052228 := by
    simpa [prefixWord, tailWord_4052228, baseEnd_4052228] using wordTrace_append hprefix tailTrace_4052228
  have hstable : (prefixWord ++ tailWord_4052228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052228).length < 2 ^ (prefixWord ++ tailWord_4052228).sum := by decide
  have hdescent : baseEnd_4052228 < baseStart_4052228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052232 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_4052232 : Nat := 118140960795 + 4052232 * 2 ^ 59
def prefixEnd_4052232 : Nat := 4983230072969 + 3 ^ 40 * 4052232 * 2
def baseEnd_4052232 : Nat := 1387161826353396571576087

theorem tailTrace_4052232 : CollatzResearch.WordTrace tailWord_4052232 prefixEnd_4052232 1387161826353396571576087 := by
  unfold tailWord_4052232
  simp only [CollatzResearch.WordTrace]
  refine ⟨73898521527731502486255475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98531362036975336648340633 73898521527731502486255475)
  ·
    refine ⟨110847782291597253729383213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73898521527731502486255475 110847782291597253729383213)
    ·
      refine ⟨41567918359348970148518705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110847782291597253729383213 41567918359348970148518705)
      ·
        refine ⟨31175938769511727611389029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41567918359348970148518705 31175938769511727611389029)
        ·
          refine ⟨5845488519283448927135443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31175938769511727611389029 5845488519283448927135443)
          ·
            refine ⟨8768232778925173390703165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845488519283448927135443 8768232778925173390703165)
            ·
              refine ⟨3288087292096940021513687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8768232778925173390703165 3288087292096940021513687)
              ·
                refine ⟨4932130938145410032270531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288087292096940021513687 4932130938145410032270531)
                ·
                  refine ⟨7398196407218115048405797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932130938145410032270531 7398196407218115048405797)
                  ·
                    refine ⟨1387161826353396571576087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398196407218115048405797 1387161826353396571576087)
                    ·
                      rfl

theorem cell22_4052232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_4052232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052232 prefixEnd_4052232 := by exact prefixLift 4052232
  have htrace : WordTrace (prefixWord ++ tailWord_4052232) baseStart_4052232 baseEnd_4052232 := by
    simpa [prefixWord, tailWord_4052232, baseEnd_4052232] using wordTrace_append hprefix tailTrace_4052232
  have hstable : (prefixWord ++ tailWord_4052232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052232).length < 2 ^ (prefixWord ++ tailWord_4052232).sum := by decide
  have hdescent : baseEnd_4052232 < baseStart_4052232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052271 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_4052271 : Nat := 118140960795 + 4052271 * 2 ^ 59
def prefixEnd_4052271 : Nat := 4983230072969 + 3 ^ 40 * 4052271 * 2
def baseEnd_4052271 : Nat := 1387175176850413469850967

theorem tailTrace_4052271 : CollatzResearch.WordTrace tailWord_4052271 prefixEnd_4052271 1387175176850413469850967 := by
  unfold tailWord_4052271
  simp only [CollatzResearch.WordTrace]
  refine ⟨147798465502321714633180667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98532310334881143088787111 147798465502321714633180667)
  ·
    refine ⟨221697698253482571949771001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147798465502321714633180667 221697698253482571949771001)
    ·
      refine ⟨166273273690111928962328251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221697698253482571949771001 166273273690111928962328251)
      ·
        refine ⟨249409910535167893443492377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166273273690111928962328251 249409910535167893443492377)
        ·
          refine ⟨187057432901375920082619283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249409910535167893443492377 187057432901375920082619283)
          ·
            refine ⟨280586149352063880123928925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187057432901375920082619283 280586149352063880123928925)
            ·
              refine ⟨105219806007023955046473347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280586149352063880123928925 105219806007023955046473347)
              ·
                refine ⟨157829709010535932569710021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105219806007023955046473347 157829709010535932569710021)
                ·
                  refine ⟨29593070439475487356820629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157829709010535932569710021 29593070439475487356820629)
                  ·
                    refine ⟨1387175176850413469850967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29593070439475487356820629 1387175176850413469850967)
                    ·
                      rfl

theorem cell22_4052271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_4052271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052271 prefixEnd_4052271 := by exact prefixLift 4052271
  have htrace : WordTrace (prefixWord ++ tailWord_4052271) baseStart_4052271 baseEnd_4052271 := by
    simpa [prefixWord, tailWord_4052271, baseEnd_4052271] using wordTrace_append hprefix tailTrace_4052271
  have hstable : (prefixWord ++ tailWord_4052271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052271).length < 2 ^ (prefixWord ++ tailWord_4052271).sum := by decide
  have hdescent : baseEnd_4052271 < baseStart_4052271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052341 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4052341 : Nat := 118140960795 + 4052341 * 2 ^ 59
def prefixEnd_4052341 : Nat := 4983230072969 + 3 ^ 40 * 4052341 * 2
def baseEnd_4052341 : Nat := 1387199139280956620600753

theorem tailTrace_4052341 : CollatzResearch.WordTrace tailWord_4052341 prefixEnd_4052341 1387199139280956620600753 := by
  unfold tailWord_4052341
  simp only [CollatzResearch.WordTrace]
  refine ⟨147801018612068116588228877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98534012408045411058819251 147801018612068116588228877)
  ·
    refine ⟨55425381979525543720585829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147801018612068116588228877 55425381979525543720585829)
    ·
      refine ⟨10392259121161039447609843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55425381979525543720585829 10392259121161039447609843)
      ·
        refine ⟨15588388681741559171414765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10392259121161039447609843 15588388681741559171414765)
        ·
          refine ⟨5845645755653084689280537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15588388681741559171414765 5845645755653084689280537)
          ·
            refine ⟨4384234316739813516960403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845645755653084689280537 4384234316739813516960403)
            ·
              refine ⟨6576351475109720275440605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384234316739813516960403 6576351475109720275440605)
              ·
                refine ⟨2466131803166145103290227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6576351475109720275440605 2466131803166145103290227)
                ·
                  refine ⟨3699197704749217654935341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466131803166145103290227 3699197704749217654935341)
                  ·
                    refine ⟨1387199139280956620600753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699197704749217654935341 1387199139280956620600753)
                    ·
                      rfl

theorem cell22_4052341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4052341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052341 prefixEnd_4052341 := by exact prefixLift 4052341
  have htrace : WordTrace (prefixWord ++ tailWord_4052341) baseStart_4052341 baseEnd_4052341 := by
    simpa [prefixWord, tailWord_4052341, baseEnd_4052341] using wordTrace_append hprefix tailTrace_4052341
  have hstable : (prefixWord ++ tailWord_4052341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052341).length < 2 ^ (prefixWord ++ tailWord_4052341).sum := by decide
  have hdescent : baseEnd_4052341 < baseStart_4052341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052397 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4052397 : Nat := 118140960795 + 4052397 * 2 ^ 59
def prefixEnd_4052397 : Nat := 4983230072969 + 3 ^ 40 * 4052397 * 2
def baseEnd_4052397 : Nat := 1387218309225391141200581

theorem tailTrace_4052397 : CollatzResearch.WordTrace tailWord_4052397 prefixEnd_4052397 1387218309225391141200581 := by
  unfold tailWord_4052397
  simp only [CollatzResearch.WordTrace]
  refine ⟨147803061099865238152267445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98535374066576825434844963 147803061099865238152267445)
  ·
    refine ⟨13856536978112366076775073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147803061099865238152267445 13856536978112366076775073)
    ·
      refine ⟨10392402733584274557581305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13856536978112366076775073 10392402733584274557581305)
      ·
        refine ⟨7794302050188205918185979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10392402733584274557581305 7794302050188205918185979)
        ·
          refine ⟨11691453075282308877278969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794302050188205918185979 11691453075282308877278969)
          ·
            refine ⟨8768589806461731657959227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11691453075282308877278969 8768589806461731657959227)
            ·
              refine ⟨13152884709692597486938841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768589806461731657959227 13152884709692597486938841)
              ·
                refine ⟨9864663532269448115204131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13152884709692597486938841 9864663532269448115204131)
                ·
                  refine ⟨14796995298404172172806197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864663532269448115204131 14796995298404172172806197)
                  ·
                    refine ⟨1387218309225391141200581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796995298404172172806197 1387218309225391141200581)
                    ·
                      rfl

theorem cell22_4052397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4052397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052397 prefixEnd_4052397 := by exact prefixLift 4052397
  have htrace : WordTrace (prefixWord ++ tailWord_4052397) baseStart_4052397 baseEnd_4052397 := by
    simpa [prefixWord, tailWord_4052397, baseEnd_4052397] using wordTrace_append hprefix tailTrace_4052397
  have hstable : (prefixWord ++ tailWord_4052397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052397).length < 2 ^ (prefixWord ++ tailWord_4052397).sum := by decide
  have hdescent : baseEnd_4052397 < baseStart_4052397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052423 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_4052423 : Nat := 118140960795 + 4052423 * 2 ^ 59
def prefixEnd_4052423 : Nat := 4983230072969 + 3 ^ 40 * 4052423 * 2
def baseEnd_4052423 : Nat := 1387227209556735740050501

theorem tailTrace_4052423 : CollatzResearch.WordTrace tailWord_4052423 prefixEnd_4052423 1387227209556735740050501 := by
  unfold tailWord_4052423
  simp only [CollatzResearch.WordTrace]
  refine ⟨147804009397771044592713923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98536006265180696395142615 147804009397771044592713923)
  ·
    refine ⟨221706014096656566889070885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147804009397771044592713923 221706014096656566889070885)
    ·
      refine ⟨41569877643123106291700791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221706014096656566889070885 41569877643123106291700791)
      ·
        refine ⟨62354816464684659437551187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41569877643123106291700791 62354816464684659437551187)
        ·
          refine ⟨93532224697026989156326781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62354816464684659437551187 93532224697026989156326781)
          ·
            refine ⟨35074584261385120933622543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93532224697026989156326781 35074584261385120933622543)
            ·
              refine ⟨52611876392077681400433815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35074584261385120933622543 52611876392077681400433815)
              ·
                refine ⟨78917814588116522100650723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52611876392077681400433815 78917814588116522100650723)
                ·
                  refine ⟨118376721882174783150976085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78917814588116522100650723 118376721882174783150976085)
                  ·
                    refine ⟨1387227209556735740050501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118376721882174783150976085 1387227209556735740050501)
                    ·
                      rfl

theorem cell22_4052423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_4052423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052423 prefixEnd_4052423 := by exact prefixLift 4052423
  have htrace : WordTrace (prefixWord ++ tailWord_4052423) baseStart_4052423 baseEnd_4052423 := by
    simpa [prefixWord, tailWord_4052423, baseEnd_4052423] using wordTrace_append hprefix tailTrace_4052423
  have hstable : (prefixWord ++ tailWord_4052423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052423).length < 2 ^ (prefixWord ++ tailWord_4052423).sum := by decide
  have hdescent : baseEnd_4052423 < baseStart_4052423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052425 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_4052425 : Nat := 118140960795 + 4052425 * 2 ^ 59
def prefixEnd_4052425 : Nat := 4983230072969 + 3 ^ 40 * 4052425 * 2
def baseEnd_4052425 : Nat := 1387227894197608401500495

theorem tailTrace_4052425 : CollatzResearch.WordTrace tailWord_4052425 prefixEnd_4052425 1387227894197608401500495 := by
  unfold tailWord_4052425
  simp only [CollatzResearch.WordTrace]
  refine ⟨147804082343763798934286729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98536054895842532622857819 147804082343763798934286729)
  ·
    refine ⟨110853061757822849200715047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147804082343763798934286729 110853061757822849200715047)
    ·
      refine ⟨166279592636734273801072571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110853061757822849200715047 166279592636734273801072571)
      ·
        refine ⟨249419388955101410701608857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166279592636734273801072571 249419388955101410701608857)
        ·
          refine ⟨187064541716326058026206643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249419388955101410701608857 187064541716326058026206643)
          ·
            refine ⟨280596812574489087039309965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187064541716326058026206643 280596812574489087039309965)
            ·
              refine ⟨105223804715433407639741237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280596812574489087039309965 105223804715433407639741237)
              ·
                refine ⟨9864731692071881966225741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105223804715433407639741237 9864731692071881966225741)
                ·
                  refine ⟨3699274384526955737334653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9864731692071881966225741 3699274384526955737334653)
                  ·
                    refine ⟨1387227894197608401500495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699274384526955737334653 1387227894197608401500495)
                    ·
                      rfl

theorem cell22_4052425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_4052425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052425 prefixEnd_4052425 := by exact prefixLift 4052425
  have htrace : WordTrace (prefixWord ++ tailWord_4052425) baseStart_4052425 baseEnd_4052425 := by
    simpa [prefixWord, tailWord_4052425, baseEnd_4052425] using wordTrace_append hprefix tailTrace_4052425
  have hstable : (prefixWord ++ tailWord_4052425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052425).length < 2 ^ (prefixWord ++ tailWord_4052425).sum := by decide
  have hdescent : baseEnd_4052425 < baseStart_4052425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052442 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_4052442 : Nat := 118140960795 + 4052442 * 2 ^ 59
def prefixEnd_4052442 : Nat := 4983230072969 + 3 ^ 40 * 4052442 * 2
def baseEnd_4052442 : Nat := 1387233713645026023825443

theorem tailTrace_4052442 : CollatzResearch.WordTrace tailWord_4052442 prefixEnd_4052442 1387233713645026023825443 := by
  unfold tailWord_4052442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36951175596175552709413895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98536468256468140558437053 36951175596175552709413895)
  ·
    refine ⟨55426763394263329064120843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36951175596175552709413895 55426763394263329064120843)
    ·
      refine ⟨83140145091394993596181265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55426763394263329064120843 83140145091394993596181265)
      ·
        refine ⟨62355108818546245197135949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83140145091394993596181265 62355108818546245197135949)
        ·
          refine ⟨23383165806954841948925981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62355108818546245197135949 23383165806954841948925981)
          ·
            refine ⟨8768687177608065730847243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23383165806954841948925981 8768687177608065730847243)
            ·
              refine ⟨13153030766412098596270865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768687177608065730847243 13153030766412098596270865)
              ·
                refine ⟨9864773074809073947203149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13153030766412098596270865 9864773074809073947203149)
                ·
                  refine ⟨3699289903053402730201181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9864773074809073947203149 3699289903053402730201181)
                  ·
                    refine ⟨1387233713645026023825443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699289903053402730201181 1387233713645026023825443)
                    ·
                      rfl

theorem cell22_4052442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_4052442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052442 prefixEnd_4052442 := by exact prefixLift 4052442
  have htrace : WordTrace (prefixWord ++ tailWord_4052442) baseStart_4052442 baseEnd_4052442 := by
    simpa [prefixWord, tailWord_4052442, baseEnd_4052442] using wordTrace_append hprefix tailTrace_4052442
  have hstable : (prefixWord ++ tailWord_4052442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052442).length < 2 ^ (prefixWord ++ tailWord_4052442).sum := by decide
  have hdescent : baseEnd_4052442 < baseStart_4052442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052472 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_4052472 : Nat := 118140960795 + 4052472 * 2 ^ 59
def prefixEnd_4052472 : Nat := 4983230072969 + 3 ^ 40 * 4052472 * 2
def baseEnd_4052472 : Nat := 462414661086038648525117

theorem tailTrace_4052472 : CollatzResearch.WordTrace tailWord_4052472 prefixEnd_4052472 462414661086038648525117 := by
  unfold tailWord_4052472
  simp only [CollatzResearch.WordTrace]
  refine ⟨73902898287296762980623835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98537197716395683974165113 73902898287296762980623835)
  ·
    refine ⟨110854347430945144470935753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73902898287296762980623835 110854347430945144470935753)
    ·
      refine ⟨83140760573208858353201815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110854347430945144470935753 83140760573208858353201815)
      ·
        refine ⟨124711140859813287529802723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83140760573208858353201815 124711140859813287529802723)
        ·
          refine ⟨187066711289719931294704085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124711140859813287529802723 187066711289719931294704085)
          ·
            refine ⟨4384376045852810889719627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 187066711289719931294704085 4384376045852810889719627)
            ·
              refine ⟨6576564068779216334579441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384376045852810889719627 6576564068779216334579441)
              ·
                refine ⟨4932423051584412250934581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576564068779216334579441 4932423051584412250934581)
                ·
                  refine ⟨462414661086038648525117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4932423051584412250934581 462414661086038648525117)
                  ·
                    rfl

theorem cell22_4052472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_4052472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052472 prefixEnd_4052472 := by exact prefixLift 4052472
  have htrace : WordTrace (prefixWord ++ tailWord_4052472) baseStart_4052472 baseEnd_4052472 := by
    simpa [prefixWord, tailWord_4052472, baseEnd_4052472] using wordTrace_append hprefix tailTrace_4052472
  have hstable : (prefixWord ++ tailWord_4052472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052472).length < 2 ^ (prefixWord ++ tailWord_4052472).sum := by decide
  have hdescent : baseEnd_4052472 < baseStart_4052472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052697 : List Nat := [1, 2, 1, 2, 3, 5, 8]
def baseStart_4052697 : Nat := 118140960795 + 4052697 * 2 ^ 59
def prefixEnd_4052697 : Nat := 4983230072969 + 3 ^ 40 * 4052697 * 2
def baseEnd_4052697 : Nat := 51382259457640383655543

theorem tailTrace_4052697 : CollatzResearch.WordTrace tailWord_4052697 prefixEnd_4052697 51382259457640383655543 := by
  unfold tailWord_4052697
  simp only [CollatzResearch.WordTrace]
  refine ⟨147814002998778389388188345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98542668665852259592125563 147814002998778389388188345)
  ·
    refine ⟨110860502249083792041141259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147814002998778389388188345 110860502249083792041141259)
    ·
      refine ⟨166290753373625688061711889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110860502249083792041141259 166290753373625688061711889)
      ·
        refine ⟨124718065030219266046283917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166290753373625688061711889 124718065030219266046283917)
        ·
          refine ⟨46769274386332224767356469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124718065030219266046283917 46769274386332224767356469)
          ·
            refine ⟨4384619473718646071939669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46769274386332224767356469 4384619473718646071939669)
            ·
              refine ⟨51382259457640383655543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4384619473718646071939669 51382259457640383655543)
              ·
                rfl

theorem cell22_4052697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 8].length) (baseStart_4052697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052697 prefixEnd_4052697 := by exact prefixLift 4052697
  have htrace : WordTrace (prefixWord ++ tailWord_4052697) baseStart_4052697 baseEnd_4052697 := by
    simpa [prefixWord, tailWord_4052697, baseEnd_4052697] using wordTrace_append hprefix tailTrace_4052697
  have hstable : (prefixWord ++ tailWord_4052697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052697).length < 2 ^ (prefixWord ++ tailWord_4052697).sum := by decide
  have hdescent : baseEnd_4052697 < baseStart_4052697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052759 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 5]
def baseStart_4052759 : Nat := 118140960795 + 4052759 * 2 ^ 59
def prefixEnd_4052759 : Nat := 4983230072969 + 3 ^ 40 * 4052759 * 2
def baseEnd_4052759 : Nat := 462447409741114287883157

theorem tailTrace_4052759 : CollatzResearch.WordTrace tailWord_4052759 prefixEnd_4052759 462447409741114287883157 := by
  unfold tailWord_4052759
  simp only [CollatzResearch.WordTrace]
  refine ⟨147816264324553773976945331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98544176216369182651296887 147816264324553773976945331)
  ·
    refine ⟨221724396486830660965417997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147816264324553773976945331 221724396486830660965417997)
    ·
      refine ⟨83146648682561497862031749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221724396486830660965417997 83146648682561497862031749)
      ·
        refine ⟨15589996627980280849130953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83146648682561497862031749 15589996627980280849130953)
        ·
          refine ⟨11692497470985210636848215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15589996627980280849130953 11692497470985210636848215)
          ·
            refine ⟨17538746206477815955272323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11692497470985210636848215 17538746206477815955272323)
            ·
              refine ⟨26308119309716723932908485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17538746206477815955272323 26308119309716723932908485)
              ·
                refine ⟨4932772370571885737420341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26308119309716723932908485 4932772370571885737420341)
                ·
                  refine ⟨462447409741114287883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4932772370571885737420341 462447409741114287883157)
                  ·
                    rfl

theorem cell22_4052759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 5].length) (baseStart_4052759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052759 prefixEnd_4052759 := by exact prefixLift 4052759
  have htrace : WordTrace (prefixWord ++ tailWord_4052759) baseStart_4052759 baseEnd_4052759 := by
    simpa [prefixWord, tailWord_4052759, baseEnd_4052759] using wordTrace_append hprefix tailTrace_4052759
  have hstable : (prefixWord ++ tailWord_4052759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052759).length < 2 ^ (prefixWord ++ tailWord_4052759).sum := by decide
  have hdescent : baseEnd_4052759 < baseStart_4052759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052821 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 4]
def baseStart_4052821 : Nat := 118140960795 + 4052821 * 2 ^ 59
def prefixEnd_4052821 : Nat := 4983230072969 + 3 ^ 40 * 4052821 * 2
def baseEnd_4052821 : Nat := 462454484363465122866427

theorem tailTrace_4052821 : CollatzResearch.WordTrace tailWord_4052821 prefixEnd_4052821 462454484363465122866427 := by
  unfold tailWord_4052821
  simp only [CollatzResearch.WordTrace]
  refine ⟨147818525650329158565702317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98545683766886105710468211 147818525650329158565702317)
  ·
    refine ⟨55431947118873434462138369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147818525650329158565702317 55431947118873434462138369)
    ·
      refine ⟨41573960339155075846603777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55431947118873434462138369 41573960339155075846603777)
      ·
        refine ⟨31180470254366306884952833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41573960339155075846603777 31180470254366306884952833)
        ·
          refine ⟨23385352690774730163714625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31180470254366306884952833 23385352690774730163714625)
          ·
            refine ⟨17539014518081047622785969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23385352690774730163714625 17539014518081047622785969)
            ·
              refine ⟨13154260888560785717089477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17539014518081047622785969 13154260888560785717089477)
              ·
                refine ⟨2466423916605147321954277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13154260888560785717089477 2466423916605147321954277)
                ·
                  refine ⟨462454484363465122866427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466423916605147321954277 462454484363465122866427)
                  ·
                    rfl

theorem cell22_4052821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_4052821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052821 prefixEnd_4052821 := by exact prefixLift 4052821
  have htrace : WordTrace (prefixWord ++ tailWord_4052821) baseStart_4052821 baseEnd_4052821 := by
    simpa [prefixWord, tailWord_4052821, baseEnd_4052821] using wordTrace_append hprefix tailTrace_4052821
  have hstable : (prefixWord ++ tailWord_4052821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052821).length < 2 ^ (prefixWord ++ tailWord_4052821).sum := by decide
  have hdescent : baseEnd_4052821 < baseStart_4052821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052881 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_4052881 : Nat := 118140960795 + 4052881 * 2 ^ 59
def prefixEnd_4052881 : Nat := 4983230072969 + 3 ^ 40 * 4052881 * 2
def baseEnd_4052881 : Nat := 1387383992316575212099097

theorem tailTrace_4052881 : CollatzResearch.WordTrace tailWord_4052881 prefixEnd_4052881 1387383992316575212099097 := by
  unfold tailWord_4052881
  simp only [CollatzResearch.WordTrace]
  refine ⟨147820714030111788812886497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98547142686741192541924331 147820714030111788812886497)
  ·
    refine ⟨110865535522583841609664873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147820714030111788812886497 110865535522583841609664873)
    ·
      refine ⟨83149151641937881207248655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110865535522583841609664873 83149151641937881207248655)
      ·
        refine ⟨124723727462906821810872983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83149151641937881207248655 124723727462906821810872983)
        ·
          refine ⟨187085591194360232716309475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124723727462906821810872983 187085591194360232716309475)
          ·
            refine ⟨280628386791540349074464213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187085591194360232716309475 280628386791540349074464213)
            ·
              refine ⟨6577227815426726931432755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 280628386791540349074464213 6577227815426726931432755)
              ·
                refine ⟨9865841723140090397149133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577227815426726931432755 9865841723140090397149133)
                ·
                  refine ⟨3699690646177533898930925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9865841723140090397149133 3699690646177533898930925)
                  ·
                    refine ⟨1387383992316575212099097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699690646177533898930925 1387383992316575212099097)
                    ·
                      rfl

theorem cell22_4052881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_4052881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052881 prefixEnd_4052881 := by exact prefixLift 4052881
  have htrace : WordTrace (prefixWord ++ tailWord_4052881) baseStart_4052881 baseEnd_4052881 := by
    simpa [prefixWord, tailWord_4052881, baseEnd_4052881] using wordTrace_append hprefix tailTrace_4052881
  have hstable : (prefixWord ++ tailWord_4052881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052881).length < 2 ^ (prefixWord ++ tailWord_4052881).sum := by decide
  have hdescent : baseEnd_4052881 < baseStart_4052881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052939 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 6]
def baseStart_4052939 : Nat := 118140960795 + 4052939 * 2 ^ 59
def prefixEnd_4052939 : Nat := 4983230072969 + 3 ^ 40 * 4052939 * 2
def baseEnd_4052939 : Nat := 462467948967294131382973

theorem tailTrace_4052939 : CollatzResearch.WordTrace tailWord_4052939 prefixEnd_4052939 462467948967294131382973 := by
  unfold tailWord_4052939
  simp only [CollatzResearch.WordTrace]
  refine ⟨147822829463901664718497871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98548552975934443145665247 147822829463901664718497871)
  ·
    refine ⟨221734244195852497077746807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147822829463901664718497871 221734244195852497077746807)
    ·
      refine ⟨332601366293778745616620211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221734244195852497077746807 332601366293778745616620211)
      ·
        refine ⟨498902049440668118424930317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332601366293778745616620211 498902049440668118424930317)
        ·
          refine ⟨187088268540250544409348869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498902049440668118424930317 187088268540250544409348869)
          ·
            refine ⟨35079050351296977076752913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187088268540250544409348869 35079050351296977076752913)
            ·
              refine ⟨26309287763472732807564685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35079050351296977076752913 26309287763472732807564685)
              ·
                refine ⟨9865982911302274802836757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26309287763472732807564685 9865982911302274802836757)
                ·
                  refine ⟨462467948967294131382973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9865982911302274802836757 462467948967294131382973)
                  ·
                    rfl

theorem cell22_4052939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_4052939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052939 prefixEnd_4052939 := by exact prefixLift 4052939
  have htrace : WordTrace (prefixWord ++ tailWord_4052939) baseStart_4052939 baseEnd_4052939 := by
    simpa [prefixWord, tailWord_4052939, baseEnd_4052939] using wordTrace_append hprefix tailTrace_4052939
  have hstable : (prefixWord ++ tailWord_4052939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052939).length < 2 ^ (prefixWord ++ tailWord_4052939).sum := by decide
  have hdescent : baseEnd_4052939 < baseStart_4052939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4052990 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_4052990 : Nat := 118140960795 + 4052990 * 2 ^ 59
def prefixEnd_4052990 : Nat := 4983230072969 + 3 ^ 40 * 4052990 * 2
def baseEnd_4052990 : Nat := 462473768414711753707921

theorem tailTrace_4052990 : CollatzResearch.WordTrace tailWord_4052990 prefixEnd_4052990 462473768414711753707921 := by
  unfold tailWord_4052990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478086198339612553575553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98549793057811266952402949 18478086198339612553575553)
  ·
    refine ⟨13858564648754709415181665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18478086198339612553575553 13858564648754709415181665)
    ·
      refine ⟨10393923486566032061386249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13858564648754709415181665 10393923486566032061386249)
      ·
        refine ⟨7795442614924524046039687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10393923486566032061386249 7795442614924524046039687)
        ·
          refine ⟨11693163922386786069059531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7795442614924524046039687 11693163922386786069059531)
          ·
            refine ⟨17539745883580179103589297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693163922386786069059531 17539745883580179103589297)
            ·
              refine ⟨13154809412685134327691973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17539745883580179103589297 13154809412685134327691973)
              ·
                refine ⟨2466526764878462686442245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13154809412685134327691973 2466526764878462686442245)
                ·
                  refine ⟨462473768414711753707921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466526764878462686442245 462473768414711753707921)
                  ·
                    rfl

theorem cell22_4052990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_4052990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4052990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4052990 prefixEnd_4052990 := by exact prefixLift 4052990
  have htrace : WordTrace (prefixWord ++ tailWord_4052990) baseStart_4052990 baseEnd_4052990 := by
    simpa [prefixWord, tailWord_4052990, baseEnd_4052990] using wordTrace_append hprefix tailTrace_4052990
  have hstable : (prefixWord ++ tailWord_4052990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4052990).length < 2 ^ (prefixWord ++ tailWord_4052990).sum := by decide
  have hdescent : baseEnd_4052990 < baseStart_4052990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4052990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053018 : List Nat := [3, 1, 1, 3, 1, 5, 2, 6]
def baseStart_4053018 : Nat := 118140960795 + 4053018 * 2 ^ 59
def prefixEnd_4053018 : Nat := 4983230072969 + 3 ^ 40 * 4053018 * 2
def baseEnd_4053018 : Nat := 154158987801816946824853

theorem tailTrace_4053018 : CollatzResearch.WordTrace tailWord_4053018 prefixEnd_4053018 154158987801816946824853 := by
  unfold tailWord_4053018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956427707653865302655927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98550473887076974140415805 36956427707653865302655927)
  ·
    refine ⟨55434641561480797953983891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36956427707653865302655927 55434641561480797953983891)
    ·
      refine ⟨83151962342221196930975837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55434641561480797953983891 83151962342221196930975837)
      ·
        refine ⟨31181985878332948849115939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83151962342221196930975837 31181985878332948849115939)
        ·
          refine ⟨46772978817499423273673909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31181985878332948849115939 46772978817499423273673909)
          ·
            refine ⟨4384966764140570931906929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46772978817499423273673909 4384966764140570931906929)
            ·
              refine ⟨3288725073105428198930197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4384966764140570931906929 3288725073105428198930197)
              ·
                refine ⟨154158987801816946824853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3288725073105428198930197 154158987801816946824853)
                ·
                  rfl

theorem cell22_4053018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_4053018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053018 prefixEnd_4053018 := by exact prefixLift 4053018
  have htrace : WordTrace (prefixWord ++ tailWord_4053018) baseStart_4053018 baseEnd_4053018 := by
    simpa [prefixWord, tailWord_4053018, baseEnd_4053018] using wordTrace_append hprefix tailTrace_4053018
  have hstable : (prefixWord ++ tailWord_4053018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053018).length < 2 ^ (prefixWord ++ tailWord_4053018).sum := by decide
  have hdescent : baseEnd_4053018 < baseStart_4053018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053123 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 1, 5]
def baseStart_4053123 : Nat := 118140960795 + 4053123 * 2 ^ 59
def prefixEnd_4053123 : Nat := 4983230072969 + 3 ^ 40 * 4053123 * 2
def baseEnd_4053123 : Nat := 1387466833862167247548355

theorem tailTrace_4053123 : CollatzResearch.WordTrace tailWord_4053123 prefixEnd_4053123 1387466833862167247548355 := by
  unfold tailWord_4053123
  simp only [CollatzResearch.WordTrace]
  refine ⟨147829540495235064143196023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98553026996823376095464015 147829540495235064143196023)
  ·
    refine ⟨221744310742852596214794035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147829540495235064143196023 221744310742852596214794035)
    ·
      refine ⟨332616466114278894322191053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221744310742852596214794035 332616466114278894322191053)
      ·
        refine ⟨124731174792854585370821645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332616466114278894322191053 124731174792854585370821645)
        ·
          refine ⟨46774190547320469514058117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124731174792854585370821645 46774190547320469514058117)
          ·
            refine ⟨8770160727622588033885897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46774190547320469514058117 8770160727622588033885897)
            ·
              refine ⟨6577620545716941025414423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770160727622588033885897 6577620545716941025414423)
              ·
                refine ⟨9866430818575411538121635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577620545716941025414423 9866430818575411538121635)
                ·
                  refine ⟨14799646227863117307182453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866430818575411538121635 14799646227863117307182453)
                  ·
                    refine ⟨1387466833862167247548355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14799646227863117307182453 1387466833862167247548355)
                    ·
                      rfl

theorem cell22_4053123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_4053123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053123 prefixEnd_4053123 := by exact prefixLift 4053123
  have htrace : WordTrace (prefixWord ++ tailWord_4053123) baseStart_4053123 baseEnd_4053123 := by
    simpa [prefixWord, tailWord_4053123, baseEnd_4053123] using wordTrace_append hprefix tailTrace_4053123
  have hstable : (prefixWord ++ tailWord_4053123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053123).length < 2 ^ (prefixWord ++ tailWord_4053123).sum := by decide
  have hdescent : baseEnd_4053123 < baseStart_4053123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053138 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_4053138 : Nat := 118140960795 + 4053138 * 2 ^ 59
def prefixEnd_4053138 : Nat := 4983230072969 + 3 ^ 40 * 4053138 * 2
def baseEnd_4053138 : Nat := 1387471968668712208423309

theorem tailTrace_4053138 : CollatzResearch.WordTrace tailWord_4053138 prefixEnd_4053138 1387471968668712208423309 := by
  unfold tailWord_4053138
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957521897545180426248017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98553391726787147803328045 36957521897545180426248017)
  ·
    refine ⟨27718141423158885319686013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36957521897545180426248017 27718141423158885319686013)
    ·
      refine ⟨10394303033684581994882255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27718141423158885319686013 10394303033684581994882255)
      ·
        refine ⟨15591454550526872992323383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10394303033684581994882255 15591454550526872992323383)
        ·
          refine ⟨23387181825790309488485075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15591454550526872992323383 23387181825790309488485075)
          ·
            refine ⟨35080772738685464232727613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23387181825790309488485075 35080772738685464232727613)
            ·
              refine ⟨13155289777007049087272855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35080772738685464232727613 13155289777007049087272855)
              ·
                refine ⟨19732934665510573630909283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13155289777007049087272855 19732934665510573630909283)
                ·
                  refine ⟨29599401998265860446363925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19732934665510573630909283 29599401998265860446363925)
                  ·
                    refine ⟨1387471968668712208423309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29599401998265860446363925 1387471968668712208423309)
                    ·
                      rfl

theorem cell22_4053138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_4053138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053138 prefixEnd_4053138 := by exact prefixLift 4053138
  have htrace : WordTrace (prefixWord ++ tailWord_4053138) baseStart_4053138 baseEnd_4053138 := by
    simpa [prefixWord, tailWord_4053138, baseEnd_4053138] using wordTrace_append hprefix tailTrace_4053138
  have hstable : (prefixWord ++ tailWord_4053138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053138).length < 2 ^ (prefixWord ++ tailWord_4053138).sum := by decide
  have hdescent : baseEnd_4053138 < baseStart_4053138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053144 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_4053144 : Nat := 118140960795 + 4053144 * 2 ^ 59
def prefixEnd_4053144 : Nat := 4983230072969 + 3 ^ 40 * 4053144 * 2
def baseEnd_4053144 : Nat := 1387474022591330192773291

theorem tailTrace_4053144 : CollatzResearch.WordTrace tailWord_4053144 prefixEnd_4053144 1387474022591330192773291 := by
  unfold tailWord_4053144
  simp only [CollatzResearch.WordTrace]
  refine ⟨73915153214079492364855243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98553537618772656486473657 73915153214079492364855243)
  ·
    refine ⟨110872729821119238547282865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73915153214079492364855243 110872729821119238547282865)
    ·
      refine ⟨83154547365839428910462149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110872729821119238547282865 83154547365839428910462149)
      ·
        refine ⟨15591477631094892920711653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83154547365839428910462149 15591477631094892920711653)
        ·
          refine ⟨2923402055830292422633435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15591477631094892920711653 2923402055830292422633435)
          ·
            refine ⟨4385103083745438633950153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923402055830292422633435 4385103083745438633950153)
            ·
              refine ⟨3288827312809078975462615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385103083745438633950153 3288827312809078975462615)
              ·
                refine ⟨4933240969213618463193923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288827312809078975462615 4933240969213618463193923)
                ·
                  refine ⟨7399861453820427694790885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933240969213618463193923 7399861453820427694790885)
                  ·
                    refine ⟨1387474022591330192773291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7399861453820427694790885 1387474022591330192773291)
                    ·
                      rfl

theorem cell22_4053144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_4053144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053144 prefixEnd_4053144 := by exact prefixLift 4053144
  have htrace : WordTrace (prefixWord ++ tailWord_4053144) baseStart_4053144 baseEnd_4053144 := by
    simpa [prefixWord, tailWord_4053144, baseEnd_4053144] using wordTrace_append hprefix tailTrace_4053144
  have hstable : (prefixWord ++ tailWord_4053144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053144).length < 2 ^ (prefixWord ++ tailWord_4053144).sum := by decide
  have hdescent : baseEnd_4053144 < baseStart_4053144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053198 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_4053198 : Nat := 118140960795 + 4053198 * 2 ^ 59
def prefixEnd_4053198 : Nat := 4983230072969 + 3 ^ 40 * 4053198 * 2
def baseEnd_4053198 : Nat := 462497502631630683974375

theorem tailTrace_4053198 : CollatzResearch.WordTrace tailWord_4053198 prefixEnd_4053198 462497502631630683974375 := by
  unfold tailWord_4053198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479034496245418994022031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98554850646642234634784165 18479034496245418994022031)
  ·
    refine ⟨27718551744368128491033047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18479034496245418994022031 27718551744368128491033047)
    ·
      refine ⟨41577827616552192736549571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27718551744368128491033047 41577827616552192736549571)
      ·
        refine ⟨62366741424828289104824357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41577827616552192736549571 62366741424828289104824357)
        ·
          refine ⟨11693764017155304207154567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62366741424828289104824357 11693764017155304207154567)
          ·
            refine ⟨17540646025732956310731851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693764017155304207154567 17540646025732956310731851)
            ·
              refine ⟨26310969038599434466097777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17540646025732956310731851 26310969038599434466097777)
              ·
                refine ⟨19733226778949575849573333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26310969038599434466097777 19733226778949575849573333)
                ·
                  refine ⟨462497502631630683974375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19733226778949575849573333 462497502631630683974375)
                  ·
                    rfl

theorem cell22_4053198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_4053198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053198 prefixEnd_4053198 := by exact prefixLift 4053198
  have htrace : WordTrace (prefixWord ++ tailWord_4053198) baseStart_4053198 baseEnd_4053198 := by
    simpa [prefixWord, tailWord_4053198, baseEnd_4053198] using wordTrace_append hprefix tailTrace_4053198
  have hstable : (prefixWord ++ tailWord_4053198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053198).length < 2 ^ (prefixWord ++ tailWord_4053198).sum := by decide
  have hdescent : baseEnd_4053198 < baseStart_4053198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053219 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 3, 3]
def baseStart_4053219 : Nat := 118140960795 + 4053219 * 2 ^ 59
def prefixEnd_4053219 : Nat := 4983230072969 + 3 ^ 40 * 4053219 * 2
def baseEnd_4053219 : Nat := 1387499696624054997148061

theorem tailTrace_4053219 : CollatzResearch.WordTrace tailWord_4053219 prefixEnd_4053219 1387499696624054997148061 := by
  unfold tailWord_4053219
  simp only [CollatzResearch.WordTrace]
  refine ⟨147833041902887272538690711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98555361268591515025793807 147833041902887272538690711)
  ·
    refine ⟨221749562854330908808036067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147833041902887272538690711 221749562854330908808036067)
    ·
      refine ⟨332624344281496363212054101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221749562854330908808036067 332624344281496363212054101)
      ·
        refine ⟨3897941534548785506391259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 332624344281496363212054101 3897941534548785506391259)
        ·
          refine ⟨5846912301823178259586889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897941534548785506391259 5846912301823178259586889)
          ·
            refine ⟨4385184226367383694690167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846912301823178259586889 4385184226367383694690167)
            ·
              refine ⟨6577776339551075542035251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385184226367383694690167 6577776339551075542035251)
              ·
                refine ⟨9866664509326613313052877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577776339551075542035251 9866664509326613313052877)
                ·
                  refine ⟨3699999190997479992394829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9866664509326613313052877 3699999190997479992394829)
                  ·
                    refine ⟨1387499696624054997148061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699999190997479992394829 1387499696624054997148061)
                    ·
                      rfl

theorem cell22_4053219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3].length) (baseStart_4053219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053219 prefixEnd_4053219 := by exact prefixLift 4053219
  have htrace : WordTrace (prefixWord ++ tailWord_4053219) baseStart_4053219 baseEnd_4053219 := by
    simpa [prefixWord, tailWord_4053219, baseEnd_4053219] using wordTrace_append hprefix tailTrace_4053219
  have hstable : (prefixWord ++ tailWord_4053219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053219).length < 2 ^ (prefixWord ++ tailWord_4053219).sum := by decide
  have hdescent : baseEnd_4053219 < baseStart_4053219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053228 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_4053228 : Nat := 118140960795 + 4053228 * 2 ^ 59
def prefixEnd_4053228 : Nat := 4983230072969 + 3 ^ 40 * 4053228 * 2
def baseEnd_4053228 : Nat := 1387502777507981973673033

theorem tailTrace_4053228 : CollatzResearch.WordTrace tailWord_4053228 prefixEnd_4053228 1387502777507981973673033 := by
  unfold tailWord_4053228
  simp only [CollatzResearch.WordTrace]
  refine ⟨73916685079927333537884169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98555580106569778050512225 73916685079927333537884169)
  ·
    refine ⟨55437513809945500153413127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73916685079927333537884169 55437513809945500153413127)
    ·
      refine ⟨83156270714918250230119691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55437513809945500153413127 83156270714918250230119691)
      ·
        refine ⟨124734406072377375345179537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83156270714918250230119691 124734406072377375345179537)
        ·
          refine ⟨93550804554283031508884653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124734406072377375345179537 93550804554283031508884653)
          ·
            refine ⟨35081551707856136815831745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93550804554283031508884653 35081551707856136815831745)
            ·
              refine ⟨26311163780892102611873809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35081551707856136815831745 26311163780892102611873809)
              ·
                refine ⟨19733372835669076958905357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26311163780892102611873809 19733372835669076958905357)
                ·
                  refine ⟨7400014813375903859589509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19733372835669076958905357 7400014813375903859589509)
                  ·
                    refine ⟨1387502777507981973673033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400014813375903859589509 1387502777507981973673033)
                    ·
                      rfl

theorem cell22_4053228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_4053228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053228 prefixEnd_4053228 := by exact prefixLift 4053228
  have htrace : WordTrace (prefixWord ++ tailWord_4053228) baseStart_4053228 baseEnd_4053228 := by
    simpa [prefixWord, tailWord_4053228, baseEnd_4053228] using wordTrace_append hprefix tailTrace_4053228
  have hstable : (prefixWord ++ tailWord_4053228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053228).length < 2 ^ (prefixWord ++ tailWord_4053228).sum := by decide
  have hdescent : baseEnd_4053228 < baseStart_4053228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053258 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_4053258 : Nat := 118140960795 + 4053258 * 2 ^ 59
def prefixEnd_4053258 : Nat := 4983230072969 + 3 ^ 40 * 4053258 * 2
def baseEnd_4053258 : Nat := 1387513047121071895422941

theorem tailTrace_4053258 : CollatzResearch.WordTrace tailWord_4053258 prefixEnd_4053258 1387513047121071895422941 := by
  unfold tailWord_4053258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36958616087436495549840107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98556309566497321466240285 36958616087436495549840107)
  ·
    refine ⟨55437924131154743324760161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36958616087436495549840107 55437924131154743324760161)
    ·
      refine ⟨41578443098366057493570121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55437924131154743324760161 41578443098366057493570121)
      ·
        refine ⟨31183832323774543120177591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41578443098366057493570121 31183832323774543120177591)
        ·
          refine ⟨46775748485661814680266387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31183832323774543120177591 46775748485661814680266387)
          ·
            refine ⟨70163622728492722020399581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46775748485661814680266387 70163622728492722020399581)
            ·
              refine ⟨26311358523184770757649843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70163622728492722020399581 26311358523184770757649843)
              ·
                refine ⟨39467037784777156136474765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26311358523184770757649843 39467037784777156136474765)
                ·
                  refine ⟨14800139169291433551178037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39467037784777156136474765 14800139169291433551178037)
                  ·
                    refine ⟨1387513047121071895422941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14800139169291433551178037 1387513047121071895422941)
                    ·
                      rfl

theorem cell22_4053258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_4053258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053258 prefixEnd_4053258 := by exact prefixLift 4053258
  have htrace : WordTrace (prefixWord ++ tailWord_4053258) baseStart_4053258 baseEnd_4053258 := by
    simpa [prefixWord, tailWord_4053258, baseEnd_4053258] using wordTrace_append hprefix tailTrace_4053258
  have hstable : (prefixWord ++ tailWord_4053258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053258).length < 2 ^ (prefixWord ++ tailWord_4053258).sum := by decide
  have hdescent : baseEnd_4053258 < baseStart_4053258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053260 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_4053260 : Nat := 118140960795 + 4053260 * 2 ^ 59
def prefixEnd_4053260 : Nat := 4983230072969 + 3 ^ 40 * 4053260 * 2
def baseEnd_4053260 : Nat := 462504577253981518957645

theorem tailTrace_4053260 : CollatzResearch.WordTrace tailWord_4053260 prefixEnd_4053260 462504577253981518957645 := by
  unfold tailWord_4053260
  simp only [CollatzResearch.WordTrace]
  refine ⟨73917268647869368270466617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98556358197159157693955489 73917268647869368270466617)
  ·
    refine ⟨55437951485902026202849963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73917268647869368270466617 55437951485902026202849963)
    ·
      refine ⟨83156927228853039304274945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55437951485902026202849963 83156927228853039304274945)
      ·
        refine ⟨62367695421639779478206209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83156927228853039304274945 62367695421639779478206209)
        ·
          refine ⟨46775771566229834608654657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62367695421639779478206209 46775771566229834608654657)
          ·
            refine ⟨35081828674672375956490993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46775771566229834608654657 35081828674672375956490993)
            ·
              refine ⟨26311371506004281967368245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35081828674672375956490993 26311371506004281967368245)
              ·
                refine ⟨2466691078687901434440773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26311371506004281967368245 2466691078687901434440773)
                ·
                  refine ⟨462504577253981518957645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466691078687901434440773 462504577253981518957645)
                  ·
                    rfl

theorem cell22_4053260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_4053260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053260 prefixEnd_4053260 := by exact prefixLift 4053260
  have htrace : WordTrace (prefixWord ++ tailWord_4053260) baseStart_4053260 baseEnd_4053260 := by
    simpa [prefixWord, tailWord_4053260, baseEnd_4053260] using wordTrace_append hprefix tailTrace_4053260
  have hstable : (prefixWord ++ tailWord_4053260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053260).length < 2 ^ (prefixWord ++ tailWord_4053260).sum := by decide
  have hdescent : baseEnd_4053260 < baseStart_4053260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053262 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_4053262 : Nat := 118140960795 + 4053262 * 2 ^ 59
def prefixEnd_4053262 : Nat := 4983230072969 + 3 ^ 40 * 4053262 * 2
def baseEnd_4053262 : Nat := 1387514416402817218322929

theorem tailTrace_4053262 : CollatzResearch.WordTrace tailWord_4053262 prefixEnd_4053262 1387514416402817218322929 := by
  unfold tailWord_4053262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479326280216436360313255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98556406827820993921670693 18479326280216436360313255)
  ·
    refine ⟨27718989420324654540469883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18479326280216436360313255 27718989420324654540469883)
    ·
      refine ⟨41578484130486981810704825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27718989420324654540469883 41578484130486981810704825)
      ·
        refine ⟨31183863097865236358028619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41578484130486981810704825 31183863097865236358028619)
        ·
          refine ⟨46775794646797854537042929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31183863097865236358028619 46775794646797854537042929)
          ·
            refine ⟨35081845985098390902782197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46775794646797854537042929 35081845985098390902782197)
            ·
              refine ⟨3288923061102974147135831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35081845985098390902782197 3288923061102974147135831)
              ·
                refine ⟨4933384591654461220703747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288923061102974147135831 4933384591654461220703747)
                ·
                  refine ⟨7400076887481691831055621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933384591654461220703747 7400076887481691831055621)
                  ·
                    refine ⟨1387514416402817218322929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400076887481691831055621 1387514416402817218322929)
                    ·
                      rfl

theorem cell22_4053262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_4053262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053262 prefixEnd_4053262 := by exact prefixLift 4053262
  have htrace : WordTrace (prefixWord ++ tailWord_4053262) baseStart_4053262 baseEnd_4053262 := by
    simpa [prefixWord, tailWord_4053262, baseEnd_4053262] using wordTrace_append hprefix tailTrace_4053262
  have hstable : (prefixWord ++ tailWord_4053262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053262).length < 2 ^ (prefixWord ++ tailWord_4053262).sum := by decide
  have hdescent : baseEnd_4053262 < baseStart_4053262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053275 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 2, 3]
def baseStart_4053275 : Nat := 118140960795 + 4053275 * 2 ^ 59
def prefixEnd_4053275 : Nat := 4983230072969 + 3 ^ 40 * 4053275 * 2
def baseEnd_4053275 : Nat := 1387518866568489517747889

theorem tailTrace_4053275 : CollatzResearch.WordTrace tailWord_4053275 prefixEnd_4053275 1387518866568489517747889 := by
  unfold tailWord_4053275
  simp only [CollatzResearch.WordTrace]
  refine ⟨147835084390684394102729279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98556722927122929401819519 147835084390684394102729279)
  ·
    refine ⟨221752626586026591154093919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147835084390684394102729279 221752626586026591154093919)
    ·
      refine ⟨332628939879039886731140879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221752626586026591154093919 332628939879039886731140879)
      ·
        refine ⟨498943409818559830096711319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332628939879039886731140879 498943409818559830096711319)
        ·
          refine ⟨748415114727839745145066979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498943409818559830096711319 748415114727839745145066979)
          ·
            refine ⟨1122622672091759617717600469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748415114727839745145066979 1122622672091759617717600469)
            ·
              refine ⟨26311468877150616040256261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1122622672091759617717600469 26311468877150616040256261)
              ·
                refine ⟨4933400414465740507548049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26311468877150616040256261 4933400414465740507548049)
                ·
                  refine ⟨3700050310849305380661037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4933400414465740507548049 3700050310849305380661037)
                  ·
                    refine ⟨1387518866568489517747889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700050310849305380661037 1387518866568489517747889)
                    ·
                      rfl

theorem cell22_4053275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3].length) (baseStart_4053275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053275 prefixEnd_4053275 := by exact prefixLift 4053275
  have htrace : WordTrace (prefixWord ++ tailWord_4053275) baseStart_4053275 baseEnd_4053275 := by
    simpa [prefixWord, tailWord_4053275, baseEnd_4053275] using wordTrace_append hprefix tailTrace_4053275
  have hstable : (prefixWord ++ tailWord_4053275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053275).length < 2 ^ (prefixWord ++ tailWord_4053275).sum := by decide
  have hdescent : baseEnd_4053275 < baseStart_4053275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053393 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_4053393 : Nat := 118140960795 + 4053393 * 2 ^ 59
def prefixEnd_4053393 : Nat := 4983230072969 + 3 ^ 40 * 4053393 * 2
def baseEnd_4053393 : Nat := 1387559260379976543297527

theorem tailTrace_4053393 : CollatzResearch.WordTrace tailWord_4053393 prefixEnd_4053393 1387559260379976543297527 := by
  unfold tailWord_4053393
  simp only [CollatzResearch.WordTrace]
  refine ⟨147839388204256900255524833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98559592136171266837016555 147839388204256900255524833)
  ·
    refine ⟨110879541153192675191643625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147839388204256900255524833 110879541153192675191643625)
    ·
      refine ⟨83159655864894506393732719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110879541153192675191643625 83159655864894506393732719)
      ·
        refine ⟨124739483797341759590599079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83159655864894506393732719 124739483797341759590599079)
        ·
          refine ⟨187109225696012639385898619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124739483797341759590599079 187109225696012639385898619)
          ·
            refine ⟨280663838544018959078847929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187109225696012639385898619 280663838544018959078847929)
            ·
              refine ⟨210497878908014219309135947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280663838544018959078847929 210497878908014219309135947)
              ·
                refine ⟨315746818362021328963703921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210497878908014219309135947 315746818362021328963703921)
                ·
                  refine ⟨236810113771515996722777941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315746818362021328963703921 236810113771515996722777941)
                  ·
                    refine ⟨1387559260379976543297527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 236810113771515996722777941 1387559260379976543297527)
                    ·
                      rfl

theorem cell22_4053393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_4053393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053393 prefixEnd_4053393 := by exact prefixLift 4053393
  have htrace : WordTrace (prefixWord ++ tailWord_4053393) baseStart_4053393 baseEnd_4053393 := by
    simpa [prefixWord, tailWord_4053393, baseEnd_4053393] using wordTrace_append hprefix tailTrace_4053393
  have hstable : (prefixWord ++ tailWord_4053393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053393).length < 2 ^ (prefixWord ++ tailWord_4053393).sum := by decide
  have hdescent : baseEnd_4053393 < baseStart_4053393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053472 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_4053472 : Nat := 118140960795 + 4053472 * 2 ^ 59
def prefixEnd_4053472 : Nat := 4983230072969 + 3 ^ 40 * 4053472 * 2
def baseEnd_4053472 : Nat := 1387586303694446670572285

theorem tailTrace_4053472 : CollatzResearch.WordTrace tailWord_4053472 prefixEnd_4053472 1387586303694446670572285 := by
  unfold tailWord_4053472
  simp only [CollatzResearch.WordTrace]
  refine ⟨73921134785485348373825335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98561513047313797831767113 73921134785485348373825335)
  ·
    refine ⟨110881702178228022560738003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73921134785485348373825335 110881702178228022560738003)
    ·
      refine ⟨166322553267342033841107005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110881702178228022560738003 166322553267342033841107005)
      ·
        refine ⟨62370957475253262690415127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166322553267342033841107005 62370957475253262690415127)
        ·
          refine ⟨93556436212879894035622691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62370957475253262690415127 93556436212879894035622691)
          ·
            refine ⟨140334654319319841053434037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93556436212879894035622691 140334654319319841053434037)
            ·
              refine ⟨13156373842436235098759441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140334654319319841053434037 13156373842436235098759441)
              ·
                refine ⟨9867280381827176324069581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13156373842436235098759441 9867280381827176324069581)
                ·
                  refine ⟨3700230143185191121526093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9867280381827176324069581 3700230143185191121526093)
                  ·
                    refine ⟨1387586303694446670572285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700230143185191121526093 1387586303694446670572285)
                    ·
                      rfl

theorem cell22_4053472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_4053472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053472 prefixEnd_4053472 := by exact prefixLift 4053472
  have htrace : WordTrace (prefixWord ++ tailWord_4053472) baseStart_4053472 baseEnd_4053472 := by
    simpa [prefixWord, tailWord_4053472, baseEnd_4053472] using wordTrace_append hprefix tailTrace_4053472
  have hstable : (prefixWord ++ tailWord_4053472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053472).length < 2 ^ (prefixWord ++ tailWord_4053472).sum := by decide
  have hdescent : baseEnd_4053472 < baseStart_4053472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053540 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_4053540 : Nat := 118140960795 + 4053540 * 2 ^ 59
def prefixEnd_4053540 : Nat := 4983230072969 + 3 ^ 40 * 4053540 * 2
def baseEnd_4053540 : Nat := 1387609581484117159872077

theorem tailTrace_4053540 : CollatzResearch.WordTrace tailWord_4053540 prefixEnd_4053540 1387609581484117159872077 := by
  unfold tailWord_4053540
  simp only [CollatzResearch.WordTrace]
  refine ⟨73922374867362172180563037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98563166489816229574084049 73922374867362172180563037)
  ·
    refine ⟨27720890575260814567711139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73922374867362172180563037 27720890575260814567711139)
    ·
      refine ⟨41581335862891221851566709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720890575260814567711139 41581335862891221851566709)
      ·
        refine ⟨3898250237146052048584379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41581335862891221851566709 3898250237146052048584379)
        ·
          refine ⟨5847375355719078072876569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898250237146052048584379 5847375355719078072876569)
          ·
            refine ⟨4385531516789308554657427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847375355719078072876569 4385531516789308554657427)
            ·
              refine ⟨6578297275183962831986141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385531516789308554657427 6578297275183962831986141)
              ·
                refine ⟨2466861478193986061994803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6578297275183962831986141 2466861478193986061994803)
                ·
                  refine ⟨3700292217290979092992205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466861478193986061994803 3700292217290979092992205)
                  ·
                    refine ⟨1387609581484117159872077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700292217290979092992205 1387609581484117159872077)
                    ·
                      rfl

theorem cell22_4053540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_4053540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053540 prefixEnd_4053540 := by exact prefixLift 4053540
  have htrace : WordTrace (prefixWord ++ tailWord_4053540) baseStart_4053540 baseEnd_4053540 := by
    simpa [prefixWord, tailWord_4053540, baseEnd_4053540] using wordTrace_append hprefix tailTrace_4053540
  have hstable : (prefixWord ++ tailWord_4053540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053540).length < 2 ^ (prefixWord ++ tailWord_4053540).sum := by decide
  have hdescent : baseEnd_4053540 < baseStart_4053540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053564 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_4053564 : Nat := 118140960795 + 4053564 * 2 ^ 59
def prefixEnd_4053564 : Nat := 4983230072969 + 3 ^ 40 * 4053564 * 2
def baseEnd_4053564 : Nat := 462539265724863032424001

theorem tailTrace_4053564 : CollatzResearch.WordTrace tailWord_4053564 prefixEnd_4053564 462539265724863032424001 := by
  unfold tailWord_4053564
  simp only [CollatzResearch.WordTrace]
  refine ⟨73922812543318698229999873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98563750057758264306666497 73922812543318698229999873)
  ·
    refine ⟨55442109407489023672499905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73922812543318698229999873 55442109407489023672499905)
    ·
      refine ⟨41581582055616767754374929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55442109407489023672499905 41581582055616767754374929)
      ·
        refine ⟨31186186541712575815781197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41581582055616767754374929 31186186541712575815781197)
        ·
          refine ⟨11694819953142215930917949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31186186541712575815781197 11694819953142215930917949)
          ·
            refine ⟨4385557482428330974094231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11694819953142215930917949 4385557482428330974094231)
            ·
              refine ⟨6578336223642496461141347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385557482428330974094231 6578336223642496461141347)
              ·
                refine ⟨9867504335463744691712021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578336223642496461141347 9867504335463744691712021)
                ·
                  refine ⟨462539265724863032424001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9867504335463744691712021 462539265724863032424001)
                  ·
                    rfl

theorem cell22_4053564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_4053564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053564 prefixEnd_4053564 := by exact prefixLift 4053564
  have htrace : WordTrace (prefixWord ++ tailWord_4053564) baseStart_4053564 baseEnd_4053564 := by
    simpa [prefixWord, tailWord_4053564, baseEnd_4053564] using wordTrace_append hprefix tailTrace_4053564
  have hstable : (prefixWord ++ tailWord_4053564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053564).length < 2 ^ (prefixWord ++ tailWord_4053564).sum := by decide
  have hdescent : baseEnd_4053564 < baseStart_4053564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053667 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_4053667 : Nat := 118140960795 + 4053667 * 2 ^ 59
def prefixEnd_4053667 : Nat := 4983230072969 + 3 ^ 40 * 4053667 * 2
def baseEnd_4053667 : Nat := 1387653056179531161946687

theorem tailTrace_4053667 : CollatzResearch.WordTrace tailWord_4053667 prefixEnd_4053667 1387653056179531161946687 := by
  unfold tailWord_4053667
  simp only [CollatzResearch.WordTrace]
  refine ⟨147849381805264245050999255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98566254536842830033999503 147849381805264245050999255)
  ·
    refine ⟨221774072707896367576498883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147849381805264245050999255 221774072707896367576498883)
    ·
      refine ⟨332661109061844551364748325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221774072707896367576498883 332661109061844551364748325)
      ·
        refine ⟨62373957949095853380890311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332661109061844551364748325 62373957949095853380890311)
        ·
          refine ⟨93560936923643780071335467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62373957949095853380890311 93560936923643780071335467)
          ·
            refine ⟨140341405385465670107003201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93560936923643780071335467 140341405385465670107003201)
            ·
              refine ⟨105256054039099252580252401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140341405385465670107003201 105256054039099252580252401)
              ·
                refine ⟨78942040529324439435189301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105256054039099252580252401 78942040529324439435189301)
                ·
                  refine ⟨7400816299624166197048997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78942040529324439435189301 7400816299624166197048997)
                  ·
                    refine ⟨1387653056179531161946687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400816299624166197048997 1387653056179531161946687)
                    ·
                      rfl

theorem cell22_4053667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_4053667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053667 prefixEnd_4053667 := by exact prefixLift 4053667
  have htrace : WordTrace (prefixWord ++ tailWord_4053667) baseStart_4053667 baseEnd_4053667 := by
    simpa [prefixWord, tailWord_4053667, baseEnd_4053667] using wordTrace_append hprefix tailTrace_4053667
  have hstable : (prefixWord ++ tailWord_4053667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053667).length < 2 ^ (prefixWord ++ tailWord_4053667).sum := by decide
  have hdescent : baseEnd_4053667 < baseStart_4053667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053671 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 7]
def baseStart_4053671 : Nat := 118140960795 + 4053671 * 2 ^ 59
def prefixEnd_4053671 : Nat := 4983230072969 + 3 ^ 40 * 4053671 * 2
def baseEnd_4053671 : Nat := 462551475153758828282225

theorem tailTrace_4053671 : CollatzResearch.WordTrace tailWord_4053671 prefixEnd_4053671 462551475153758828282225 := by
  unfold tailWord_4053671
  simp only [CollatzResearch.WordTrace]
  refine ⟨147849527697249753734144867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98566351798166502489429911 147849527697249753734144867)
  ·
    refine ⟨221774291545874630601217301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147849527697249753734144867 221774291545874630601217301)
    ·
      refine ⟨10395669916212873309432061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 221774291545874630601217301 10395669916212873309432061)
      ·
        refine ⟨3898376218579827491037023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10395669916212873309432061 3898376218579827491037023)
        ·
          refine ⟨5847564327869741236555535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898376218579827491037023 5847564327869741236555535)
          ·
            refine ⟨8771346491804611854833303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847564327869741236555535 8771346491804611854833303)
            ·
              refine ⟨13157019737706917782249955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771346491804611854833303 13157019737706917782249955)
              ·
                refine ⟨19735529606560376673374933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157019737706917782249955 19735529606560376673374933)
                ·
                  refine ⟨462551475153758828282225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19735529606560376673374933 462551475153758828282225)
                  ·
                    rfl

theorem cell22_4053671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 7].length) (baseStart_4053671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053671 prefixEnd_4053671 := by exact prefixLift 4053671
  have htrace : WordTrace (prefixWord ++ tailWord_4053671) baseStart_4053671 baseEnd_4053671 := by
    simpa [prefixWord, tailWord_4053671, baseEnd_4053671] using wordTrace_append hprefix tailTrace_4053671
  have hstable : (prefixWord ++ tailWord_4053671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053671).length < 2 ^ (prefixWord ++ tailWord_4053671).sum := by decide
  have hdescent : baseEnd_4053671 < baseStart_4053671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053709 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_4053709 : Nat := 118140960795 + 4053709 * 2 ^ 59
def prefixEnd_4053709 : Nat := 4983230072969 + 3 ^ 40 * 4053709 * 2
def baseEnd_4053709 : Nat := 1387667433637857052396559

theorem tailTrace_4053709 : CollatzResearch.WordTrace tailWord_4053709 prefixEnd_4053709 1387667433637857052396559 := by
  unfold tailWord_4053709
  simp only [CollatzResearch.WordTrace]
  refine ⟨147850913671112086224028181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98567275780741390816018787 147850913671112086224028181)
  ·
    refine ⟨6930511578333379041751321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147850913671112086224028181 6930511578333379041751321)
    ·
      refine ⟨5197883683750034281313491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930511578333379041751321 5197883683750034281313491)
      ·
        refine ⟨7796825525625051421970237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197883683750034281313491 7796825525625051421970237)
        ·
          refine ⟨2923809572109394283238839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7796825525625051421970237 2923809572109394283238839)
          ·
            refine ⟨4385714358164091424858259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923809572109394283238839 4385714358164091424858259)
            ·
              refine ⟨6578571537246137137287389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385714358164091424858259 6578571537246137137287389)
              ·
                refine ⟨2466964326467301426482771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6578571537246137137287389 2466964326467301426482771)
                ·
                  refine ⟨3700446489700952139724157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466964326467301426482771 3700446489700952139724157)
                  ·
                    refine ⟨1387667433637857052396559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700446489700952139724157 1387667433637857052396559)
                    ·
                      rfl

theorem cell22_4053709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_4053709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053709 prefixEnd_4053709 := by exact prefixLift 4053709
  have htrace : WordTrace (prefixWord ++ tailWord_4053709) baseStart_4053709 baseEnd_4053709 := by
    simpa [prefixWord, tailWord_4053709, baseEnd_4053709] using wordTrace_append hprefix tailTrace_4053709
  have hstable : (prefixWord ++ tailWord_4053709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053709).length < 2 ^ (prefixWord ++ tailWord_4053709).sum := by decide
  have hdescent : baseEnd_4053709 < baseStart_4053709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053727 : List Nat := [1, 1, 2, 3, 2, 3, 10]
def baseStart_4053727 : Nat := 118140960795 + 4053727 * 2 ^ 59
def prefixEnd_4053727 : Nat := 4983230072969 + 3 ^ 40 * 4053727 * 2
def baseEnd_4053727 : Nat := 51395318348359666868389

theorem tailTrace_4053727 : CollatzResearch.WordTrace tailWord_4053727 prefixEnd_4053727 51395318348359666868389 := by
  unfold tailWord_4053727
  simp only [CollatzResearch.WordTrace]
  refine ⟨147851570185046875298183435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98567713456697916865455623 147851570185046875298183435)
  ·
    refine ⟨221777355277570312947275153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147851570185046875298183435 221777355277570312947275153)
    ·
      refine ⟨166333016458177734710456365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221777355277570312947275153 166333016458177734710456365)
      ·
        refine ⟨62374881171816650516421137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166333016458177734710456365 62374881171816650516421137)
        ·
          refine ⟨46781160878862487887315853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62374881171816650516421137 46781160878862487887315853)
          ·
            refine ⟨17542935329573432957743445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46781160878862487887315853 17542935329573432957743445)
            ·
              refine ⟨51395318348359666868389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17542935329573432957743445 51395318348359666868389)
              ·
                rfl

theorem cell22_4053727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 10].length) (baseStart_4053727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053727 prefixEnd_4053727 := by exact prefixLift 4053727
  have htrace : WordTrace (prefixWord ++ tailWord_4053727) baseStart_4053727 baseEnd_4053727 := by
    simpa [prefixWord, tailWord_4053727, baseEnd_4053727] using wordTrace_append hprefix tailTrace_4053727
  have hstable : (prefixWord ++ tailWord_4053727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053727).length < 2 ^ (prefixWord ++ tailWord_4053727).sum := by decide
  have hdescent : baseEnd_4053727 < baseStart_4053727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053729 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_4053729 : Nat := 118140960795 + 4053729 * 2 ^ 59
def prefixEnd_4053729 : Nat := 4983230072969 + 3 ^ 40 * 4053729 * 2
def baseEnd_4053729 : Nat := 1387674280046583666896497

theorem tailTrace_4053729 : CollatzResearch.WordTrace tailWord_4053729 prefixEnd_4053729 1387674280046583666896497 := by
  unfold tailWord_4053729
  simp only [CollatzResearch.WordTrace]
  refine ⟨147851643131039629639756241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98567762087359753093170827 147851643131039629639756241)
  ·
    refine ⟨110888732348279722229817181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147851643131039629639756241 110888732348279722229817181)
    ·
      refine ⟨41583274630604895836181443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110888732348279722229817181 41583274630604895836181443)
      ·
        refine ⟨62374911945907343754272165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41583274630604895836181443 62374911945907343754272165)
        ·
          refine ⟨11695295989857626953926031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62374911945907343754272165 11695295989857626953926031)
          ·
            refine ⟨17542943984786440430889047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695295989857626953926031 17542943984786440430889047)
            ·
              refine ⟨26314415977179660646333571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17542943984786440430889047 26314415977179660646333571)
              ·
                refine ⟨39471623965769490969500357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26314415977179660646333571 39471623965769490969500357)
                ·
                  refine ⟨7400929493581779556781317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39471623965769490969500357 7400929493581779556781317)
                  ·
                    refine ⟨1387674280046583666896497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400929493581779556781317 1387674280046583666896497)
                    ·
                      rfl

theorem cell22_4053729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_4053729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053729 prefixEnd_4053729 := by exact prefixLift 4053729
  have htrace : WordTrace (prefixWord ++ tailWord_4053729) baseStart_4053729 baseEnd_4053729 := by
    simpa [prefixWord, tailWord_4053729, baseEnd_4053729] using wordTrace_append hprefix tailTrace_4053729
  have hstable : (prefixWord ++ tailWord_4053729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053729).length < 2 ^ (prefixWord ++ tailWord_4053729).sum := by decide
  have hdescent : baseEnd_4053729 < baseStart_4053729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053731 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 4, 3]
def baseStart_4053731 : Nat := 118140960795 + 4053731 * 2 ^ 59
def prefixEnd_4053731 : Nat := 4983230072969 + 3 ^ 40 * 4053731 * 2
def baseEnd_4053731 : Nat := 1387674964687456328346491

theorem tailTrace_4053731 : CollatzResearch.WordTrace tailWord_4053731 prefixEnd_4053731 1387674964687456328346491 := by
  unfold tailWord_4053731
  simp only [CollatzResearch.WordTrace]
  refine ⟨147851716077032383981329047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98567810718021589320886031 147851716077032383981329047)
  ·
    refine ⟨221777574115548575971993571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147851716077032383981329047 221777574115548575971993571)
    ·
      refine ⟨332666361173322863957990357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221777574115548575971993571 332666361173322863957990357)
      ·
        refine ⟨7796867839999754624015399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 332666361173322863957990357 7796867839999754624015399)
        ·
          refine ⟨11695301759999631936023099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796867839999754624015399 11695301759999631936023099)
          ·
            refine ⟨17542952639999447904034649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695301759999631936023099 17542952639999447904034649)
            ·
              refine ⟨13157214479999585928025987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542952639999447904034649 13157214479999585928025987)
              ·
                refine ⟨19735821719999378892038981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157214479999585928025987 19735821719999378892038981)
                ·
                  refine ⟨3700466572499883542257309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19735821719999378892038981 3700466572499883542257309)
                  ·
                    refine ⟨1387674964687456328346491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700466572499883542257309 1387674964687456328346491)
                    ·
                      rfl

theorem cell22_4053731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3].length) (baseStart_4053731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053731 prefixEnd_4053731 := by exact prefixLift 4053731
  have htrace : WordTrace (prefixWord ++ tailWord_4053731) baseStart_4053731 baseEnd_4053731 := by
    simpa [prefixWord, tailWord_4053731, baseEnd_4053731] using wordTrace_append hprefix tailTrace_4053731
  have hstable : (prefixWord ++ tailWord_4053731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053731).length < 2 ^ (prefixWord ++ tailWord_4053731).sum := by decide
  have hdescent : baseEnd_4053731 < baseStart_4053731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053733 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 4]
def baseStart_4053733 : Nat := 118140960795 + 4053733 * 2 ^ 59
def prefixEnd_4053733 : Nat := 4983230072969 + 3 ^ 40 * 4053733 * 2
def baseEnd_4053733 : Nat := 462558549776109663265495

theorem tailTrace_4053733 : CollatzResearch.WordTrace tailWord_4053733 prefixEnd_4053733 462558549776109663265495 := by
  unfold tailWord_4053733
  simp only [CollatzResearch.WordTrace]
  refine ⟨147851789023025138322901853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98567859348683425548601235 147851789023025138322901853)
  ·
    refine ⟨55444420883634426871088195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147851789023025138322901853 55444420883634426871088195)
    ·
      refine ⟨83166631325451640306632293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55444420883634426871088195 83166631325451640306632293)
      ·
        refine ⟨15593743373522182557493555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83166631325451640306632293 15593743373522182557493555)
        ·
          refine ⟨23390615060283273836240333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15593743373522182557493555 23390615060283273836240333)
          ·
            refine ⟨8771480647606227688590125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23390615060283273836240333 8771480647606227688590125)
            ·
              refine ⟨3289305242852335383221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8771480647606227688590125 3289305242852335383221297)
              ·
                refine ⟨2466978932139251537415973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289305242852335383221297 2466978932139251537415973)
                ·
                  refine ⟨462558549776109663265495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2466978932139251537415973 462558549776109663265495)
                  ·
                    rfl

theorem cell22_4053733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_4053733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053733 prefixEnd_4053733 := by exact prefixLift 4053733
  have htrace : WordTrace (prefixWord ++ tailWord_4053733) baseStart_4053733 baseEnd_4053733 := by
    simpa [prefixWord, tailWord_4053733, baseEnd_4053733] using wordTrace_append hprefix tailTrace_4053733
  have hstable : (prefixWord ++ tailWord_4053733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053733).length < 2 ^ (prefixWord ++ tailWord_4053733).sum := by decide
  have hdescent : baseEnd_4053733 < baseStart_4053733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053759 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 5, 3]
def baseStart_4053759 : Nat := 118140960795 + 4053759 * 2 ^ 59
def prefixEnd_4053759 : Nat := 4983230072969 + 3 ^ 40 * 4053759 * 2
def baseEnd_4053759 : Nat := 1387684549659673588646405

theorem tailTrace_4053759 : CollatzResearch.WordTrace tailWord_4053759 prefixEnd_4053759 1387684549659673588646405 := by
  unfold tailWord_4053759
  simp only [CollatzResearch.WordTrace]
  refine ⟨147852737320930944763348331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98568491547287296508898887 147852737320930944763348331)
  ·
    refine ⟨221779105981396417145022497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147852737320930944763348331 221779105981396417145022497)
    ·
      refine ⟨166334329486047312858766873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221779105981396417145022497 166334329486047312858766873)
      ·
        refine ⟨124750747114535484644075155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166334329486047312858766873 124750747114535484644075155)
        ·
          refine ⟨187126120671803226966112733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124750747114535484644075155 187126120671803226966112733)
          ·
            refine ⟨70172295251926210112292275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187126120671803226966112733 70172295251926210112292275)
            ·
              refine ⟨105258442877889315168438413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70172295251926210112292275 105258442877889315168438413)
              ·
                refine ⟨39471916079208493188164405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105258442877889315168438413 39471916079208493188164405)
                ·
                  refine ⟨3700492132425796236390413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39471916079208493188164405 3700492132425796236390413)
                  ·
                    refine ⟨1387684549659673588646405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700492132425796236390413 1387684549659673588646405)
                    ·
                      rfl

theorem cell22_4053759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_4053759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053759 prefixEnd_4053759 := by exact prefixLift 4053759
  have htrace : WordTrace (prefixWord ++ tailWord_4053759) baseStart_4053759 baseEnd_4053759 := by
    simpa [prefixWord, tailWord_4053759, baseEnd_4053759] using wordTrace_append hprefix tailTrace_4053759
  have hstable : (prefixWord ++ tailWord_4053759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053759).length < 2 ^ (prefixWord ++ tailWord_4053759).sum := by decide
  have hdescent : baseEnd_4053759 < baseStart_4053759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053793 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 1, 3]
def baseStart_4053793 : Nat := 118140960795 + 4053793 * 2 ^ 59
def prefixEnd_4053793 : Nat := 4983230072969 + 3 ^ 40 * 4053793 * 2
def baseEnd_4053793 : Nat := 1387696188554508833296301

theorem tailTrace_4053793 : CollatzResearch.WordTrace tailWord_4053793 prefixEnd_4053793 1387696188554508833296301 := by
  unfold tailWord_4053793
  simp only [CollatzResearch.WordTrace]
  refine ⟨147853977402807768570086033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98569318268538512380057355 147853977402807768570086033)
  ·
    refine ⟨110890483052105826427564525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147853977402807768570086033 110890483052105826427564525)
    ·
      refine ⟨41583931144539684910336697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110890483052105826427564525 41583931144539684910336697)
      ·
        refine ⟨31187948358404763682752523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41583931144539684910336697 31187948358404763682752523)
        ·
          refine ⟨46781922537607145524128785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31187948358404763682752523 46781922537607145524128785)
          ·
            refine ⟨35086441903205359143096589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46781922537607145524128785 35086441903205359143096589)
            ·
              refine ⟨13157415713702009678661221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35086441903205359143096589 13157415713702009678661221)
              ·
                refine ⟨2467015446319126814748979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13157415713702009678661221 2467015446319126814748979)
                ·
                  refine ⟨3700523169478690222123469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467015446319126814748979 3700523169478690222123469)
                  ·
                    refine ⟨1387696188554508833296301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700523169478690222123469 1387696188554508833296301)
                    ·
                      rfl

theorem cell22_4053793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_4053793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053793 prefixEnd_4053793 := by exact prefixLift 4053793
  have htrace : WordTrace (prefixWord ++ tailWord_4053793) baseStart_4053793 baseEnd_4053793 := by
    simpa [prefixWord, tailWord_4053793, baseEnd_4053793] using wordTrace_append hprefix tailTrace_4053793
  have hstable : (prefixWord ++ tailWord_4053793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053793).length < 2 ^ (prefixWord ++ tailWord_4053793).sum := by decide
  have hdescent : baseEnd_4053793 < baseStart_4053793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053804 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_4053804 : Nat := 118140960795 + 4053804 * 2 ^ 59
def prefixEnd_4053804 : Nat := 4983230072969 + 3 ^ 40 * 4053804 * 2
def baseEnd_4053804 : Nat := 1387699954079308471271267

theorem tailTrace_4053804 : CollatzResearch.WordTrace tailWord_4053804 prefixEnd_4053804 1387699954079308471271267 := by
  unfold tailWord_4053804
  simp only [CollatzResearch.WordTrace]
  refine ⟨73927189302883958724368233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98569585737178611632490977 73927189302883958724368233)
  ·
    refine ⟨55445391977162969043276175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73927189302883958724368233 55445391977162969043276175)
    ·
      refine ⟨83168087965744453564914263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55445391977162969043276175 83168087965744453564914263)
      ·
        refine ⟨124752131948616680347371395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83168087965744453564914263 124752131948616680347371395)
        ·
          refine ⟨187128197922925020521057093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124752131948616680347371395 187128197922925020521057093)
          ·
            refine ⟨35086537110548441347698205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187128197922925020521057093 35086537110548441347698205)
            ·
              refine ⟨13157451416455665505386827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35086537110548441347698205 13157451416455665505386827)
              ·
                refine ⟨19736177124683498258080241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157451416455665505386827 19736177124683498258080241)
                ·
                  refine ⟨14802132843512623693560181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19736177124683498258080241 14802132843512623693560181)
                  ·
                    refine ⟨1387699954079308471271267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14802132843512623693560181 1387699954079308471271267)
                    ·
                      rfl

theorem cell22_4053804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_4053804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053804 prefixEnd_4053804 := by exact prefixLift 4053804
  have htrace : WordTrace (prefixWord ++ tailWord_4053804) baseStart_4053804 baseEnd_4053804 := by
    simpa [prefixWord, tailWord_4053804, baseEnd_4053804] using wordTrace_append hprefix tailTrace_4053804
  have hstable : (prefixWord ++ tailWord_4053804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053804).length < 2 ^ (prefixWord ++ tailWord_4053804).sum := by decide
  have hdescent : baseEnd_4053804 < baseStart_4053804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053870 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4053870 : Nat := 118140960795 + 4053870 * 2 ^ 59
def prefixEnd_4053870 : Nat := 4983230072969 + 3 ^ 40 * 4053870 * 2
def baseEnd_4053870 : Nat := 1387722547228106299121065

theorem tailTrace_4053870 : CollatzResearch.WordTrace tailWord_4053870 prefixEnd_4053870 1387722547228106299121065 := by
  unfold tailWord_4053870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482098227941101340079883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98571190549019207147092709 18482098227941101340079883)
  ·
    refine ⟨27723147341911652010119825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18482098227941101340079883 27723147341911652010119825)
    ·
      refine ⟨20792360506433739007589869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27723147341911652010119825 20792360506433739007589869)
      ·
        refine ⟨7797135189912652127846201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20792360506433739007589869 7797135189912652127846201)
        ·
          refine ⟨5847851392434489095884651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7797135189912652127846201 5847851392434489095884651)
          ·
            refine ⟨8771777088651733643826977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847851392434489095884651 8771777088651733643826977)
            ·
              refine ⟨6578832816488800232870233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8771777088651733643826977 6578832816488800232870233)
              ·
                refine ⟨4934124612366600174652675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578832816488800232870233 4934124612366600174652675)
                ·
                  refine ⟨7401186918549900261979013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934124612366600174652675 7401186918549900261979013)
                  ·
                    refine ⟨1387722547228106299121065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401186918549900261979013 1387722547228106299121065)
                    ·
                      rfl

theorem cell22_4053870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4053870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053870 prefixEnd_4053870 := by exact prefixLift 4053870
  have htrace : WordTrace (prefixWord ++ tailWord_4053870) baseStart_4053870 baseEnd_4053870 := by
    simpa [prefixWord, tailWord_4053870, baseEnd_4053870] using wordTrace_append hprefix tailTrace_4053870
  have hstable : (prefixWord ++ tailWord_4053870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053870).length < 2 ^ (prefixWord ++ tailWord_4053870).sum := by decide
  have hdescent : baseEnd_4053870 < baseStart_4053870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053896 : List Nat := [2, 1, 3, 3, 2, 3, 8]
def baseStart_4053896 : Nat := 118140960795 + 4053896 * 2 ^ 59
def prefixEnd_4053896 : Nat := 4983230072969 + 3 ^ 40 * 4053896 * 2
def baseEnd_4053896 : Nat := 51397461020720403628555

theorem tailTrace_4053896 : CollatzResearch.WordTrace tailWord_4053896 prefixEnd_4053896 51397461020720403628555 := by
  unfold tailWord_4053896
  simp only [CollatzResearch.WordTrace]
  refine ⟨73928867060717308580542771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98571822747623078107390361 73928867060717308580542771)
  ·
    refine ⟨110893300591075962870814157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73928867060717308580542771 110893300591075962870814157)
    ·
      refine ⟨41584987721653486076555309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110893300591075962870814157 41584987721653486076555309)
      ·
        refine ⟨15594370395620057278708241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41584987721653486076555309 15594370395620057278708241)
        ·
          refine ⟨11695777796715042959031181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15594370395620057278708241 11695777796715042959031181)
          ·
            refine ⟨4385916673768141109636693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11695777796715042959031181 4385916673768141109636693)
            ·
              refine ⟨51397461020720403628555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4385916673768141109636693 51397461020720403628555)
              ·
                rfl

theorem cell22_4053896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 8].length) (baseStart_4053896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053896 prefixEnd_4053896 := by exact prefixLift 4053896
  have htrace : WordTrace (prefixWord ++ tailWord_4053896) baseStart_4053896 baseEnd_4053896 := by
    simpa [prefixWord, tailWord_4053896, baseEnd_4053896] using wordTrace_append hprefix tailTrace_4053896
  have hstable : (prefixWord ++ tailWord_4053896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053896).length < 2 ^ (prefixWord ++ tailWord_4053896).sum := by decide
  have hdescent : baseEnd_4053896 < baseStart_4053896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053898 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_4053898 : Nat := 118140960795 + 4053898 * 2 ^ 59
def prefixEnd_4053898 : Nat := 4983230072969 + 3 ^ 40 * 4053898 * 2
def baseEnd_4053898 : Nat := 1387732132200323559420979

theorem tailTrace_4053898 : CollatzResearch.WordTrace tailWord_4053898 prefixEnd_4053898 1387732132200323559420979 := by
  unfold tailWord_4053898
  simp only [CollatzResearch.WordTrace]
  refine ⟨36964451766856842875664587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98571871378284914335105565 36964451766856842875664587)
  ·
    refine ⟨55446677650285264313496881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36964451766856842875664587 55446677650285264313496881)
    ·
      refine ⟨41585008237713948235122661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55446677650285264313496881 41585008237713948235122661)
      ·
        refine ⟨7797189044571365294085499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41585008237713948235122661 7797189044571365294085499)
        ·
          refine ⟨11695783566857047941128249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797189044571365294085499 11695783566857047941128249)
          ·
            refine ⟨8771837675142785955846187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11695783566857047941128249 8771837675142785955846187)
            ·
              refine ⟨13157756512714178933769281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771837675142785955846187 13157756512714178933769281)
              ·
                refine ⟨9868317384535634200326961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13157756512714178933769281 9868317384535634200326961)
                ·
                  refine ⟨7401238038401725650245221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9868317384535634200326961 7401238038401725650245221)
                  ·
                    refine ⟨1387732132200323559420979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401238038401725650245221 1387732132200323559420979)
                    ·
                      rfl

theorem cell22_4053898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_4053898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053898 prefixEnd_4053898 := by exact prefixLift 4053898
  have htrace : WordTrace (prefixWord ++ tailWord_4053898) baseStart_4053898 baseEnd_4053898 := by
    simpa [prefixWord, tailWord_4053898, baseEnd_4053898] using wordTrace_append hprefix tailTrace_4053898
  have hstable : (prefixWord ++ tailWord_4053898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053898).length < 2 ^ (prefixWord ++ tailWord_4053898).sum := by decide
  have hdescent : baseEnd_4053898 < baseStart_4053898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053939 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_4053939 : Nat := 118140960795 + 4053939 * 2 ^ 59
def prefixEnd_4053939 : Nat := 4983230072969 + 3 ^ 40 * 4053939 * 2
def baseEnd_4053939 : Nat := 1387746167338213119145853

theorem tailTrace_4053939 : CollatzResearch.WordTrace tailWord_4053939 prefixEnd_4053939 1387746167338213119145853 := by
  unfold tailWord_4053939
  simp only [CollatzResearch.WordTrace]
  refine ⟨147859302460278835504900871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98572868306852557003267247 147859302460278835504900871)
  ·
    refine ⟨221788953690418253257351307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147859302460278835504900871 221788953690418253257351307)
    ·
      refine ⟨332683430535627379886026961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221788953690418253257351307 332683430535627379886026961)
      ·
        refine ⟨249512572901720534914520221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332683430535627379886026961 249512572901720534914520221)
        ·
          refine ⟨93567214838145200592945083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249512572901720534914520221 93567214838145200592945083)
          ·
            refine ⟨140350822257217800889417625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93567214838145200592945083 140350822257217800889417625)
            ·
              refine ⟨105263116692913350667063219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140350822257217800889417625 105263116692913350667063219)
              ·
                refine ⟨157894675039370026000594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105263116692913350667063219 157894675039370026000594829)
                ·
                  refine ⟨59210503139763759750223061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157894675039370026000594829 59210503139763759750223061)
                  ·
                    refine ⟨1387746167338213119145853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59210503139763759750223061 1387746167338213119145853)
                    ·
                      rfl

theorem cell22_4053939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_4053939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053939 prefixEnd_4053939 := by exact prefixLift 4053939
  have htrace : WordTrace (prefixWord ++ tailWord_4053939) baseStart_4053939 baseEnd_4053939 := by
    simpa [prefixWord, tailWord_4053939, baseEnd_4053939] using wordTrace_append hprefix tailTrace_4053939
  have hstable : (prefixWord ++ tailWord_4053939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053939).length < 2 ^ (prefixWord ++ tailWord_4053939).sum := by decide
  have hdescent : baseEnd_4053939 < baseStart_4053939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4053973 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4053973 : Nat := 118140960795 + 4053973 * 2 ^ 59
def prefixEnd_4053973 : Nat := 4983230072969 + 3 ^ 40 * 4053973 * 2
def baseEnd_4053973 : Nat := 1387757806233048363795749

theorem tailTrace_4053973 : CollatzResearch.WordTrace tailWord_4053973 prefixEnd_4053973 1387757806233048363795749 := by
  unfold tailWord_4053973
  simp only [CollatzResearch.WordTrace]
  refine ⟨147860542542155659311638573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98573695028103772874425715 147860542542155659311638573)
  ·
    refine ⟨55447703453308372241864465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147860542542155659311638573 55447703453308372241864465)
    ·
      refine ⟨41585777589981279181398349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55447703453308372241864465 41585777589981279181398349)
      ·
        refine ⟨15594666596242979693024381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41585777589981279181398349 15594666596242979693024381)
        ·
          refine ⟨5847999973591117384884143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15594666596242979693024381 5847999973591117384884143)
          ·
            refine ⟨8771999960386676077326215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847999973591117384884143 8771999960386676077326215)
            ·
              refine ⟨13157999940580014115989323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771999960386676077326215 13157999940580014115989323)
              ·
                refine ⟨19736999910870021173983985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157999940580014115989323 19736999910870021173983985)
                ·
                  refine ⟨14802749933152515880487989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19736999910870021173983985 14802749933152515880487989)
                  ·
                    refine ⟨1387757806233048363795749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14802749933152515880487989 1387757806233048363795749)
                    ·
                      rfl

theorem cell22_4053973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4053973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4053973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4053973 prefixEnd_4053973 := by exact prefixLift 4053973
  have htrace : WordTrace (prefixWord ++ tailWord_4053973) baseStart_4053973 baseEnd_4053973 := by
    simpa [prefixWord, tailWord_4053973, baseEnd_4053973] using wordTrace_append hprefix tailTrace_4053973
  have hstable : (prefixWord ++ tailWord_4053973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4053973).length < 2 ^ (prefixWord ++ tailWord_4053973).sum := by decide
  have hdescent : baseEnd_4053973 < baseStart_4053973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4053973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054086 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4054086 : Nat := 118140960795 + 4054086 * 2 ^ 59
def prefixEnd_4054086 : Nat := 4983230072969 + 3 ^ 40 * 4054086 * 2
def baseEnd_4054086 : Nat := 1387796488442353735720403

theorem tailTrace_4054086 : CollatzResearch.WordTrace tailWord_4054086 prefixEnd_4054086 1387796488442353735720403 := by
  unfold tailWord_4054086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620770749710821237828191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98576442660497519740334741 4620770749710821237828191)
  ·
    refine ⟨6931156124566231856742287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620770749710821237828191 6931156124566231856742287)
    ·
      refine ⟨10396734186849347785113431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6931156124566231856742287 10396734186849347785113431)
      ·
        refine ⟨15595101280274021677670147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396734186849347785113431 15595101280274021677670147)
        ·
          refine ⟨23392651920411032516505221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15595101280274021677670147 23392651920411032516505221)
          ·
            refine ⟨4386122235077068596844729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23392651920411032516505221 4386122235077068596844729)
            ·
              refine ⟨3289591676307801447633547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386122235077068596844729 3289591676307801447633547)
              ·
                refine ⟨4934387514461702171450321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289591676307801447633547 4934387514461702171450321)
                ·
                  refine ⟨3700790635846276628587741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4934387514461702171450321 3700790635846276628587741)
                  ·
                    refine ⟨1387796488442353735720403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700790635846276628587741 1387796488442353735720403)
                    ·
                      rfl

theorem cell22_4054086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4054086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054086 prefixEnd_4054086 := by exact prefixLift 4054086
  have htrace : WordTrace (prefixWord ++ tailWord_4054086) baseStart_4054086 baseEnd_4054086 := by
    simpa [prefixWord, tailWord_4054086, baseEnd_4054086] using wordTrace_append hprefix tailTrace_4054086
  have hstable : (prefixWord ++ tailWord_4054086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054086).length < 2 ^ (prefixWord ++ tailWord_4054086).sum := by decide
  have hdescent : baseEnd_4054086 < baseStart_4054086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054153 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_4054153 : Nat := 118140960795 + 4054153 * 2 ^ 59
def prefixEnd_4054153 : Nat := 4983230072969 + 3 ^ 40 * 4054153 * 2
def baseEnd_4054153 : Nat := 1387819423911587894295197

theorem tailTrace_4054153 : CollatzResearch.WordTrace tailWord_4054153 prefixEnd_4054153 1387819423911587894295197 := by
  unfold tailWord_4054153
  simp only [CollatzResearch.WordTrace]
  refine ⟨147867107681503550053191113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98578071787669033368794075 147867107681503550053191113)
  ·
    refine ⟨110900330761127662539893335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147867107681503550053191113 110900330761127662539893335)
    ·
      refine ⟨166350496141691493809840003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110900330761127662539893335 166350496141691493809840003)
      ·
        refine ⟨249525744212537240714760005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166350496141691493809840003 249525744212537240714760005)
        ·
          refine ⟨46786077039850732634017501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249525744212537240714760005 46786077039850732634017501)
          ·
            refine ⟨17544778889944024737756563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46786077039850732634017501 17544778889944024737756563)
            ·
              refine ⟨26317168334916037106634845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17544778889944024737756563 26317168334916037106634845)
              ·
                refine ⟨9868938125593513914988067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26317168334916037106634845 9868938125593513914988067)
                ·
                  refine ⟨14803407188390270872482101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9868938125593513914988067 14803407188390270872482101)
                  ·
                    refine ⟨1387819423911587894295197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14803407188390270872482101 1387819423911587894295197)
                    ·
                      rfl

theorem cell22_4054153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_4054153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054153 prefixEnd_4054153 := by exact prefixLift 4054153
  have htrace : WordTrace (prefixWord ++ tailWord_4054153) baseStart_4054153 baseEnd_4054153 := by
    simpa [prefixWord, tailWord_4054153, baseEnd_4054153] using wordTrace_append hprefix tailTrace_4054153
  have hstable : (prefixWord ++ tailWord_4054153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054153).length < 2 ^ (prefixWord ++ tailWord_4054153).sum := by decide
  have hdescent : baseEnd_4054153 < baseStart_4054153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054170 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_4054170 : Nat := 118140960795 + 4054170 * 2 ^ 59
def prefixEnd_4054170 : Nat := 4983230072969 + 3 ^ 40 * 4054170 * 2
def baseEnd_4054170 : Nat := 1387825243359005516620145

theorem tailTrace_4054170 : CollatzResearch.WordTrace tailWord_4054170 prefixEnd_4054170 1387825243359005516620145 := by
  unfold tailWord_4054170
  simp only [CollatzResearch.WordTrace]
  refine ⟨36966931930610490489139991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98578485148294641304373309 36966931930610490489139991)
  ·
    refine ⟨55450397895915735733709987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36966931930610490489139991 55450397895915735733709987)
    ·
      refine ⟨83175596843873603600564981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55450397895915735733709987 83175596843873603600564981)
      ·
        refine ⟨7797712204113150337552967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83175596843873603600564981 7797712204113150337552967)
        ·
          refine ⟨11696568306169725506329451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797712204113150337552967 11696568306169725506329451)
          ·
            refine ⟨17544852459254588259494177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696568306169725506329451 17544852459254588259494177)
            ·
              refine ⟨13158639344440941194620633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17544852459254588259494177 13158639344440941194620633)
              ·
                refine ⟨9868979508330705895965475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158639344440941194620633 9868979508330705895965475)
                ·
                  refine ⟨14803469262496058843948213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9868979508330705895965475 14803469262496058843948213)
                  ·
                    refine ⟨1387825243359005516620145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14803469262496058843948213 1387825243359005516620145)
                    ·
                      rfl

theorem cell22_4054170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_4054170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054170 prefixEnd_4054170 := by exact prefixLift 4054170
  have htrace : WordTrace (prefixWord ++ tailWord_4054170) baseStart_4054170 baseEnd_4054170 := by
    simpa [prefixWord, tailWord_4054170, baseEnd_4054170] using wordTrace_append hprefix tailTrace_4054170
  have hstable : (prefixWord ++ tailWord_4054170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054170).length < 2 ^ (prefixWord ++ tailWord_4054170).sum := by decide
  have hdescent : baseEnd_4054170 < baseStart_4054170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054172 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_4054172 : Nat := 118140960795 + 4054172 * 2 ^ 59
def prefixEnd_4054172 : Nat := 4983230072969 + 3 ^ 40 * 4054172 * 2
def baseEnd_4054172 : Nat := 462608642666626059356713

theorem tailTrace_4054172 : CollatzResearch.WordTrace tailWord_4054172 prefixEnd_4054172 462608642666626059356713 := by
  unfold tailWord_4054172
  simp only [CollatzResearch.WordTrace]
  refine ⟨73933900334217358149066385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98578533778956477532088513 73933900334217358149066385)
  ·
    refine ⟨55450425250663018611799789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73933900334217358149066385 55450425250663018611799789)
    ·
      refine ⟨20793909468998631979424921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55450425250663018611799789 20793909468998631979424921)
      ·
        refine ⟨15595432101748973984568691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20793909468998631979424921 15595432101748973984568691)
        ·
          refine ⟨23393148152623460976853037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15595432101748973984568691 23393148152623460976853037)
          ·
            refine ⟨8772430557233797866319889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23393148152623460976853037 8772430557233797866319889)
            ·
              refine ⟨6579322917925348399739917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772430557233797866319889 6579322917925348399739917)
              ·
                refine ⟨2467246094222005649902469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6579322917925348399739917 2467246094222005649902469)
                ·
                  refine ⟨462608642666626059356713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467246094222005649902469 462608642666626059356713)
                  ·
                    rfl

theorem cell22_4054172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_4054172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054172 prefixEnd_4054172 := by exact prefixLift 4054172
  have htrace : WordTrace (prefixWord ++ tailWord_4054172) baseStart_4054172 baseEnd_4054172 := by
    simpa [prefixWord, tailWord_4054172, baseEnd_4054172] using wordTrace_append hprefix tailTrace_4054172
  have hstable : (prefixWord ++ tailWord_4054172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054172).length < 2 ^ (prefixWord ++ tailWord_4054172).sum := by decide
  have hdescent : baseEnd_4054172 < baseStart_4054172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054174 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_4054174 : Nat := 118140960795 + 4054174 * 2 ^ 59
def prefixEnd_4054174 : Nat := 4983230072969 + 3 ^ 40 * 4054174 * 2
def baseEnd_4054174 : Nat := 1387826612640750839520133

theorem tailTrace_4054174 : CollatzResearch.WordTrace tailWord_4054174 prefixEnd_4054174 1387826612640750839520133 := by
  unfold tailWord_4054174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483484201803433829963197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98578582409618313759803717 18483484201803433829963197)
  ·
    refine ⟨6931306575676287686236199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18483484201803433829963197 6931306575676287686236199)
    ·
      refine ⟨10396959863514431529354299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6931306575676287686236199 10396959863514431529354299)
      ·
        refine ⟨15595439795271647294031449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396959863514431529354299 15595439795271647294031449)
        ·
          refine ⟨11696579846453735470523587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15595439795271647294031449 11696579846453735470523587)
          ·
            refine ⟨17544869769680603205785381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696579846453735470523587 17544869769680603205785381)
            ·
              refine ⟨3289663081815113101084759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17544869769680603205785381 3289663081815113101084759)
              ·
                refine ⟨4934494622722669651627139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289663081815113101084759 4934494622722669651627139)
                ·
                  refine ⟨7401741934084004477440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934494622722669651627139 7401741934084004477440709)
                  ·
                    refine ⟨1387826612640750839520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401741934084004477440709 1387826612640750839520133)
                    ·
                      rfl

theorem cell22_4054174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_4054174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054174 prefixEnd_4054174 := by exact prefixLift 4054174
  have htrace : WordTrace (prefixWord ++ tailWord_4054174) baseStart_4054174 baseEnd_4054174 := by
    simpa [prefixWord, tailWord_4054174, baseEnd_4054174] using wordTrace_append hprefix tailTrace_4054174
  have hstable : (prefixWord ++ tailWord_4054174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054174).length < 2 ^ (prefixWord ++ tailWord_4054174).sum := by decide
  have hdescent : baseEnd_4054174 < baseStart_4054174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054204 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_4054204 : Nat := 118140960795 + 4054204 * 2 ^ 59
def prefixEnd_4054204 : Nat := 4983230072969 + 3 ^ 40 * 4054204 * 2
def baseEnd_4054204 : Nat := 1387836882253840761270041

theorem tailTrace_4054204 : CollatzResearch.WordTrace tailWord_4054204 prefixEnd_4054204 1387836882253840761270041 := by
  unfold tailWord_4054204
  simp only [CollatzResearch.WordTrace]
  refine ⟨73934483902159392881648833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98579311869545857175531777 73934483902159392881648833)
  ·
    refine ⟨55450862926619544661236625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73934483902159392881648833 55450862926619544661236625)
    ·
      refine ⟨41588147194964658495927469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55450862926619544661236625 41588147194964658495927469)
      ·
        refine ⟨15595555198111746935972801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41588147194964658495927469 15595555198111746935972801)
        ·
          refine ⟨11696666398583810201979601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15595555198111746935972801 11696666398583810201979601)
          ·
            refine ⟨8772499798937857651484701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11696666398583810201979601 8772499798937857651484701)
            ·
              refine ⟨3289687424601696619306763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8772499798937857651484701 3289687424601696619306763)
              ·
                refine ⟨4934531136902544928960145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289687424601696619306763 4934531136902544928960145)
                ·
                  refine ⟨3700898352676908696720109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4934531136902544928960145 3700898352676908696720109)
                  ·
                    refine ⟨1387836882253840761270041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700898352676908696720109 1387836882253840761270041)
                    ·
                      rfl

theorem cell22_4054204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_4054204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054204 prefixEnd_4054204 := by exact prefixLift 4054204
  have htrace : WordTrace (prefixWord ++ tailWord_4054204) baseStart_4054204 baseEnd_4054204 := by
    simpa [prefixWord, tailWord_4054204, baseEnd_4054204] using wordTrace_append hprefix tailTrace_4054204
  have hstable : (prefixWord ++ tailWord_4054204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054204).length < 2 ^ (prefixWord ++ tailWord_4054204).sum := by decide
  have hdescent : baseEnd_4054204 < baseStart_4054204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054275 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_4054275 : Nat := 118140960795 + 4054275 * 2 ^ 59
def prefixEnd_4054275 : Nat := 4983230072969 + 3 ^ 40 * 4054275 * 2
def baseEnd_4054275 : Nat := 1387861187004820242744823

theorem tailTrace_4054275 : CollatzResearch.WordTrace tailWord_4054275 prefixEnd_4054275 1387861187004820242744823 := by
  unfold tailWord_4054275
  simp only [CollatzResearch.WordTrace]
  refine ⟨147871557387061564889132279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98581038258041043259421519 147871557387061564889132279)
  ·
    refine ⟨221807336080592347333698419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147871557387061564889132279 221807336080592347333698419)
    ·
      refine ⟨332711004120888521000547629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221807336080592347333698419 332711004120888521000547629)
      ·
        refine ⟨124766626545333195375205361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332711004120888521000547629 124766626545333195375205361)
        ·
          refine ⟨93574969908999896531404021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124766626545333195375205361 93574969908999896531404021)
          ·
            refine ⟨8772653428968740299819127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93574969908999896531404021 8772653428968740299819127)
            ·
              refine ⟨13158980143453110449728691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772653428968740299819127 13158980143453110449728691)
              ·
                refine ⟨19738470215179665674593037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13158980143453110449728691 19738470215179665674593037)
                ·
                  refine ⟨7401926330692374627972389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19738470215179665674593037 7401926330692374627972389)
                  ·
                    refine ⟨1387861187004820242744823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7401926330692374627972389 1387861187004820242744823)
                    ·
                      rfl

theorem cell22_4054275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_4054275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054275 prefixEnd_4054275 := by exact prefixLift 4054275
  have htrace : WordTrace (prefixWord ++ tailWord_4054275) baseStart_4054275 baseEnd_4054275 := by
    simpa [prefixWord, tailWord_4054275, baseEnd_4054275] using wordTrace_append hprefix tailTrace_4054275
  have hstable : (prefixWord ++ tailWord_4054275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054275).length < 2 ^ (prefixWord ++ tailWord_4054275).sum := by decide
  have hdescent : baseEnd_4054275 < baseStart_4054275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054307 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 4]
def baseStart_4054307 : Nat := 118140960795 + 4054307 * 2 ^ 59
def prefixEnd_4054307 : Nat := 4983230072969 + 3 ^ 40 * 4054307 * 2
def baseEnd_4054307 : Nat := 462624047086260941981575

theorem tailTrace_4054307 : CollatzResearch.WordTrace tailWord_4054307 prefixEnd_4054307 462624047086260941981575 := by
  unfold tailWord_4054307
  simp only [CollatzResearch.WordTrace]
  refine ⟨147872724522945634354297175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98581816348630422902864783 147872724522945634354297175)
  ·
    refine ⟨221809086784418451531445763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147872724522945634354297175 221809086784418451531445763)
    ·
      refine ⟨332713630176627677297168645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221809086784418451531445763 332713630176627677297168645)
      ·
        refine ⟨62383805658117689493219121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332713630176627677297168645 62383805658117689493219121)
        ·
          refine ⟨46787854243588267119914341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62383805658117689493219121 46787854243588267119914341)
          ·
            refine ⟨8772722670672800084983939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46787854243588267119914341 8772722670672800084983939)
            ·
              refine ⟨13159084006009200127475909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772722670672800084983939 13159084006009200127475909)
              ·
                refine ⟨2467328251126725023901733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13159084006009200127475909 2467328251126725023901733)
                ·
                  refine ⟨462624047086260941981575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467328251126725023901733 462624047086260941981575)
                  ·
                    rfl

theorem cell22_4054307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 4].length) (baseStart_4054307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054307 prefixEnd_4054307 := by exact prefixLift 4054307
  have htrace : WordTrace (prefixWord ++ tailWord_4054307) baseStart_4054307 baseEnd_4054307 := by
    simpa [prefixWord, tailWord_4054307, baseEnd_4054307] using wordTrace_append hprefix tailTrace_4054307
  have hstable : (prefixWord ++ tailWord_4054307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054307).length < 2 ^ (prefixWord ++ tailWord_4054307).sum := by decide
  have hdescent : baseEnd_4054307 < baseStart_4054307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054322 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_4054322 : Nat := 118140960795 + 4054322 * 2 ^ 59
def prefixEnd_4054322 : Nat := 4983230072969 + 3 ^ 40 * 4054322 * 2
def baseEnd_4054322 : Nat := 1387877276065327786819679

theorem tailTrace_4054322 : CollatzResearch.WordTrace tailWord_4054322 prefixEnd_4054322 1387877276065327786819679 := by
  unfold tailWord_4054322
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968317904472822979023305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98582181078594194610728813 36968317904472822979023305)
  ·
    refine ⟨27726238428354617234267479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36968317904472822979023305 27726238428354617234267479)
    ·
      refine ⟨41589357642531925851401219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27726238428354617234267479 41589357642531925851401219)
      ·
        refine ⟨62384036463797888777101829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41589357642531925851401219 62384036463797888777101829)
        ·
          refine ⟨11697006836962104145706593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62384036463797888777101829 11697006836962104145706593)
          ·
            refine ⟨8772755127721578109279945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11697006836962104145706593 8772755127721578109279945)
            ·
              refine ⟨6579566345791183581959959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772755127721578109279945 6579566345791183581959959)
              ·
                refine ⟨9869349518686775372939939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579566345791183581959959 9869349518686775372939939)
                ·
                  refine ⟨14804024278030163059409909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9869349518686775372939939 14804024278030163059409909)
                  ·
                    refine ⟨1387877276065327786819679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14804024278030163059409909 1387877276065327786819679)
                    ·
                      rfl

theorem cell22_4054322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_4054322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054322 prefixEnd_4054322 := by exact prefixLift 4054322
  have htrace : WordTrace (prefixWord ++ tailWord_4054322) baseStart_4054322 baseEnd_4054322 := by
    simpa [prefixWord, tailWord_4054322, baseEnd_4054322] using wordTrace_append hprefix tailTrace_4054322
  have hstable : (prefixWord ++ tailWord_4054322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054322).length < 2 ^ (prefixWord ++ tailWord_4054322).sum := by decide
  have hdescent : baseEnd_4054322 < baseStart_4054322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054337 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4054337 : Nat := 118140960795 + 4054337 * 2 ^ 59
def prefixEnd_4054337 : Nat := 4983230072969 + 3 ^ 40 * 4054337 * 2
def baseEnd_4054337 : Nat := 1387882410871872747694633

theorem tailTrace_4054337 : CollatzResearch.WordTrace tailWord_4054337 prefixEnd_4054337 1387882410871872747694633 := by
  unfold tailWord_4054337
  simp only [CollatzResearch.WordTrace]
  refine ⟨147873818712836949477889265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98582545808557966318592843 147873818712836949477889265)
  ·
    refine ⟨110905364034627712108416949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147873818712836949477889265 110905364034627712108416949)
    ·
      refine ⟨10397377878246348010164089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110905364034627712108416949 10397377878246348010164089)
      ·
        refine ⟨7798033408684761007623067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10397377878246348010164089 7798033408684761007623067)
        ·
          refine ⟨11697050113027141511434601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798033408684761007623067 11697050113027141511434601)
          ·
            refine ⟨8772787584770356133575951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11697050113027141511434601 8772787584770356133575951)
            ·
              refine ⟨13159181377155534200363927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772787584770356133575951 13159181377155534200363927)
              ·
                refine ⟨19738772065733301300545891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13159181377155534200363927 19738772065733301300545891)
                ·
                  refine ⟨29608158098599951950818837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19738772065733301300545891 29608158098599951950818837)
                  ·
                    refine ⟨1387882410871872747694633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29608158098599951950818837 1387882410871872747694633)
                    ·
                      rfl

theorem cell22_4054337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4054337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054337 prefixEnd_4054337 := by exact prefixLift 4054337
  have htrace : WordTrace (prefixWord ++ tailWord_4054337) baseStart_4054337 baseEnd_4054337 := by
    simpa [prefixWord, tailWord_4054337, baseEnd_4054337] using wordTrace_append hprefix tailTrace_4054337
  have hstable : (prefixWord ++ tailWord_4054337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054337).length < 2 ^ (prefixWord ++ tailWord_4054337).sum := by decide
  have hdescent : baseEnd_4054337 < baseStart_4054337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054358 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4054358 : Nat := 118140960795 + 4054358 * 2 ^ 59
def prefixEnd_4054358 : Nat := 4983230072969 + 3 ^ 40 * 4054358 * 2
def baseEnd_4054358 : Nat := 462629866533678564306523

theorem tailTrace_4054358 : CollatzResearch.WordTrace tailWord_4054358 prefixEnd_4054358 462629866533678564306523 := by
  unfold tailWord_4054358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242161540360054379025233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98583056430507246709602485 9242161540360054379025233)
  ·
    refine ⟨6931621155270040784268925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9242161540360054379025233 6931621155270040784268925)
    ·
      refine ⟨2599357933226265294100847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6931621155270040784268925 2599357933226265294100847)
      ·
        refine ⟨3899036899839397941151271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599357933226265294100847 3899036899839397941151271)
        ·
          refine ⟨5848555349759096911726907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899036899839397941151271 5848555349759096911726907)
          ·
            refine ⟨8772833024638645367590361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848555349759096911726907 8772833024638645367590361)
            ·
              refine ⟨6579624768478984025692771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772833024638645367590361 6579624768478984025692771)
              ·
                refine ⟨9869437152718476038539157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579624768478984025692771 9869437152718476038539157)
                ·
                  refine ⟨462629866533678564306523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9869437152718476038539157 462629866533678564306523)
                  ·
                    rfl

theorem cell22_4054358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4054358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054358 prefixEnd_4054358 := by exact prefixLift 4054358
  have htrace : WordTrace (prefixWord ++ tailWord_4054358) baseStart_4054358 baseEnd_4054358 := by
    simpa [prefixWord, tailWord_4054358, baseEnd_4054358] using wordTrace_append hprefix tailTrace_4054358
  have hstable : (prefixWord ++ tailWord_4054358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054358).length < 2 ^ (prefixWord ++ tailWord_4054358).sum := by decide
  have hdescent : baseEnd_4054358 < baseStart_4054358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054418 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4054418 : Nat := 118140960795 + 4054418 * 2 ^ 59
def prefixEnd_4054418 : Nat := 4983230072969 + 3 ^ 40 * 4054418 * 2
def baseEnd_4054418 : Nat := 1387910138827215536419385

theorem tailTrace_4054418 : CollatzResearch.WordTrace tailWord_4054418 prefixEnd_4054418 1387910138827215536419385 := by
  unfold tailWord_4054418
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969193256385875077896977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98584515350362333541058605 36969193256385875077896977)
  ·
    refine ⟨27726894942289406308422733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36969193256385875077896977 27726894942289406308422733)
    ·
      refine ⟨10397585603358527365658525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27726894942289406308422733 10397585603358527365658525)
      ·
        refine ⟨3899094601259447762121947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10397585603358527365658525 3899094601259447762121947)
        ·
          refine ⟨5848641901889171643182921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3899094601259447762121947 5848641901889171643182921)
          ·
            refine ⟨4386481426416878732387191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5848641901889171643182921 4386481426416878732387191)
            ·
              refine ⟨6579722139625318098580787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386481426416878732387191 6579722139625318098580787)
              ·
                refine ⟨9869583209437977147871181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579722139625318098580787 9869583209437977147871181)
                ·
                  refine ⟨3701093703539241430451693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9869583209437977147871181 3701093703539241430451693)
                  ·
                    refine ⟨1387910138827215536419385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701093703539241430451693 1387910138827215536419385)
                    ·
                      rfl

theorem cell22_4054418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4054418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054418 prefixEnd_4054418 := by exact prefixLift 4054418
  have htrace : WordTrace (prefixWord ++ tailWord_4054418) baseStart_4054418 baseEnd_4054418 := by
    simpa [prefixWord, tailWord_4054418, baseEnd_4054418] using wordTrace_append hprefix tailTrace_4054418
  have hstable : (prefixWord ++ tailWord_4054418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054418).length < 2 ^ (prefixWord ++ tailWord_4054418).sum := by decide
  have hdescent : baseEnd_4054418 < baseStart_4054418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054472 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_4054472 : Nat := 118140960795 + 4054472 * 2 ^ 59
def prefixEnd_4054472 : Nat := 4983230072969 + 3 ^ 40 * 4054472 * 2
def baseEnd_4054472 : Nat := 1387928624130777395569219

theorem tailTrace_4054472 : CollatzResearch.WordTrace tailWord_4054472 prefixEnd_4054472 1387928624130777395569219 := by
  unfold tailWord_4054472
  simp only [CollatzResearch.WordTrace]
  refine ⟨73939371283673933767026835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98585828378231911689369113 73939371283673933767026835)
  ·
    refine ⟨110909056925510900650540253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73939371283673933767026835 110909056925510900650540253)
    ·
      refine ⟨41590896347066587743952595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110909056925510900650540253 41590896347066587743952595)
      ·
        refine ⟨62386344520599881615928893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41590896347066587743952595 62386344520599881615928893)
        ·
          refine ⟨23394879195224955605973335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62386344520599881615928893 23394879195224955605973335)
          ·
            refine ⟨35092318792837433408960003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23394879195224955605973335 35092318792837433408960003)
            ·
              refine ⟨52638478189256150113440005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35092318792837433408960003 52638478189256150113440005)
              ·
                refine ⟨9869714660485528146270001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52638478189256150113440005 9869714660485528146270001)
                ·
                  refine ⟨7402285995364146109702501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9869714660485528146270001 7402285995364146109702501)
                  ·
                    refine ⟨1387928624130777395569219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402285995364146109702501 1387928624130777395569219)
                    ·
                      rfl

theorem cell22_4054472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_4054472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054472 prefixEnd_4054472 := by exact prefixLift 4054472
  have htrace : WordTrace (prefixWord ++ tailWord_4054472) baseStart_4054472 baseEnd_4054472 := by
    simpa [prefixWord, tailWord_4054472, baseEnd_4054472] using wordTrace_append hprefix tailTrace_4054472
  have hstable : (prefixWord ++ tailWord_4054472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054472).length < 2 ^ (prefixWord ++ tailWord_4054472).sum := by decide
  have hdescent : baseEnd_4054472 < baseStart_4054472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054474 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_4054474 : Nat := 118140960795 + 4054474 * 2 ^ 59
def prefixEnd_4054474 : Nat := 4983230072969 + 3 ^ 40 * 4054474 * 2
def baseEnd_4054474 : Nat := 1387929308771650057019213

theorem tailTrace_4054474 : CollatzResearch.WordTrace tailWord_4054474 prefixEnd_4054474 1387929308771650057019213 := by
  unfold tailWord_4054474
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969703878335155468906619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98585877008893747917084317 36969703878335155468906619)
  ·
    refine ⟨55454555817502733203359929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36969703878335155468906619 55454555817502733203359929)
    ·
      refine ⟨41590916863127049902519947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55454555817502733203359929 41590916863127049902519947)
      ·
        refine ⟨62386375294690574853779921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41590916863127049902519947 62386375294690574853779921)
        ·
          refine ⟨46789781471017931140334941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62386375294690574853779921 46789781471017931140334941)
          ·
            refine ⟨17546168051631724177625603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46789781471017931140334941 17546168051631724177625603)
            ·
              refine ⟨26319252077447586266438405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17546168051631724177625603 26319252077447586266438405)
              ·
                refine ⟨4934859764521422424957201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26319252077447586266438405 4934859764521422424957201)
                ·
                  refine ⟨3701144823391066818717901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4934859764521422424957201 3701144823391066818717901)
                  ·
                    refine ⟨1387929308771650057019213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701144823391066818717901 1387929308771650057019213)
                    ·
                      rfl

theorem cell22_4054474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_4054474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054474 prefixEnd_4054474 := by exact prefixLift 4054474
  have htrace : WordTrace (prefixWord ++ tailWord_4054474) baseStart_4054474 baseEnd_4054474 := by
    simpa [prefixWord, tailWord_4054474, baseEnd_4054474] using wordTrace_append hprefix tailTrace_4054474
  have hstable : (prefixWord ++ tailWord_4054474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054474).length < 2 ^ (prefixWord ++ tailWord_4054474).sum := by decide
  have hdescent : baseEnd_4054474 < baseStart_4054474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054476 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_4054476 : Nat := 118140960795 + 4054476 * 2 ^ 59
def prefixEnd_4054476 : Nat := 4983230072969 + 3 ^ 40 * 4054476 * 2
def baseEnd_4054476 : Nat := 462643331137507572823069

theorem tailTrace_4054476 : CollatzResearch.WordTrace tailWord_4054476 prefixEnd_4054476 462643331137507572823069 := by
  unfold tailWord_4054476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73939444229666688108599641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98585925639555584144799521 73939444229666688108599641)
  ·
    refine ⟨55454583172250016081449731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73939444229666688108599641 55454583172250016081449731)
    ·
      refine ⟨83181874758375024122174597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55454583172250016081449731 83181874758375024122174597)
      ·
        refine ⟨15596601517195317022907737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83181874758375024122174597 15596601517195317022907737)
        ·
          refine ⟨11697451137896487767180803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15596601517195317022907737 11697451137896487767180803)
          ·
            refine ⟨17546176706844731650771205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697451137896487767180803 17546176706844731650771205)
            ·
              refine ⟨3289908132533387184519601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17546176706844731650771205 3289908132533387184519601)
              ·
                refine ⟨2467431099400040388389701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289908132533387184519601 2467431099400040388389701)
                ·
                  refine ⟨462643331137507572823069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467431099400040388389701 462643331137507572823069)
                  ·
                    rfl

theorem cell22_4054476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_4054476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054476 prefixEnd_4054476 := by exact prefixLift 4054476
  have htrace : WordTrace (prefixWord ++ tailWord_4054476) baseStart_4054476 baseEnd_4054476 := by
    simpa [prefixWord, tailWord_4054476, baseEnd_4054476] using wordTrace_append hprefix tailTrace_4054476
  have hstable : (prefixWord ++ tailWord_4054476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054476).length < 2 ^ (prefixWord ++ tailWord_4054476).sum := by decide
  have hdescent : baseEnd_4054476 < baseStart_4054476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054506 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_4054506 : Nat := 118140960795 + 4054506 * 2 ^ 59
def prefixEnd_4054506 : Nat := 4983230072969 + 3 ^ 40 * 4054506 * 2
def baseEnd_4054506 : Nat := 1387940263025612640219115

theorem tailTrace_4054506 : CollatzResearch.WordTrace tailWord_4054506 prefixEnd_4054506 1387940263025612640219115 := by
  unfold tailWord_4054506
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969995662306172835197843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98586655099483127560527581 36969995662306172835197843)
  ·
    refine ⟨55454993493459259252796765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36969995662306172835197843 55454993493459259252796765)
    ·
      refine ⟨20795622560047222219798787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55454993493459259252796765 20795622560047222219798787)
      ·
        refine ⟨31193433840070833329698181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20795622560047222219798787 31193433840070833329698181)
        ·
          refine ⟨5848768845013281249318409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31193433840070833329698181 5848768845013281249318409)
          ·
            refine ⟨4386576633759960936988807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5848768845013281249318409 4386576633759960936988807)
            ·
              refine ⟨6579864950639941405483211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386576633759960936988807 6579864950639941405483211)
              ·
                refine ⟨9869797425959912108224817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579864950639941405483211 9869797425959912108224817)
                ·
                  refine ⟨7402348069469934081168613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9869797425959912108224817 7402348069469934081168613)
                  ·
                    refine ⟨1387940263025612640219115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402348069469934081168613 1387940263025612640219115)
                    ·
                      rfl

theorem cell22_4054506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_4054506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054506 prefixEnd_4054506 := by exact prefixLift 4054506
  have htrace : WordTrace (prefixWord ++ tailWord_4054506) baseStart_4054506 baseEnd_4054506 := by
    simpa [prefixWord, tailWord_4054506, baseEnd_4054506] using wordTrace_append hprefix tailTrace_4054506
  have hstable : (prefixWord ++ tailWord_4054506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054506).length < 2 ^ (prefixWord ++ tailWord_4054506).sum := by decide
  have hdescent : baseEnd_4054506 < baseStart_4054506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054536 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 1, 3]
def baseStart_4054536 : Nat := 118140960795 + 4054536 * 2 ^ 59
def prefixEnd_4054536 : Nat := 4983230072969 + 3 ^ 40 * 4054536 * 2
def baseEnd_4054536 : Nat := 1387950532638702561969023

theorem tailTrace_4054536 : CollatzResearch.WordTrace tailWord_4054536 prefixEnd_4054536 1387950532638702561969023 := by
  unfold tailWord_4054536
  simp only [CollatzResearch.WordTrace]
  refine ⟨73940538419558003232191731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98587384559410670976255641 73940538419558003232191731)
  ·
    refine ⟨110910807629337004848287597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73940538419558003232191731 110910807629337004848287597)
    ·
      refine ⟨41591552861001376818107849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110910807629337004848287597 41591552861001376818107849)
      ·
        refine ⟨31193664645751032613580887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41591552861001376818107849 31193664645751032613580887)
        ·
          refine ⟨46790496968626548920371331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31193664645751032613580887 46790496968626548920371331)
          ·
            refine ⟨70185745452939823380556997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46790496968626548920371331 70185745452939823380556997)
            ·
              refine ⟨13159827272426216883854437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70185745452939823380556997 13159827272426216883854437)
              ·
                refine ⟨2467467613579915665722707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13159827272426216883854437 2467467613579915665722707)
                ·
                  refine ⟨3701201420369873498584061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467467613579915665722707 3701201420369873498584061)
                  ·
                    refine ⟨1387950532638702561969023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701201420369873498584061 1387950532638702561969023)
                    ·
                      rfl

theorem cell22_4054536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_4054536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054536 prefixEnd_4054536 := by exact prefixLift 4054536
  have htrace : WordTrace (prefixWord ++ tailWord_4054536) baseStart_4054536 baseEnd_4054536 := by
    simpa [prefixWord, tailWord_4054536, baseEnd_4054536] using wordTrace_append hprefix tailTrace_4054536
  have hstable : (prefixWord ++ tailWord_4054536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054536).length < 2 ^ (prefixWord ++ tailWord_4054536).sum := by decide
  have hdescent : baseEnd_4054536 < baseStart_4054536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054547 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_4054547 : Nat := 118140960795 + 4054547 * 2 ^ 59
def prefixEnd_4054547 : Nat := 4983230072969 + 3 ^ 40 * 4054547 * 2
def baseEnd_4054547 : Nat := 1387954298163502199943989

theorem tailTrace_4054547 : CollatzResearch.WordTrace tailWord_4054547 prefixEnd_4054547 1387954298163502199943989 := by
  unfold tailWord_4054547
  simp only [CollatzResearch.WordTrace]
  refine ⟨147881478042076155343033895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98587652028050770228689263 147881478042076155343033895)
  ·
    refine ⟨221822217063114233014550843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147881478042076155343033895 221822217063114233014550843)
    ·
      refine ⟨332733325594671349521826265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221822217063114233014550843 332733325594671349521826265)
      ·
        refine ⟨249549994196003512141369699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332733325594671349521826265 249549994196003512141369699)
        ·
          refine ⟨374324991294005268212054549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249549994196003512141369699 374324991294005268212054549)
          ·
            refine ⟨17546483966906496947440057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 374324991294005268212054549 17546483966906496947440057)
            ·
              refine ⟨13159862975179872710580043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17546483966906496947440057 13159862975179872710580043)
              ·
                refine ⟨19739794462769809065870065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13159862975179872710580043 19739794462769809065870065)
                ·
                  refine ⟨14804845847077356799402549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19739794462769809065870065 14804845847077356799402549)
                  ·
                    refine ⟨1387954298163502199943989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14804845847077356799402549 1387954298163502199943989)
                    ·
                      rfl

theorem cell22_4054547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_4054547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054547 prefixEnd_4054547 := by exact prefixLift 4054547
  have htrace : WordTrace (prefixWord ++ tailWord_4054547) baseStart_4054547 baseEnd_4054547 := by
    simpa [prefixWord, tailWord_4054547, baseEnd_4054547] using wordTrace_append hprefix tailTrace_4054547
  have hstable : (prefixWord ++ tailWord_4054547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054547).length < 2 ^ (prefixWord ++ tailWord_4054547).sum := by decide
  have hdescent : baseEnd_4054547 < baseStart_4054547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054579 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 1, 4]
def baseStart_4054579 : Nat := 118140960795 + 4054579 * 2 ^ 59
def prefixEnd_4054579 : Nat := 4983230072969 + 3 ^ 40 * 4054579 * 2
def baseEnd_4054579 : Nat := 1387965252417464783143891

theorem tailTrace_4054579 : CollatzResearch.WordTrace tailWord_4054579 prefixEnd_4054579 1387965252417464783143891 := by
  unfold tailWord_4054579
  simp only [CollatzResearch.WordTrace]
  refine ⟨147882645177960224808198791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98588430118640149872132527 147882645177960224808198791)
  ·
    refine ⟨221823967766940337212298187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147882645177960224808198791 221823967766940337212298187)
    ·
      refine ⟨332735951650410505818447281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221823967766940337212298187 332735951650410505818447281)
      ·
        refine ⟨249551963737807879363835461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332735951650410505818447281 249551963737807879363835461)
        ·
          refine ⟨46790993200838977380719149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249551963737807879363835461 46790993200838977380719149)
          ·
            refine ⟨17546622450314616517769681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46790993200838977380719149 17546622450314616517769681)
            ·
              refine ⟨13159966837735962388327261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17546622450314616517769681 13159966837735962388327261)
              ·
                refine ⟨4934987564150985895622723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13159966837735962388327261 4934987564150985895622723)
                ·
                  refine ⟨7402481346226478843434085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934987564150985895622723 7402481346226478843434085)
                  ·
                    refine ⟨1387965252417464783143891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402481346226478843434085 1387965252417464783143891)
                    ·
                      rfl

theorem cell22_4054579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4].length) (baseStart_4054579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054579 prefixEnd_4054579 := by exact prefixLift 4054579
  have htrace : WordTrace (prefixWord ++ tailWord_4054579) baseStart_4054579 baseEnd_4054579 := by
    simpa [prefixWord, tailWord_4054579, baseEnd_4054579] using wordTrace_append hprefix tailTrace_4054579
  have hstable : (prefixWord ++ tailWord_4054579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054579).length < 2 ^ (prefixWord ++ tailWord_4054579).sum := by decide
  have hdescent : baseEnd_4054579 < baseStart_4054579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054607 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_4054607 : Nat := 118140960795 + 4054607 * 2 ^ 59
def prefixEnd_4054607 : Nat := 4983230072969 + 3 ^ 40 * 4054607 * 2
def baseEnd_4054607 : Nat := 1387974837389682043443805

theorem tailTrace_4054607 : CollatzResearch.WordTrace tailWord_4054607 prefixEnd_4054607 1387974837389682043443805 := by
  unfold tailWord_4054607
  simp only [CollatzResearch.WordTrace]
  refine ⟨147883666421858785590218075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98589110947905857060145383 147883666421858785590218075)
  ·
    refine ⟨221825499632788178385327113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147883666421858785590218075 221825499632788178385327113)
    ·
      refine ⟨166369124724591133788995335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221825499632788178385327113 166369124724591133788995335)
      ·
        refine ⟨249553687086886700683493003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166369124724591133788995335 249553687086886700683493003)
        ·
          refine ⟨374330530630330051025239505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249553687086886700683493003 374330530630330051025239505)
          ·
            refine ⟨280747897972747538268929629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374330530630330051025239505 280747897972747538268929629)
            ·
              refine ⟨105280461739780326850848611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280747897972747538268929629 105280461739780326850848611)
              ·
                refine ⟨157920692609670490276272917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105280461739780326850848611 157920692609670490276272917)
                ·
                  refine ⟨7402532466078304231700293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157920692609670490276272917 7402532466078304231700293)
                  ·
                    refine ⟨1387974837389682043443805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402532466078304231700293 1387974837389682043443805)
                    ·
                      rfl

theorem cell22_4054607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_4054607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054607 prefixEnd_4054607 := by exact prefixLift 4054607
  have htrace : WordTrace (prefixWord ++ tailWord_4054607) baseStart_4054607 baseEnd_4054607 := by
    simpa [prefixWord, tailWord_4054607, baseEnd_4054607] using wordTrace_append hprefix tailTrace_4054607
  have hstable : (prefixWord ++ tailWord_4054607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054607).length < 2 ^ (prefixWord ++ tailWord_4054607).sum := by decide
  have hdescent : baseEnd_4054607 < baseStart_4054607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054645 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 4]
def baseStart_4054645 : Nat := 118140960795 + 4054645 * 2 ^ 59
def prefixEnd_4054645 : Nat := 4983230072969 + 3 ^ 40 * 4054645 * 2
def baseEnd_4054645 : Nat := 462662615188754203664563

theorem tailTrace_4054645 : CollatzResearch.WordTrace tailWord_4054645 prefixEnd_4054645 462662615188754203664563 := by
  unfold tailWord_4054645
  simp only [CollatzResearch.WordTrace]
  refine ⟨147885052395721118080101389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98590034930480745386734259 147885052395721118080101389)
  ·
    refine ⟨55456894648395419280038021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147885052395721118080101389 55456894648395419280038021)
    ·
      refine ⟨10398167746574141115007129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55456894648395419280038021 10398167746574141115007129)
      ·
        refine ⟨7798625809930605836255347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10398167746574141115007129 7798625809930605836255347)
        ·
          refine ⟨11697938714895908754383021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798625809930605836255347 11697938714895908754383021)
          ·
            refine ⟨4386727018085965782893633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11697938714895908754383021 4386727018085965782893633)
            ·
              refine ⟨3290045263564474337170225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4386727018085965782893633 3290045263564474337170225)
              ·
                refine ⟨2467533947673355752877669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290045263564474337170225 2467533947673355752877669)
                ·
                  refine ⟨462662615188754203664563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467533947673355752877669 462662615188754203664563)
                  ·
                    rfl

theorem cell22_4054645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_4054645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054645 prefixEnd_4054645 := by exact prefixLift 4054645
  have htrace : WordTrace (prefixWord ++ tailWord_4054645) baseStart_4054645 baseEnd_4054645 := by
    simpa [prefixWord, tailWord_4054645, baseEnd_4054645] using wordTrace_append hprefix tailTrace_4054645
  have hstable : (prefixWord ++ tailWord_4054645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054645).length < 2 ^ (prefixWord ++ tailWord_4054645).sum := by decide
  have hdescent : baseEnd_4054645 < baseStart_4054645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054688 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 1, 3]
def baseStart_4054688 : Nat := 118140960795 + 4054688 * 2 ^ 59
def prefixEnd_4054688 : Nat := 4983230072969 + 3 ^ 40 * 4054688 * 2
def baseEnd_4054688 : Nat := 1388002565345024832168557

theorem tailTrace_4054688 : CollatzResearch.WordTrace tailWord_4054688 prefixEnd_4054688 1388002565345024832168557 := by
  unfold tailWord_4054688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73943310367282668211958359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98591080489710224282611145 73943310367282668211958359)
  ·
    refine ⟨110914965550924002317937539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73943310367282668211958359 110914965550924002317937539)
    ·
      refine ⟨166372448326386003476906309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110914965550924002317937539 166372448326386003476906309)
      ·
        refine ⟨31194834061197375651919933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166372448326386003476906309 31194834061197375651919933)
        ·
          refine ⟨11698062772949015869469975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31194834061197375651919933 11698062772949015869469975)
          ·
            refine ⟨17547094159423523804204963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698062772949015869469975 17547094159423523804204963)
            ·
              refine ⟨26320641239135285706307445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17547094159423523804204963 26320641239135285706307445)
              ·
                refine ⟨2467560116168933034966323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26320641239135285706307445 2467560116168933034966323)
                ·
                  refine ⟨3701340174253399552449485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467560116168933034966323 3701340174253399552449485)
                  ·
                    refine ⟨1388002565345024832168557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701340174253399552449485 1388002565345024832168557)
                    ·
                      rfl

theorem cell22_4054688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_4054688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054688 prefixEnd_4054688 := by exact prefixLift 4054688
  have htrace : WordTrace (prefixWord ++ tailWord_4054688) baseStart_4054688 baseEnd_4054688 := by
    simpa [prefixWord, tailWord_4054688, baseEnd_4054688] using wordTrace_append hprefix tailTrace_4054688
  have hstable : (prefixWord ++ tailWord_4054688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054688).length < 2 ^ (prefixWord ++ tailWord_4054688).sum := by decide
  have hdescent : baseEnd_4054688 < baseStart_4054688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054697 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_4054697 : Nat := 118140960795 + 4054697 * 2 ^ 59
def prefixEnd_4054697 : Nat := 4983230072969 + 3 ^ 40 * 4054697 * 2
def baseEnd_4054697 : Nat := 1388005646228951808693529

theorem tailTrace_4054697 : CollatzResearch.WordTrace tailWord_4054697 prefixEnd_4054697 1388005646228951808693529 := by
  unfold tailWord_4054697
  simp only [CollatzResearch.WordTrace]
  refine ⟨147886948991532730960994345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98591299327688487307329563 147886948991532730960994345)
  ·
    refine ⟨110915211743649548220745759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147886948991532730960994345 110915211743649548220745759)
    ·
      refine ⟨166372817615474322331118639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110915211743649548220745759 166372817615474322331118639)
      ·
        refine ⟨249559226423211483496677959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166372817615474322331118639 249559226423211483496677959)
        ·
          refine ⟨374338839634817225245016939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249559226423211483496677959 374338839634817225245016939)
          ·
            refine ⟨561508259452225837867525409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374338839634817225245016939 561508259452225837867525409)
            ·
              refine ⟨421131194589169378400644057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561508259452225837867525409 421131194589169378400644057)
              ·
                refine ⟨315848395941877033800483043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421131194589169378400644057 315848395941877033800483043)
                ·
                  refine ⟨473772593912815550700724565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315848395941877033800483043 473772593912815550700724565)
                  ·
                    refine ⟨1388005646228951808693529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 473772593912815550700724565 1388005646228951808693529)
                    ·
                      rfl

theorem cell22_4054697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_4054697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054697 prefixEnd_4054697 := by exact prefixLift 4054697
  have htrace : WordTrace (prefixWord ++ tailWord_4054697) baseStart_4054697 baseEnd_4054697 := by
    simpa [prefixWord, tailWord_4054697, baseEnd_4054697] using wordTrace_append hprefix tailTrace_4054697
  have hstable : (prefixWord ++ tailWord_4054697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054697).length < 2 ^ (prefixWord ++ tailWord_4054697).sum := by decide
  have hdescent : baseEnd_4054697 < baseStart_4054697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054718 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_4054718 : Nat := 118140960795 + 4054718 * 2 ^ 59
def prefixEnd_4054718 : Nat := 4983230072969 + 3 ^ 40 * 4054718 * 2
def baseEnd_4054718 : Nat := 462670944986038251306155

theorem tailTrace_4054718 : CollatzResearch.WordTrace tailWord_4054718 prefixEnd_4054718 462670944986038251306155 := by
  unfold tailWord_4054718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18485964365557081443438601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98591809949637767698339205 18485964365557081443438601)
  ·
    refine ⟨13864473274167811082578951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18485964365557081443438601 13864473274167811082578951)
    ·
      refine ⟨20796709911251716623868427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13864473274167811082578951 20796709911251716623868427)
      ·
        refine ⟨31195064866877574935802641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796709911251716623868427 31195064866877574935802641)
        ·
          refine ⟨23396298650158181201851981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31195064866877574935802641 23396298650158181201851981)
          ·
            refine ⟨8773611993809317950694493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23396298650158181201851981 8773611993809317950694493)
            ·
              refine ⟨3290104497678494231510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8773611993809317950694493 3290104497678494231510435)
              ·
                refine ⟨4935156746517741347265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290104497678494231510435 4935156746517741347265653)
                ·
                  refine ⟨462670944986038251306155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935156746517741347265653 462670944986038251306155)
                  ·
                    rfl

theorem cell22_4054718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_4054718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054718 prefixEnd_4054718 := by exact prefixLift 4054718
  have htrace : WordTrace (prefixWord ++ tailWord_4054718) baseStart_4054718 baseEnd_4054718 := by
    simpa [prefixWord, tailWord_4054718, baseEnd_4054718] using wordTrace_append hprefix tailTrace_4054718
  have hstable : (prefixWord ++ tailWord_4054718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054718).length < 2 ^ (prefixWord ++ tailWord_4054718).sum := by decide
  have hdescent : baseEnd_4054718 < baseStart_4054718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054744 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_4054744 : Nat := 118140960795 + 4054744 * 2 ^ 59
def prefixEnd_4054744 : Nat := 4983230072969 + 3 ^ 40 * 4054744 * 2
def baseEnd_4054744 : Nat := 1388021735289459352768385

theorem tailTrace_4054744 : CollatzResearch.WordTrace tailWord_4054744 prefixEnd_4054744 1388021735289459352768385 := by
  unfold tailWord_4054744
  simp only [CollatzResearch.WordTrace]
  refine ⟨73944331611181228993977643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98592442148241638658636857 73944331611181228993977643)
  ·
    refine ⟨110916497416771843490966465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73944331611181228993977643 110916497416771843490966465)
    ·
      refine ⟨83187373062578882618224849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110916497416771843490966465 83187373062578882618224849)
      ·
        refine ⟨62390529796934161963668637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83187373062578882618224849 62390529796934161963668637)
        ·
          refine ⟨23396448673850310736375739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62390529796934161963668637 23396448673850310736375739)
          ·
            refine ⟨35094673010775466104563609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23396448673850310736375739 35094673010775466104563609)
            ·
              refine ⟨26321004758081599578422707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35094673010775466104563609 26321004758081599578422707)
              ·
                refine ⟨39481507137122399367634061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26321004758081599578422707 39481507137122399367634061)
                ·
                  refine ⟨14805565176420899762862773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39481507137122399367634061 14805565176420899762862773)
                  ·
                    refine ⟨1388021735289459352768385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14805565176420899762862773 1388021735289459352768385)
                    ·
                      rfl

theorem cell22_4054744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_4054744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054744 prefixEnd_4054744 := by exact prefixLift 4054744
  have htrace : WordTrace (prefixWord ++ tailWord_4054744) baseStart_4054744 baseEnd_4054744 := by
    simpa [prefixWord, tailWord_4054744, baseEnd_4054744] using wordTrace_append hprefix tailTrace_4054744
  have hstable : (prefixWord ++ tailWord_4054744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054744).length < 2 ^ (prefixWord ++ tailWord_4054744).sum := by decide
  have hdescent : baseEnd_4054744 < baseStart_4054744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054761 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_4054761 : Nat := 118140960795 + 4054761 * 2 ^ 59
def prefixEnd_4054761 : Nat := 4983230072969 + 3 ^ 40 * 4054761 * 2
def baseEnd_4054761 : Nat := 1388027554736876975093333

theorem tailTrace_4054761 : CollatzResearch.WordTrace tailWord_4054761 prefixEnd_4054761 1388027554736876975093333 := by
  unfold tailWord_4054761
  simp only [CollatzResearch.WordTrace]
  refine ⟨147889283263300869891324137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98592855508867246594216091 147889283263300869891324137)
  ·
    refine ⟨110916962447475652418493103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147889283263300869891324137 110916962447475652418493103)
    ·
      refine ⟨166375443671213478627739655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110916962447475652418493103 166375443671213478627739655)
      ·
        refine ⟨249563165506820217941609483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166375443671213478627739655 249563165506820217941609483)
        ·
          refine ⟨374344748260230326912414225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249563165506820217941609483 374344748260230326912414225)
          ·
            refine ⟨280758561195172745184310669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374344748260230326912414225 280758561195172745184310669)
            ·
              refine ⟨105284460448189779444116501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280758561195172745184310669 105284460448189779444116501)
              ·
                refine ⟨4935209083508895911442961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105284460448189779444116501 4935209083508895911442961)
                ·
                  refine ⟨3701406812631671933582221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4935209083508895911442961 3701406812631671933582221)
                  ·
                    refine ⟨1388027554736876975093333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701406812631671933582221 1388027554736876975093333)
                    ·
                      rfl

theorem cell22_4054761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_4054761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054761 prefixEnd_4054761 := by exact prefixLift 4054761
  have htrace : WordTrace (prefixWord ++ tailWord_4054761) baseStart_4054761 baseEnd_4054761 := by
    simpa [prefixWord, tailWord_4054761, baseEnd_4054761] using wordTrace_append hprefix tailTrace_4054761
  have hstable : (prefixWord ++ tailWord_4054761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054761).length < 2 ^ (prefixWord ++ tailWord_4054761).sum := by decide
  have hdescent : baseEnd_4054761 < baseStart_4054761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054782 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4054782 : Nat := 118140960795 + 4054782 * 2 ^ 59
def prefixEnd_4054782 : Nat := 4983230072969 + 3 ^ 40 * 4054782 * 2
def baseEnd_4054782 : Nat := 1388034743466039920318269

theorem tailTrace_4054782 : CollatzResearch.WordTrace tailWord_4054782 prefixEnd_4054782 1388034743466039920318269 := by
  unfold tailWord_4054782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486256149528098809729825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98593366130816526985225733 18486256149528098809729825)
  ·
    refine ⟨13864692112146074107297369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18486256149528098809729825 13864692112146074107297369)
    ·
      refine ⟨10398519084109555580473027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13864692112146074107297369 10398519084109555580473027)
      ·
        refine ⟨15597778626164333370709541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10398519084109555580473027 15597778626164333370709541)
        ·
          refine ⟨2924583492405812507008039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15597778626164333370709541 2924583492405812507008039)
          ·
            refine ⟨4386875238608718760512059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2924583492405812507008039 4386875238608718760512059)
            ·
              refine ⟨6580312857913078140768089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386875238608718760512059 6580312857913078140768089)
              ·
                refine ⟨4935234643434808605576067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6580312857913078140768089 4935234643434808605576067)
                ·
                  refine ⟨7402851965152212908364101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935234643434808605576067 7402851965152212908364101)
                  ·
                    refine ⟨1388034743466039920318269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7402851965152212908364101 1388034743466039920318269)
                    ·
                      rfl

theorem cell22_4054782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4054782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054782 prefixEnd_4054782 := by exact prefixLift 4054782
  have htrace : WordTrace (prefixWord ++ tailWord_4054782) baseStart_4054782 baseEnd_4054782 := by
    simpa [prefixWord, tailWord_4054782, baseEnd_4054782] using wordTrace_append hprefix tailTrace_4054782
  have hstable : (prefixWord ++ tailWord_4054782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054782).length < 2 ^ (prefixWord ++ tailWord_4054782).sum := by decide
  have hdescent : baseEnd_4054782 < baseStart_4054782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054819 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 7]
def baseStart_4054819 : Nat := 118140960795 + 4054819 * 2 ^ 59
def prefixEnd_4054819 : Nat := 4983230072969 + 3 ^ 40 * 4054819 * 2
def baseEnd_4054819 : Nat := 462682469774061385714385

theorem tailTrace_4054819 : CollatzResearch.WordTrace tailWord_4054819 prefixEnd_4054819 462682469774061385714385 := by
  unfold tailWord_4054819
  simp only [CollatzResearch.WordTrace]
  refine ⟨147891398697090745796935511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98594265798060497197957007 147891398697090745796935511)
  ·
    refine ⟨221837098045636118695403267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147891398697090745796935511 221837098045636118695403267)
    ·
      refine ⟨332755647068454178043104901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221837098045636118695403267 332755647068454178043104901)
      ·
        refine ⟨62391683825335158383082169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332755647068454178043104901 62391683825335158383082169)
        ·
          refine ⟨46793762869001368787311627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62391683825335158383082169 46793762869001368787311627)
          ·
            refine ⟨70190644303502053180967441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46793762869001368787311627 70190644303502053180967441)
            ·
              refine ⟨52642983227626539885725581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70190644303502053180967441 52642983227626539885725581)
              ·
                refine ⟨19741118710359952457147093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52642983227626539885725581 19741118710359952457147093)
                ·
                  refine ⟨462682469774061385714385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19741118710359952457147093 462682469774061385714385)
                  ·
                    rfl

theorem cell22_4054819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_4054819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054819 prefixEnd_4054819 := by exact prefixLift 4054819
  have htrace : WordTrace (prefixWord ++ tailWord_4054819) baseStart_4054819 baseEnd_4054819 := by
    simpa [prefixWord, tailWord_4054819, baseEnd_4054819] using wordTrace_append hprefix tailTrace_4054819
  have hstable : (prefixWord ++ tailWord_4054819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054819).length < 2 ^ (prefixWord ++ tailWord_4054819).sum := by decide
  have hdescent : baseEnd_4054819 < baseStart_4054819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054864 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_4054864 : Nat := 118140960795 + 4054864 * 2 ^ 59
def prefixEnd_4054864 : Nat := 4983230072969 + 3 ^ 40 * 4054864 * 2
def baseEnd_4054864 : Nat := 462687604580606346589339

theorem tailTrace_4054864 : CollatzResearch.WordTrace tailWord_4054864 prefixEnd_4054864 462687604580606346589339 := by
  unfold tailWord_4054864
  simp only [CollatzResearch.WordTrace]
  refine ⟨73946519990963859241161823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98595359987951812321549097 73946519990963859241161823)
  ·
    refine ⟨110919779986445788861742735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73946519990963859241161823 110919779986445788861742735)
    ·
      refine ⟨166379669979668683292614103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110919779986445788861742735 166379669979668683292614103)
      ·
        refine ⟨249569504969503024938921155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166379669979668683292614103 249569504969503024938921155)
        ·
          refine ⟨374354257454254537408381733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249569504969503024938921155 374354257454254537408381733)
          ·
            refine ⟨70191423272672725764071575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374354257454254537408381733 70191423272672725764071575)
            ·
              refine ⟨105287134909009088646107363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70191423272672725764071575 105287134909009088646107363)
              ·
                refine ⟨157930702363513632969161045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105287134909009088646107363 157930702363513632969161045)
                ·
                  refine ⟨462687604580606346589339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 157930702363513632969161045 462687604580606346589339)
                  ·
                    rfl

theorem cell22_4054864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_4054864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054864 prefixEnd_4054864 := by exact prefixLift 4054864
  have htrace : WordTrace (prefixWord ++ tailWord_4054864) baseStart_4054864 baseEnd_4054864 := by
    simpa [prefixWord, tailWord_4054864, baseEnd_4054864] using wordTrace_append hprefix tailTrace_4054864
  have hstable : (prefixWord ++ tailWord_4054864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054864).length < 2 ^ (prefixWord ++ tailWord_4054864).sum := by decide
  have hdescent : baseEnd_4054864 < baseStart_4054864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054881 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 6]
def baseStart_4054881 : Nat := 118140960795 + 4054881 * 2 ^ 59
def prefixEnd_4054881 : Nat := 4983230072969 + 3 ^ 40 * 4054881 * 2
def baseEnd_4054881 : Nat := 462689544396412220697655

theorem tailTrace_4054881 : CollatzResearch.WordTrace tailWord_4054881 prefixEnd_4054881 462689544396412220697655 := by
  unfold tailWord_4054881
  simp only [CollatzResearch.WordTrace]
  refine ⟨147893660022866130385692497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98595773348577420257128331 147893660022866130385692497)
  ·
    refine ⟨110920245017149597789269373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147893660022866130385692497 110920245017149597789269373)
    ·
      refine ⟨41595091881431099170976015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110920245017149597789269373 41595091881431099170976015)
      ·
        refine ⟨62392637822146648756464023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41595091881431099170976015 62392637822146648756464023)
        ·
          refine ⟨93588956733219973134696035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62392637822146648756464023 93588956733219973134696035)
          ·
            refine ⟨140383435099829959702044053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93588956733219973134696035 140383435099829959702044053)
            ·
              refine ⟨6580473520304529361033315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140383435099829959702044053 6580473520304529361033315)
              ·
                refine ⟨9870710280456794041549973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580473520304529361033315 9870710280456794041549973)
                ·
                  refine ⟨462689544396412220697655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9870710280456794041549973 462689544396412220697655)
                  ·
                    rfl

theorem cell22_4054881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_4054881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054881 prefixEnd_4054881 := by exact prefixLift 4054881
  have htrace : WordTrace (prefixWord ++ tailWord_4054881) baseStart_4054881 baseEnd_4054881 := by
    simpa [prefixWord, tailWord_4054881, baseEnd_4054881] using wordTrace_append hprefix tailTrace_4054881
  have hstable : (prefixWord ++ tailWord_4054881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054881).length < 2 ^ (prefixWord ++ tailWord_4054881).sum := by decide
  have hdescent : baseEnd_4054881 < baseStart_4054881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054911 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_4054911 : Nat := 118140960795 + 4054911 * 2 ^ 59
def prefixEnd_4054911 : Nat := 4983230072969 + 3 ^ 40 * 4054911 * 2
def baseEnd_4054911 : Nat := 1388078902802326583842873

theorem tailTrace_4054911 : CollatzResearch.WordTrace tailWord_4054911 prefixEnd_4054911 1388078902802326583842873 := by
  unfold tailWord_4054911
  simp only [CollatzResearch.WordTrace]
  refine ⟨147894754212757445509284587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98596502808504963672856391 147894754212757445509284587)
  ·
    refine ⟨221842131319136168263926881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147894754212757445509284587 221842131319136168263926881)
    ·
      refine ⟨166381598489352126197945161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221842131319136168263926881 166381598489352126197945161)
      ·
        refine ⟨124786198867014094648458871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166381598489352126197945161 124786198867014094648458871)
        ·
          refine ⟨187179298300521141972688307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124786198867014094648458871 187179298300521141972688307)
          ·
            refine ⟨280768947450781712959032461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187179298300521141972688307 280768947450781712959032461)
            ·
              refine ⟨105288355294043142359637173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280768947450781712959032461 105288355294043142359637173)
              ·
                refine ⟨9870783308816544596215985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105288355294043142359637173 9870783308816544596215985)
                ·
                  refine ⟨7403087481612408447161989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9870783308816544596215985 7403087481612408447161989)
                  ·
                    refine ⟨1388078902802326583842873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403087481612408447161989 1388078902802326583842873)
                    ·
                      rfl

theorem cell22_4054911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_4054911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054911 prefixEnd_4054911 := by exact prefixLift 4054911
  have htrace : WordTrace (prefixWord ++ tailWord_4054911) baseStart_4054911 baseEnd_4054911 := by
    simpa [prefixWord, tailWord_4054911, baseEnd_4054911] using wordTrace_append hprefix tailTrace_4054911
  have hstable : (prefixWord ++ tailWord_4054911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054911).length < 2 ^ (prefixWord ++ tailWord_4054911).sum := by decide
  have hdescent : baseEnd_4054911 < baseStart_4054911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054915 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 4]
def baseStart_4054915 : Nat := 118140960795 + 4054915 * 2 ^ 59
def prefixEnd_4054915 : Nat := 4983230072969 + 3 ^ 40 * 4054915 * 2
def baseEnd_4054915 : Nat := 462693424028023968914287

theorem tailTrace_4054915 : CollatzResearch.WordTrace tailWord_4054915 prefixEnd_4054915 462693424028023968914287 := by
  unfold tailWord_4054915
  simp only [CollatzResearch.WordTrace]
  refine ⟨147894900104742954192430199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98596600069828636128286799 147894900104742954192430199)
  ·
    refine ⟨221842350157114431288645299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147894900104742954192430199 221842350157114431288645299)
    ·
      refine ⟨332763525235671646932967949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221842350157114431288645299 332763525235671646932967949)
      ·
        refine ⟨124786321963376867599862981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332763525235671646932967949 124786321963376867599862981)
        ·
          refine ⟨23397435368133162674974309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124786321963376867599862981 23397435368133162674974309)
          ·
            refine ⟨4387019131524968001557683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23397435368133162674974309 4387019131524968001557683)
            ·
              refine ⟨6580528697287452002336525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387019131524968001557683 6580528697287452002336525)
              ·
                refine ⟨2467698261482794500876197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6580528697287452002336525 2467698261482794500876197)
                ·
                  refine ⟨462693424028023968914287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467698261482794500876197 462693424028023968914287)
                  ·
                    rfl

theorem cell22_4054915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 4].length) (baseStart_4054915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054915 prefixEnd_4054915 := by exact prefixLift 4054915
  have htrace : WordTrace (prefixWord ++ tailWord_4054915) baseStart_4054915 baseEnd_4054915 := by
    simpa [prefixWord, tailWord_4054915, baseEnd_4054915] using wordTrace_append hprefix tailTrace_4054915
  have hstable : (prefixWord ++ tailWord_4054915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054915).length < 2 ^ (prefixWord ++ tailWord_4054915).sum := by decide
  have hdescent : baseEnd_4054915 < baseStart_4054915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054930 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4054930 : Nat := 118140960795 + 4054930 * 2 ^ 59
def prefixEnd_4054930 : Nat := 4983230072969 + 3 ^ 40 * 4054930 * 2
def baseEnd_4054930 : Nat := 1388085406890616867617815

theorem tailTrace_4054930 : CollatzResearch.WordTrace tailWord_4054930 prefixEnd_4054930 1388085406890616867617815 := by
  unfold tailWord_4054930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36973861799922152938556561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98596964799792407836150829 36973861799922152938556561)
  ·
    refine ⟨27730396349941614703917421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36973861799922152938556561 27730396349941614703917421)
    ·
      refine ⟨10398898631228105513969033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27730396349941614703917421 10398898631228105513969033)
      ·
        refine ⟨7799173973421079135476775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10398898631228105513969033 7799173973421079135476775)
        ·
          refine ⟨11698760960131618703215163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799173973421079135476775 11698760960131618703215163)
          ·
            refine ⟨17548141440197428054822745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11698760960131618703215163 17548141440197428054822745)
            ·
              refine ⟨13161106080148071041117059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17548141440197428054822745 13161106080148071041117059)
              ·
                refine ⟨19741659120222106561675589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13161106080148071041117059 19741659120222106561675589)
                ·
                  refine ⟨3701561085041644980314173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19741659120222106561675589 3701561085041644980314173)
                  ·
                    refine ⟨1388085406890616867617815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701561085041644980314173 1388085406890616867617815)
                    ·
                      rfl

theorem cell22_4054930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4054930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054930 prefixEnd_4054930 := by exact prefixLift 4054930
  have htrace : WordTrace (prefixWord ++ tailWord_4054930) baseStart_4054930 baseEnd_4054930 := by
    simpa [prefixWord, tailWord_4054930, baseEnd_4054930] using wordTrace_append hprefix tailTrace_4054930
  have hstable : (prefixWord ++ tailWord_4054930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054930).length < 2 ^ (prefixWord ++ tailWord_4054930).sum := by decide
  have hdescent : baseEnd_4054930 < baseStart_4054930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054932 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_4054932 : Nat := 118140960795 + 4054932 * 2 ^ 59
def prefixEnd_4054932 : Nat := 4983230072969 + 3 ^ 40 * 4054932 * 2
def baseEnd_4054932 : Nat := 462695363843829843022603

theorem tailTrace_4054932 : CollatzResearch.WordTrace tailWord_4054932 prefixEnd_4054932 462695363843829843022603 := by
  unfold tailWord_4054932
  simp only [CollatzResearch.WordTrace]
  refine ⟨73947760072840683047899525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98597013430454244063866033 73947760072840683047899525)
  ·
    refine ⟨13865205013657628071481161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73947760072840683047899525 13865205013657628071481161)
    ·
      refine ⟨10398903760243221053610871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13865205013657628071481161 10398903760243221053610871)
      ·
        refine ⟨15598355640364831580416307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10398903760243221053610871 15598355640364831580416307)
        ·
          refine ⟨23397533460547247370624461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15598355640364831580416307 23397533460547247370624461)
          ·
            refine ⟨8774075047705217763984173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23397533460547247370624461 8774075047705217763984173)
            ·
              refine ⟨3290278142889456661494065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8774075047705217763984173 3290278142889456661494065)
              ·
                refine ⟨2467708607167092496120549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290278142889456661494065 2467708607167092496120549)
                ·
                  refine ⟨462695363843829843022603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2467708607167092496120549 462695363843829843022603)
                  ·
                    rfl

theorem cell22_4054932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_4054932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054932 prefixEnd_4054932 := by exact prefixLift 4054932
  have htrace : WordTrace (prefixWord ++ tailWord_4054932) baseStart_4054932 baseEnd_4054932 := by
    simpa [prefixWord, tailWord_4054932, baseEnd_4054932] using wordTrace_append hprefix tailTrace_4054932
  have hstable : (prefixWord ++ tailWord_4054932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054932).length < 2 ^ (prefixWord ++ tailWord_4054932).sum := by decide
  have hdescent : baseEnd_4054932 < baseStart_4054932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054943 : List Nat := [1, 1, 2, 5, 3, 1, 2, 7]
def baseStart_4054943 : Nat := 118140960795 + 4054943 * 2 ^ 59
def prefixEnd_4054943 : Nat := 4983230072969 + 3 ^ 40 * 4054943 * 2
def baseEnd_4054943 : Nat := 154232206339587685226975

theorem tailTrace_4054943 : CollatzResearch.WordTrace tailWord_4054943 prefixEnd_4054943 154232206339587685226975 := by
  unfold tailWord_4054943
  simp only [CollatzResearch.WordTrace]
  refine ⟨147895921348641514974449483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98597280899094343316299655 147895921348641514974449483)
  ·
    refine ⟨221843882022962272461674225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147895921348641514974449483 221843882022962272461674225)
    ·
      refine ⟨166382911517221704346255669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221843882022962272461674225 166382911517221704346255669)
      ·
        refine ⟨15598397954739534782461469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166382911517221704346255669 15598397954739534782461469)
        ·
          refine ⟨5849399233027325543423051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15598397954739534782461469 5849399233027325543423051)
          ·
            refine ⟨8774098849540988315134577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849399233027325543423051 8774098849540988315134577)
            ·
              refine ⟨6580574137155741236350933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8774098849540988315134577 6580574137155741236350933)
              ·
                refine ⟨154232206339587685226975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6580574137155741236350933 154232206339587685226975)
                ·
                  rfl

theorem cell22_4054943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 7].length) (baseStart_4054943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054943 prefixEnd_4054943 := by exact prefixLift 4054943
  have htrace : WordTrace (prefixWord ++ tailWord_4054943) baseStart_4054943 baseEnd_4054943 := by
    simpa [prefixWord, tailWord_4054943, baseEnd_4054943] using wordTrace_append hprefix tailTrace_4054943
  have hstable : (prefixWord ++ tailWord_4054943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054943).length < 2 ^ (prefixWord ++ tailWord_4054943).sum := by decide
  have hdescent : baseEnd_4054943 < baseStart_4054943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054975 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 1, 3]
def baseStart_4054975 : Nat := 118140960795 + 4054975 * 2 ^ 59
def prefixEnd_4054975 : Nat := 4983230072969 + 3 ^ 40 * 4054975 * 2
def baseEnd_4054975 : Nat := 1388100811310251750242677

theorem tailTrace_4054975 : CollatzResearch.WordTrace tailWord_4054975 prefixEnd_4054975 1388100811310251750242677 := by
  unfold tailWord_4054975
  simp only [CollatzResearch.WordTrace]
  refine ⟨147897088484525584439614379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98598058989683722959742919 147897088484525584439614379)
  ·
    refine ⟨221845632726788376659421569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147897088484525584439614379 221845632726788376659421569)
    ·
      refine ⟨166384224545091282494566177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221845632726788376659421569 166384224545091282494566177)
      ·
        refine ⟨124788168408818461870924633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166384224545091282494566177 124788168408818461870924633)
        ·
          refine ⟨93591126306613846403193475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124788168408818461870924633 93591126306613846403193475)
          ·
            refine ⟨140386689459920769604790213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93591126306613846403193475 140386689459920769604790213)
            ·
              refine ⟨26322504273735144300898165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140386689459920769604790213 26322504273735144300898165)
              ·
                refine ⟨2467734775662669778209203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26322504273735144300898165 2467734775662669778209203)
                ·
                  refine ⟨3701602163494004667313805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467734775662669778209203 3701602163494004667313805)
                  ·
                    refine ⟨1388100811310251750242677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701602163494004667313805 1388100811310251750242677)
                    ·
                      rfl

theorem cell22_4054975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 1, 3].length) (baseStart_4054975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054975 prefixEnd_4054975 := by exact prefixLift 4054975
  have htrace : WordTrace (prefixWord ++ tailWord_4054975) baseStart_4054975 baseEnd_4054975 := by
    simpa [prefixWord, tailWord_4054975, baseEnd_4054975] using wordTrace_append hprefix tailTrace_4054975
  have hstable : (prefixWord ++ tailWord_4054975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054975).length < 2 ^ (prefixWord ++ tailWord_4054975).sum := by decide
  have hdescent : baseEnd_4054975 < baseStart_4054975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054988 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_4054988 : Nat := 118140960795 + 4054988 * 2 ^ 59
def prefixEnd_4054988 : Nat := 4983230072969 + 3 ^ 40 * 4054988 * 2
def baseEnd_4054988 : Nat := 462701753825308016555879

theorem tailTrace_4054988 : CollatzResearch.WordTrace tailWord_4054988 prefixEnd_4054988 462701753825308016555879 := by
  unfold tailWord_4054988
  simp only [CollatzResearch.WordTrace]
  refine ⟨73948781316739243829918809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98598375088985658439891745 73948781316739243829918809)
  ·
    refine ⟨55461585987554432872439107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73948781316739243829918809 55461585987554432872439107)
    ·
      refine ⟨83192378981331649308658661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55461585987554432872439107 83192378981331649308658661)
      ·
        refine ⟨15598571058999684245373499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83192378981331649308658661 15598571058999684245373499)
        ·
          refine ⟨23397856588499526368060249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15598571058999684245373499 23397856588499526368060249)
          ·
            refine ⟨17548392441374644776045187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23397856588499526368060249 17548392441374644776045187)
            ·
              refine ⟨26322588662061967164067781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17548392441374644776045187 26322588662061967164067781)
              ·
                refine ⟨4935485374136618843262709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26322588662061967164067781 4935485374136618843262709)
                ·
                  refine ⟨462701753825308016555879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935485374136618843262709 462701753825308016555879)
                  ·
                    rfl

theorem cell22_4054988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_4054988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054988 prefixEnd_4054988 := by exact prefixLift 4054988
  have htrace : WordTrace (prefixWord ++ tailWord_4054988) baseStart_4054988 baseEnd_4054988 := by
    simpa [prefixWord, tailWord_4054988, baseEnd_4054988] using wordTrace_append hprefix tailTrace_4054988
  have hstable : (prefixWord ++ tailWord_4054988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054988).length < 2 ^ (prefixWord ++ tailWord_4054988).sum := by decide
  have hdescent : baseEnd_4054988 < baseStart_4054988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4054992 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 1, 3]
def baseStart_4054992 : Nat := 118140960795 + 4054992 * 2 ^ 59
def prefixEnd_4054992 : Nat := 4983230072969 + 3 ^ 40 * 4054992 * 2
def baseEnd_4054992 : Nat := 1388106630757669372567625

theorem tailTrace_4054992 : CollatzResearch.WordTrace tailWord_4054992 prefixEnd_4054992 1388106630757669372567625 := by
  unfold tailWord_4054992
  simp only [CollatzResearch.WordTrace]
  refine ⟨73948854262731998171491615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98598472350309330895322153 73948854262731998171491615)
  ·
    refine ⟨110923281394097997257237423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73948854262731998171491615 110923281394097997257237423)
    ·
      refine ⟨166384922091146995885856135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110923281394097997257237423 166384922091146995885856135)
      ·
        refine ⟨249577383136720493828784203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166384922091146995885856135 249577383136720493828784203)
        ·
          refine ⟨374366074705080740743176305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249577383136720493828784203 374366074705080740743176305)
          ·
            refine ⟨280774556028810555557382229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374366074705080740743176305 280774556028810555557382229)
            ·
              refine ⟨3290326828462623697938073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 280774556028810555557382229 3290326828462623697938073)
              ·
                refine ⟨2467745121346967773453555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290326828462623697938073 2467745121346967773453555)
                ·
                  refine ⟨3701617682020451660180333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467745121346967773453555 3701617682020451660180333)
                  ·
                    refine ⟨1388106630757669372567625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701617682020451660180333 1388106630757669372567625)
                    ·
                      rfl

theorem cell22_4054992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_4054992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4054992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4054992 prefixEnd_4054992 := by exact prefixLift 4054992
  have htrace : WordTrace (prefixWord ++ tailWord_4054992) baseStart_4054992 baseEnd_4054992 := by
    simpa [prefixWord, tailWord_4054992, baseEnd_4054992] using wordTrace_append hprefix tailTrace_4054992
  have hstable : (prefixWord ++ tailWord_4054992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4054992).length < 2 ^ (prefixWord ++ tailWord_4054992).sum := by decide
  have hdescent : baseEnd_4054992 < baseStart_4054992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4054992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055018 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4055018 : Nat := 118140960795 + 4055018 * 2 ^ 59
def prefixEnd_4055018 : Nat := 4983230072969 + 3 ^ 40 * 4055018 * 2
def baseEnd_4055018 : Nat := 1388115531089013971417545

theorem tailTrace_4055018 : CollatzResearch.WordTrace tailWord_4055018 prefixEnd_4055018 1388115531089013971417545 := by
  unfold tailWord_4055018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974664205842450695857427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98599104548913201855619805 36974664205842450695857427)
  ·
    refine ⟨55461996308763676043786141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36974664205842450695857427 55461996308763676043786141)
    ·
      refine ⟨20798248615786378516419803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55461996308763676043786141 20798248615786378516419803)
      ·
        refine ⟨31197372923679567774629705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20798248615786378516419803 31197372923679567774629705)
        ·
          refine ⟨23398029692759675830972279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31197372923679567774629705 23398029692759675830972279)
          ·
            refine ⟨35097044539139513746458419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23398029692759675830972279 35097044539139513746458419)
            ·
              refine ⟨52645566808709270619687629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35097044539139513746458419 52645566808709270619687629)
              ·
                refine ⟨19742087553265976482382861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52645566808709270619687629 19742087553265976482382861)
                ·
                  refine ⟨7403282832474741180893573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19742087553265976482382861 7403282832474741180893573)
                  ·
                    refine ⟨1388115531089013971417545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403282832474741180893573 1388115531089013971417545)
                    ·
                      rfl

theorem cell22_4055018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4055018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055018 prefixEnd_4055018 := by exact prefixLift 4055018
  have htrace : WordTrace (prefixWord ++ tailWord_4055018) baseStart_4055018 baseEnd_4055018 := by
    simpa [prefixWord, tailWord_4055018, baseEnd_4055018] using wordTrace_append hprefix tailTrace_4055018
  have hstable : (prefixWord ++ tailWord_4055018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055018).length < 2 ^ (prefixWord ++ tailWord_4055018).sum := by decide
  have hdescent : baseEnd_4055018 < baseStart_4055018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055035 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 1, 4]
def baseStart_4055035 : Nat := 118140960795 + 4055035 * 2 ^ 59
def prefixEnd_4055035 : Nat := 4983230072969 + 3 ^ 40 * 4055035 * 2
def baseEnd_4055035 : Nat := 1388121350536431593742493

theorem tailTrace_4055035 : CollatzResearch.WordTrace tailWord_4055035 prefixEnd_4055035 1388121350536431593742493 := by
  unfold tailWord_4055035
  simp only [CollatzResearch.WordTrace]
  refine ⟨147899276864308214686798559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98599517909538809791199039 147899276864308214686798559)
  ·
    refine ⟨221848915296462322030197839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147899276864308214686798559 221848915296462322030197839)
    ·
      refine ⟨332773372944693483045296759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221848915296462322030197839 332773372944693483045296759)
      ·
        refine ⟨499160059417040224567945139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332773372944693483045296759 499160059417040224567945139)
        ·
          refine ⟨748740089125560336851917709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499160059417040224567945139 748740089125560336851917709)
          ·
            refine ⟨280777533422085126319469141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748740089125560336851917709 280777533422085126319469141)
            ·
              refine ⟨3290361719790060074056279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 280777533422085126319469141 3290361719790060074056279)
              ·
                refine ⟨4935542579685090111084419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290361719790060074056279 4935542579685090111084419)
                ·
                  refine ⟨7403313869527635166626629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935542579685090111084419 7403313869527635166626629)
                  ·
                    refine ⟨1388121350536431593742493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403313869527635166626629 1388121350536431593742493)
                    ·
                      rfl

theorem cell22_4055035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 1, 4].length) (baseStart_4055035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055035 prefixEnd_4055035 := by exact prefixLift 4055035
  have htrace : WordTrace (prefixWord ++ tailWord_4055035) baseStart_4055035 baseEnd_4055035 := by
    simpa [prefixWord, tailWord_4055035, baseEnd_4055035] using wordTrace_append hprefix tailTrace_4055035
  have hstable : (prefixWord ++ tailWord_4055035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055035).length < 2 ^ (prefixWord ++ tailWord_4055035).sum := by decide
  have hdescent : baseEnd_4055035 < baseStart_4055035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055050 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_4055050 : Nat := 118140960795 + 4055050 * 2 ^ 59
def prefixEnd_4055050 : Nat := 4983230072969 + 3 ^ 40 * 4055050 * 2
def baseEnd_4055050 : Nat := 462708828447658851539149

theorem tailTrace_4055050 : CollatzResearch.WordTrace tailWord_4055050 prefixEnd_4055050 462708828447658851539149 := by
  unfold tailWord_4055050
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974955989813468062148651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98599882639502581499063069 36974955989813468062148651)
  ·
    refine ⟨55462433984720202093222977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36974955989813468062148651 55462433984720202093222977)
    ·
      refine ⟨41596825488540151569917233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55462433984720202093222977 41596825488540151569917233)
      ·
        refine ⟨31197619116405113677437925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41596825488540151569917233 31197619116405113677437925)
        ·
          refine ⟨5849553584325958814519611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31197619116405113677437925 5849553584325958814519611)
          ·
            refine ⟨8774330376488938221779417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849553584325958814519611 8774330376488938221779417)
            ·
              refine ⟨6580747782366703666334563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8774330376488938221779417 6580747782366703666334563)
              ·
                refine ⟨9871121673550055499501845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580747782366703666334563 9871121673550055499501845)
                ·
                  refine ⟨462708828447658851539149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9871121673550055499501845 462708828447658851539149)
                  ·
                    rfl

theorem cell22_4055050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_4055050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055050 prefixEnd_4055050 := by exact prefixLift 4055050
  have htrace : WordTrace (prefixWord ++ tailWord_4055050) baseStart_4055050 baseEnd_4055050 := by
    simpa [prefixWord, tailWord_4055050, baseEnd_4055050] using wordTrace_append hprefix tailTrace_4055050
  have hstable : (prefixWord ++ tailWord_4055050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055050).length < 2 ^ (prefixWord ++ tailWord_4055050).sum := by decide
  have hdescent : baseEnd_4055050 < baseStart_4055050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055161 : List Nat := [1, 2, 1, 3, 4, 3, 2, 2, 1, 3]
def baseStart_4055161 : Nat := 118140960795 + 4055161 * 2 ^ 59
def prefixEnd_4055161 : Nat := 4983230072969 + 3 ^ 40 * 4055161 * 2
def baseEnd_4055161 : Nat := 1388164482911409265092107

theorem tailTrace_4055161 : CollatzResearch.WordTrace tailWord_4055161 prefixEnd_4055161 1388164482911409265092107 := by
  unfold tailWord_4055161
  simp only [CollatzResearch.WordTrace]
  refine ⟨147903872461851738205885337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98602581641234492137256891 147903872461851738205885337)
  ·
    refine ⟨110927904346388803654414003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147903872461851738205885337 110927904346388803654414003)
    ·
      refine ⟨166391856519583205481621005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110927904346388803654414003 166391856519583205481621005)
      ·
        refine ⟨62396946194843702055607877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166391856519583205481621005 62396946194843702055607877)
        ·
          refine ⟨11699427411533194135426477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62396946194843702055607877 11699427411533194135426477)
          ·
            refine ⟨4387285279324947800784929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11699427411533194135426477 4387285279324947800784929)
            ·
              refine ⟨3290463959493710850588697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4387285279324947800784929 3290463959493710850588697)
              ·
                refine ⟨2467847969620283137941523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3290463959493710850588697 2467847969620283137941523)
                ·
                  refine ⟨3701771954430424706912285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467847969620283137941523 3701771954430424706912285)
                  ·
                    refine ⟨1388164482911409265092107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701771954430424706912285 1388164482911409265092107)
                    ·
                      rfl

theorem cell22_4055161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_4055161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055161 prefixEnd_4055161 := by exact prefixLift 4055161
  have htrace : WordTrace (prefixWord ++ tailWord_4055161) baseStart_4055161 baseEnd_4055161 := by
    simpa [prefixWord, tailWord_4055161, baseEnd_4055161] using wordTrace_append hprefix tailTrace_4055161
  have hstable : (prefixWord ++ tailWord_4055161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055161).length < 2 ^ (prefixWord ++ tailWord_4055161).sum := by decide
  have hdescent : baseEnd_4055161 < baseStart_4055161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055168 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_4055168 : Nat := 118140960795 + 4055168 * 2 ^ 59
def prefixEnd_4055168 : Nat := 4983230072969 + 3 ^ 40 * 4055168 * 2
def baseEnd_4055168 : Nat := 462722293051487860055695

theorem tailTrace_4055168 : CollatzResearch.WordTrace tailWord_4055168 prefixEnd_4055168 462722293051487860055695 := by
  unfold tailWord_4055168
  simp only [CollatzResearch.WordTrace]
  refine ⟨73952063886413189200695079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98602751848550918934260105 73952063886413189200695079)
  ·
    refine ⟨110928095829619783801042619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73952063886413189200695079 110928095829619783801042619)
    ·
      refine ⟨166392143744429675701563929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110928095829619783801042619 166392143744429675701563929)
      ·
        refine ⟨124794107808322256776172947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166392143744429675701563929 124794107808322256776172947)
        ·
          refine ⟨187191161712483385164259421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124794107808322256776172947 187191161712483385164259421)
          ·
            refine ⟨70196685642181269436597283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187191161712483385164259421 70196685642181269436597283)
            ·
              refine ⟨105295028463271904154895925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70196685642181269436597283 105295028463271904154895925)
              ·
                refine ⟨9871408918431741014521493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105295028463271904154895925 9871408918431741014521493)
                ·
                  refine ⟨462722293051487860055695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9871408918431741014521493 462722293051487860055695)
                  ·
                    rfl

theorem cell22_4055168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_4055168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055168 prefixEnd_4055168 := by exact prefixLift 4055168
  have htrace : WordTrace (prefixWord ++ tailWord_4055168) baseStart_4055168 baseEnd_4055168 := by
    simpa [prefixWord, tailWord_4055168, baseEnd_4055168] using wordTrace_append hprefix tailTrace_4055168
  have hstable : (prefixWord ++ tailWord_4055168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055168).length < 2 ^ (prefixWord ++ tailWord_4055168).sum := by decide
  have hdescent : baseEnd_4055168 < baseStart_4055168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055200 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_4055200 : Nat := 118140960795 + 4055200 * 2 ^ 59
def prefixEnd_4055200 : Nat := 4983230072969 + 3 ^ 40 * 4055200 * 2
def baseEnd_4055200 : Nat := 1388177833408426163366987

theorem tailTrace_4055200 : CollatzResearch.WordTrace tailWord_4055200 prefixEnd_4055200 1388177833408426163366987 := by
  unfold tailWord_4055200
  simp only [CollatzResearch.WordTrace]
  refine ⟨73952647454355223933277527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98603529939140298577703369 73952647454355223933277527)
  ·
    refine ⟨110928971181532835899916291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73952647454355223933277527 110928971181532835899916291)
    ·
      refine ⟨166393456772299253849874437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110928971181532835899916291 166393456772299253849874437)
      ·
        refine ⟨31198773144806110096851457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166393456772299253849874437 31198773144806110096851457)
        ·
          refine ⟨23399079858604582572638593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31198773144806110096851457 23399079858604582572638593)
          ·
            refine ⟨17549309893953436929478945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23399079858604582572638593 17549309893953436929478945)
            ·
              refine ⟨13161982420465077697109209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17549309893953436929478945 13161982420465077697109209)
              ·
                refine ⟨9871486815348808272831907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13161982420465077697109209 9871486815348808272831907)
                ·
                  refine ⟨14807230223023212409247861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9871486815348808272831907 14807230223023212409247861)
                  ·
                    refine ⟨1388177833408426163366987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14807230223023212409247861 1388177833408426163366987)
                    ·
                      rfl

theorem cell22_4055200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_4055200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055200 prefixEnd_4055200 := by exact prefixLift 4055200
  have htrace : WordTrace (prefixWord ++ tailWord_4055200) baseStart_4055200 baseEnd_4055200 := by
    simpa [prefixWord, tailWord_4055200, baseEnd_4055200] using wordTrace_append hprefix tailTrace_4055200
  have hstable : (prefixWord ++ tailWord_4055200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055200).length < 2 ^ (prefixWord ++ tailWord_4055200).sum := by decide
  have hdescent : baseEnd_4055200 < baseStart_4055200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055275 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 5]
def baseStart_4055275 : Nat := 118140960795 + 4055275 * 2 ^ 59
def prefixEnd_4055275 : Nat := 4983230072969 + 3 ^ 40 * 4055275 * 2
def baseEnd_4055275 : Nat := 462734502480383655913919

theorem tailTrace_4055275 : CollatzResearch.WordTrace tailWord_4055275 prefixEnd_4055275 462734502480383655913919 := by
  unfold tailWord_4055275
  simp only [CollatzResearch.WordTrace]
  refine ⟨147908030383438735675535279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98605353588959157117023519 147908030383438735675535279)
  ·
    refine ⟨221862045575158103513302919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147908030383438735675535279 221862045575158103513302919)
    ·
      refine ⟨332793068362737155269954379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221862045575158103513302919 332793068362737155269954379)
      ·
        refine ⟨499189602544105732904931569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332793068362737155269954379 499189602544105732904931569)
        ·
          refine ⟨374392201908079299678698677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499189602544105732904931569 374392201908079299678698677)
          ·
            refine ⟨35099268928882434344878001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 374392201908079299678698677 35099268928882434344878001)
            ·
              refine ⟨26324451696661825758658501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35099268928882434344878001 26324451696661825758658501)
              ·
                refine ⟨4935834693124092329748469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26324451696661825758658501 4935834693124092329748469)
                ·
                  refine ⟨462734502480383655913919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935834693124092329748469 462734502480383655913919)
                  ·
                    rfl

theorem cell22_4055275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 5].length) (baseStart_4055275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055275 prefixEnd_4055275 := by exact prefixLift 4055275
  have htrace : WordTrace (prefixWord ++ tailWord_4055275) baseStart_4055275 baseEnd_4055275 := by
    simpa [prefixWord, tailWord_4055275, baseEnd_4055275] using wordTrace_append hprefix tailTrace_4055275
  have hstable : (prefixWord ++ tailWord_4055275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055275).length < 2 ^ (prefixWord ++ tailWord_4055275).sum := by decide
  have hdescent : baseEnd_4055275 < baseStart_4055275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055279 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 3, 3]
def baseStart_4055279 : Nat := 118140960795 + 4055279 * 2 ^ 59
def prefixEnd_4055279 : Nat := 4983230072969 + 3 ^ 40 * 4055279 * 2
def baseEnd_4055279 : Nat := 1388204876722896290641745

theorem tailTrace_4055279 : CollatzResearch.WordTrace tailWord_4055279 prefixEnd_4055279 1388204876722896290641745 := by
  unfold tailWord_4055279
  simp only [CollatzResearch.WordTrace]
  refine ⟨147908176275424244358680891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98605450850282829572453927 147908176275424244358680891)
  ·
    refine ⟨221862264413136366538021337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147908176275424244358680891 221862264413136366538021337)
    ·
      refine ⟨166396698309852274903516003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221862264413136366538021337 166396698309852274903516003)
      ·
        refine ⟨249595047464778412355274005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166396698309852274903516003 249595047464778412355274005)
        ·
          refine ⟨11699767849911488079153469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249595047464778412355274005 11699767849911488079153469)
          ·
            refine ⟨4387412943716808029682551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11699767849911488079153469 4387412943716808029682551)
            ·
              refine ⟨6581119415575212044523827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4387412943716808029682551 6581119415575212044523827)
              ·
                refine ⟨9871679123362818066785741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6581119415575212044523827 9871679123362818066785741)
                ·
                  refine ⟨3701879671261056775044653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9871679123362818066785741 3701879671261056775044653)
                  ·
                    refine ⟨1388204876722896290641745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701879671261056775044653 1388204876722896290641745)
                    ·
                      rfl

theorem cell22_4055279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_4055279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055279 prefixEnd_4055279 := by exact prefixLift 4055279
  have htrace : WordTrace (prefixWord ++ tailWord_4055279) baseStart_4055279 baseEnd_4055279 := by
    simpa [prefixWord, tailWord_4055279, baseEnd_4055279] using wordTrace_append hprefix tailTrace_4055279
  have hstable : (prefixWord ++ tailWord_4055279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055279).length < 2 ^ (prefixWord ++ tailWord_4055279).sum := by decide
  have hdescent : baseEnd_4055279 < baseStart_4055279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055292 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_4055292 : Nat := 118140960795 + 4055292 * 2 ^ 59
def prefixEnd_4055292 : Nat := 4983230072969 + 3 ^ 40 * 4055292 * 2
def baseEnd_4055292 : Nat := 462736442296189530022235

theorem tailTrace_4055292 : CollatzResearch.WordTrace tailWord_4055292 prefixEnd_4055292 462736442296189530022235 := by
  unfold tailWord_4055292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73954325212188573789452065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98605766949584765052602753 73954325212188573789452065)
  ·
    refine ⟨55465743909141430342089049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73954325212188573789452065 55465743909141430342089049)
    ·
      refine ⟨41599307931856072756566787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55465743909141430342089049 41599307931856072756566787)
      ·
        refine ⟨62398961897784109134850181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41599307931856072756566787 62398961897784109134850181)
        ·
          refine ⟨11699805355834520462784409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62398961897784109134850181 11699805355834520462784409)
          ·
            refine ⟨8774854016875890347088307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11699805355834520462784409 8774854016875890347088307)
            ·
              refine ⟨13162281025313835520632461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774854016875890347088307 13162281025313835520632461)
              ·
                refine ⟨4935855384492688320237173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13162281025313835520632461 4935855384492688320237173)
                ·
                  refine ⟨462736442296189530022235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935855384492688320237173 462736442296189530022235)
                  ·
                    rfl

theorem cell22_4055292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_4055292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055292 prefixEnd_4055292 := by exact prefixLift 4055292
  have htrace : WordTrace (prefixWord ++ tailWord_4055292) baseStart_4055292 baseEnd_4055292 := by
    simpa [prefixWord, tailWord_4055292, baseEnd_4055292] using wordTrace_append hprefix tailTrace_4055292
  have hstable : (prefixWord ++ tailWord_4055292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055292).length < 2 ^ (prefixWord ++ tailWord_4055292).sum := by decide
  have hdescent : baseEnd_4055292 < baseStart_4055292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055326 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4055326 : Nat := 118140960795 + 4055326 * 2 ^ 59
def prefixEnd_4055326 : Nat := 4983230072969 + 3 ^ 40 * 4055326 * 2
def baseEnd_4055326 : Nat := 462740321927801278238867

theorem tailTrace_4055326 : CollatzResearch.WordTrace tailWord_4055326 prefixEnd_4055326 462740321927801278238867 := by
  unfold tailWord_4055326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18488736313281746423205229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98606593670835980923761221 18488736313281746423205229)
  ·
    refine ⟨6933276117480654908701961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18488736313281746423205229 6933276117480654908701961)
    ·
      refine ⟨5199957088110491181526471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6933276117480654908701961 5199957088110491181526471)
      ·
        refine ⟨7799935632165736772289707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199957088110491181526471 7799935632165736772289707)
        ·
          refine ⟨11699903448248605158434561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799935632165736772289707 11699903448248605158434561)
          ·
            refine ⟨8774927586186453868825921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11699903448248605158434561 8774927586186453868825921)
            ·
              refine ⟨6581195689639840401619441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8774927586186453868825921 6581195689639840401619441)
              ·
                refine ⟨4935896767229880301214581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581195689639840401619441 4935896767229880301214581)
                ·
                  refine ⟨462740321927801278238867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4935896767229880301214581 462740321927801278238867)
                  ·
                    rfl

theorem cell22_4055326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4055326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055326 prefixEnd_4055326 := by exact prefixLift 4055326
  have htrace : WordTrace (prefixWord ++ tailWord_4055326) baseStart_4055326 baseEnd_4055326 := by
    simpa [prefixWord, tailWord_4055326, baseEnd_4055326] using wordTrace_append hprefix tailTrace_4055326
  have hstable : (prefixWord ++ tailWord_4055326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055326).length < 2 ^ (prefixWord ++ tailWord_4055326).sum := by decide
  have hdescent : baseEnd_4055326 < baseStart_4055326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055502 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_4055502 : Nat := 118140960795 + 4055502 * 2 ^ 59
def prefixEnd_4055502 : Nat := 4983230072969 + 3 ^ 40 * 4055502 * 2
def baseEnd_4055502 : Nat := 1388281214180198042316061

theorem tailTrace_4055502 : CollatzResearch.WordTrace tailWord_4055502 prefixEnd_4055502 1388281214180198042316061 := by
  unfold tailWord_4055502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489538719202044180506095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98610873169077568962699173 18489538719202044180506095)
  ·
    refine ⟨27734308078803066270759143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18489538719202044180506095 27734308078803066270759143)
    ·
      refine ⟨41601462118204599406138715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27734308078803066270759143 41601462118204599406138715)
      ·
        refine ⟨62402193177306899109208073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41601462118204599406138715 62402193177306899109208073)
        ·
          refine ⟨46801644882980174331906055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62402193177306899109208073 46801644882980174331906055)
          ·
            refine ⟨70202467324470261497859083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46801644882980174331906055 70202467324470261497859083)
            ·
              refine ⟨105303700986705392246788625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70202467324470261497859083 105303700986705392246788625)
              ·
                refine ⟨78977775740029044185091469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105303700986705392246788625 78977775740029044185091469)
                ·
                  refine ⟨29616665902510891569409301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78977775740029044185091469 29616665902510891569409301)
                  ·
                    refine ⟨1388281214180198042316061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29616665902510891569409301 1388281214180198042316061)
                    ·
                      rfl

theorem cell22_4055502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_4055502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055502 prefixEnd_4055502 := by exact prefixLift 4055502
  have htrace : WordTrace (prefixWord ++ tailWord_4055502) baseStart_4055502 baseEnd_4055502 := by
    simpa [prefixWord, tailWord_4055502, baseEnd_4055502] using wordTrace_append hprefix tailTrace_4055502
  have hstable : (prefixWord ++ tailWord_4055502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055502).length < 2 ^ (prefixWord ++ tailWord_4055502).sum := by decide
  have hdescent : baseEnd_4055502 < baseStart_4055502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055549 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_4055549 : Nat := 118140960795 + 4055549 * 2 ^ 59
def prefixEnd_4055549 : Nat := 4983230072969 + 3 ^ 40 * 4055549 * 2
def baseEnd_4055549 : Nat := 1388297303240705586390917

theorem tailTrace_4055549 : CollatzResearch.WordTrace tailWord_4055549 prefixEnd_4055549 1388297303240705586390917 := by
  unfold tailWord_4055549
  simp only [CollatzResearch.WordTrace]
  refine ⟨147918023984446080471009701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98612015989630720314006467 147918023984446080471009701)
  ·
    refine ⟨27734629497083640088314319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147918023984446080471009701 27734629497083640088314319)
    ·
      refine ⟨41601944245625460132471479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27734629497083640088314319 41601944245625460132471479)
      ·
        refine ⟨62402916368438190198707219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41601944245625460132471479 62402916368438190198707219)
        ·
          refine ⟨93604374552657285298060829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62402916368438190198707219 93604374552657285298060829)
          ·
            refine ⟨35101640457246481986772811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93604374552657285298060829 35101640457246481986772811)
            ·
              refine ⟨52652460685869722980159217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35101640457246481986772811 52652460685869722980159217)
              ·
                refine ⟨39489345514402292235119413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52652460685869722980159217 39489345514402292235119413)
                ·
                  refine ⟨3702126141975214897042445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39489345514402292235119413 3702126141975214897042445)
                  ·
                    refine ⟨1388297303240705586390917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702126141975214897042445 1388297303240705586390917)
                    ·
                      rfl

theorem cell22_4055549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_4055549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055549 prefixEnd_4055549 := by exact prefixLift 4055549
  have htrace : WordTrace (prefixWord ++ tailWord_4055549) baseStart_4055549 baseEnd_4055549 := by
    simpa [prefixWord, tailWord_4055549, baseEnd_4055549] using wordTrace_append hprefix tailTrace_4055549
  have hstable : (prefixWord ++ tailWord_4055549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055549).length < 2 ^ (prefixWord ++ tailWord_4055549).sum := by decide
  have hdescent : baseEnd_4055549 < baseStart_4055549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055566 : List Nat := [4, 1, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_4055566 : Nat := 118140960795 + 4055566 * 2 ^ 59
def prefixEnd_4055566 : Nat := 4983230072969 + 3 ^ 40 * 4055566 * 2
def baseEnd_4055566 : Nat := 1388303122688123208715865

theorem tailTrace_4055566 : CollatzResearch.WordTrace tailWord_4055566 prefixEnd_4055566 1388303122688123208715865 := by
  unfold tailWord_4055566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489830503173061546797319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98612429350256328249585701 18489830503173061546797319)
  ·
    refine ⟨27734745754759592320195979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18489830503173061546797319 27734745754759592320195979)
    ·
      refine ⟨41602118632139388480293969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27734745754759592320195979 41602118632139388480293969)
      ·
        refine ⟨31201588974104541360220477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41602118632139388480293969 31201588974104541360220477)
        ·
          refine ⟨11700595865289203010082679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31201588974104541360220477 11700595865289203010082679)
          ·
            refine ⟨17550893797933804515124019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11700595865289203010082679 17550893797933804515124019)
            ·
              refine ⟨26326340696900706772686029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17550893797933804515124019 26326340696900706772686029)
              ·
                refine ⟨9872377761337765039757261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26326340696900706772686029 9872377761337765039757261)
                ·
                  refine ⟨3702141660501661889908973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9872377761337765039757261 3702141660501661889908973)
                  ·
                    refine ⟨1388303122688123208715865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702141660501661889908973 1388303122688123208715865)
                    ·
                      rfl

theorem cell22_4055566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_4055566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055566 prefixEnd_4055566 := by exact prefixLift 4055566
  have htrace : WordTrace (prefixWord ++ tailWord_4055566) baseStart_4055566 baseEnd_4055566 := by
    simpa [prefixWord, tailWord_4055566, baseEnd_4055566] using wordTrace_append hprefix tailTrace_4055566
  have hstable : (prefixWord ++ tailWord_4055566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055566).length < 2 ^ (prefixWord ++ tailWord_4055566).sum := by decide
  have hdescent : baseEnd_4055566 < baseStart_4055566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055639 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_4055639 : Nat := 118140960795 + 4055639 * 2 ^ 59
def prefixEnd_4055639 : Nat := 4983230072969 + 3 ^ 40 * 4055639 * 2
def baseEnd_4055639 : Nat := 1388328112079975351640641

theorem tailTrace_4055639 : CollatzResearch.WordTrace tailWord_4055639 prefixEnd_4055639 1388328112079975351640641 := by
  unfold tailWord_4055639
  simp only [CollatzResearch.WordTrace]
  refine ⟨147921306554120025841785971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98614204369413350561190647 147921306554120025841785971)
  ·
    refine ⟨221881959831180038762678957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147921306554120025841785971 221881959831180038762678957)
    ·
      refine ⟨83205734936692514536004609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221881959831180038762678957 83205734936692514536004609)
      ·
        refine ⟨62404301202519385902003457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83205734936692514536004609 62404301202519385902003457)
        ·
          refine ⟨46803225901889539426502593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62404301202519385902003457 46803225901889539426502593)
          ·
            refine ⟨35102419426417154569876945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46803225901889539426502593 35102419426417154569876945)
            ·
              refine ⟨26326814569812865927407709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35102419426417154569876945 26326814569812865927407709)
              ·
                refine ⟨9872555463679824722777891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26326814569812865927407709 9872555463679824722777891)
                ·
                  refine ⟨14808833195519737084166837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9872555463679824722777891 14808833195519737084166837)
                  ·
                    refine ⟨1388328112079975351640641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14808833195519737084166837 1388328112079975351640641)
                    ·
                      rfl

theorem cell22_4055639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_4055639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055639 prefixEnd_4055639 := by exact prefixLift 4055639
  have htrace : WordTrace (prefixWord ++ tailWord_4055639) baseStart_4055639 baseEnd_4055639 := by
    simpa [prefixWord, tailWord_4055639, baseEnd_4055639] using wordTrace_append hprefix tailTrace_4055639
  have hstable : (prefixWord ++ tailWord_4055639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055639).length < 2 ^ (prefixWord ++ tailWord_4055639).sum := by decide
  have hdescent : baseEnd_4055639 < baseStart_4055639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055669 : List Nat := [1, 3, 4, 2, 12]
def baseStart_4055669 : Nat := 118140960795 + 4055669 * 2 ^ 59
def prefixEnd_4055669 : Nat := 4983230072969 + 3 ^ 40 * 4055669 * 2
def baseEnd_4055669 : Nat := 5713326673634013470743

theorem tailTrace_4055669 : CollatzResearch.WordTrace tailWord_4055669 prefixEnd_4055669 5713326673634013470743 := by
  unfold tailWord_4055669
  simp only [CollatzResearch.WordTrace]
  refine ⟨147922400744011340965378061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98614933829340893976918707 147922400744011340965378061)
  ·
    refine ⟨55470900279004252862016773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147922400744011340965378061 55470900279004252862016773)
    ·
      refine ⟨10400793802313297411628145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55470900279004252862016773 10400793802313297411628145)
      ·
        refine ⟨7800595351734973058721109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10400793802313297411628145 7800595351734973058721109)
        ·
          refine ⟨5713326673634013470743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7800595351734973058721109 5713326673634013470743)
          ·
            rfl

theorem cell22_4055669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 12].length) (baseStart_4055669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055669 prefixEnd_4055669 := by exact prefixLift 4055669
  have htrace : WordTrace (prefixWord ++ tailWord_4055669) baseStart_4055669 baseEnd_4055669 := by
    simpa [prefixWord, tailWord_4055669, baseEnd_4055669] using wordTrace_append hprefix tailTrace_4055669
  have hstable : (prefixWord ++ tailWord_4055669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055669).length < 2 ^ (prefixWord ++ tailWord_4055669).sum := by decide
  have hdescent : baseEnd_4055669 < baseStart_4055669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055673 : List Nat := [1, 2, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_4055673 : Nat := 118140960795 + 4055673 * 2 ^ 59
def prefixEnd_4055673 : Nat := 4983230072969 + 3 ^ 40 * 4055673 * 2
def baseEnd_4055673 : Nat := 1388339750974810596290537

theorem tailTrace_4055673 : CollatzResearch.WordTrace tailWord_4055673 prefixEnd_4055673 1388339750974810596290537 := by
  unfold tailWord_4055673
  simp only [CollatzResearch.WordTrace]
  refine ⟨147922546635996849648523673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98615031090664566432349115 147922546635996849648523673)
  ·
    refine ⟨110941909976997637236392755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147922546635996849648523673 110941909976997637236392755)
    ·
      refine ⟨166412864965496455854589133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110941909976997637236392755 166412864965496455854589133)
      ·
        refine ⟨62404824362061170945470925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166412864965496455854589133 62404824362061170945470925)
        ·
          refine ⟨23401809135772939104551597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62404824362061170945470925 23401809135772939104551597)
          ·
            refine ⟨8775678425914852164206849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23401809135772939104551597 8775678425914852164206849)
            ·
              refine ⟨6581758819436139123155137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8775678425914852164206849 6581758819436139123155137)
              ·
                refine ⟨4936319114577104342366353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581758819436139123155137 4936319114577104342366353)
                ·
                  refine ⟨3702239335932828256774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936319114577104342366353 3702239335932828256774765)
                  ·
                    refine ⟨1388339750974810596290537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702239335932828256774765 1388339750974810596290537)
                    ·
                      rfl

theorem cell22_4055673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_4055673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055673 prefixEnd_4055673 := by exact prefixLift 4055673
  have htrace : WordTrace (prefixWord ++ tailWord_4055673) baseStart_4055673 baseEnd_4055673 := by
    simpa [prefixWord, tailWord_4055673, baseEnd_4055673] using wordTrace_append hprefix tailTrace_4055673
  have hstable : (prefixWord ++ tailWord_4055673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055673).length < 2 ^ (prefixWord ++ tailWord_4055673).sum := by decide
  have hdescent : baseEnd_4055673 < baseStart_4055673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055731 : List Nat := [1, 1, 1, 2, 3, 4, 3, 2, 5]
def baseStart_4055731 : Nat := 118140960795 + 4055731 * 2 ^ 59
def prefixEnd_4055731 : Nat := 4983230072969 + 3 ^ 40 * 4055731 * 2
def baseEnd_4055731 : Nat := 462786535186705926113453

theorem tailTrace_4055731 : CollatzResearch.WordTrace tailWord_4055731 prefixEnd_4055731 462786535186705926113453 := by
  unfold tailWord_4055731
  simp only [CollatzResearch.WordTrace]
  refine ⟨147924662069786725554135047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98616441379857817036090031 147924662069786725554135047)
  ·
    refine ⟨221886993104680088331202571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147924662069786725554135047 221886993104680088331202571)
    ·
      refine ⟨332830489657020132496803857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221886993104680088331202571 332830489657020132496803857)
      ·
        refine ⟨249622867242765099372602893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332830489657020132496803857 249622867242765099372602893)
        ·
          refine ⟨93608575216036912264726085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249622867242765099372602893 93608575216036912264726085)
          ·
            refine ⟨17551607853006921049636141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93608575216036912264726085 17551607853006921049636141)
            ·
              refine ⟨6581852944877595393613553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17551607853006921049636141 6581852944877595393613553)
              ·
                refine ⟨4936389708658196545210165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6581852944877595393613553 4936389708658196545210165)
                ·
                  refine ⟨462786535186705926113453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936389708658196545210165 462786535186705926113453)
                  ·
                    rfl

theorem cell22_4055731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 2, 5].length) (baseStart_4055731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055731 prefixEnd_4055731 := by exact prefixLift 4055731
  have htrace : WordTrace (prefixWord ++ tailWord_4055731) baseStart_4055731 baseEnd_4055731 := by
    simpa [prefixWord, tailWord_4055731, baseEnd_4055731] using wordTrace_append hprefix tailTrace_4055731
  have hstable : (prefixWord ++ tailWord_4055731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055731).length < 2 ^ (prefixWord ++ tailWord_4055731).sum := by decide
  have hdescent : baseEnd_4055731 < baseStart_4055731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055844 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_4055844 : Nat := 118140960795 + 4055844 * 2 ^ 59
def prefixEnd_4055844 : Nat := 4983230072969 + 3 ^ 40 * 4055844 * 2
def baseEnd_4055844 : Nat := 462799429256474383421671

theorem tailTrace_4055844 : CollatzResearch.WordTrace tailWord_4055844 prefixEnd_4055844 462799429256474383421671 := by
  unfold tailWord_4055844
  simp only [CollatzResearch.WordTrace]
  refine ⟨73964391759188672926499293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98619189012251563901999057 73964391759188672926499293)
  ·
    refine ⟨27736646909695752347437235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73964391759188672926499293 27736646909695752347437235)
    ·
      refine ⟨41604970364543628521155853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27736646909695752347437235 41604970364543628521155853)
      ·
        refine ⟨15601863886703860695433445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41604970364543628521155853 15601863886703860695433445)
        ·
          refine ⟨2925349478756973880393771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15601863886703860695433445 2925349478756973880393771)
          ·
            refine ⟨4388024218135460820590657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925349478756973880393771 4388024218135460820590657)
            ·
              refine ⟨3291018163601595615442993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388024218135460820590657 3291018163601595615442993)
              ·
                refine ⟨2468263622701196711582245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291018163601595615442993 2468263622701196711582245)
                ·
                  refine ⟨462799429256474383421671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468263622701196711582245 462799429256474383421671)
                  ·
                    rfl

theorem cell22_4055844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_4055844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055844 prefixEnd_4055844 := by exact prefixLift 4055844
  have htrace : WordTrace (prefixWord ++ tailWord_4055844) baseStart_4055844 baseEnd_4055844 := by
    simpa [prefixWord, tailWord_4055844, baseEnd_4055844] using wordTrace_append hprefix tailTrace_4055844
  have hstable : (prefixWord ++ tailWord_4055844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055844).length < 2 ^ (prefixWord ++ tailWord_4055844).sum := by decide
  have hdescent : baseEnd_4055844 < baseStart_4055844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055900 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_4055900 : Nat := 118140960795 + 4055900 * 2 ^ 59
def prefixEnd_4055900 : Nat := 4983230072969 + 3 ^ 40 * 4055900 * 2
def baseEnd_4055900 : Nat := 462805819237952556954947

theorem tailTrace_4055900 : CollatzResearch.WordTrace tailWord_4055900 prefixEnd_4055900 462805819237952556954947 := by
  unfold tailWord_4055900
  simp only [CollatzResearch.WordTrace]
  refine ⟨73965413003087233708518577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98620550670782978278024769 73965413003087233708518577)
  ·
    refine ⟨55474059752315425281388933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73965413003087233708518577 55474059752315425281388933)
    ·
      refine ⟨10401386203559142240260425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55474059752315425281388933 10401386203559142240260425)
      ·
        refine ⟨7801039652669356680195319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10401386203559142240260425 7801039652669356680195319)
        ·
          refine ⟨11701559479004035020292979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801039652669356680195319 11701559479004035020292979)
          ·
            refine ⟨17552339218506052530439469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11701559479004035020292979 17552339218506052530439469)
            ·
              refine ⟨6582127206939769698914801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17552339218506052530439469 6582127206939769698914801)
              ·
                refine ⟨4936595405204827274186101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582127206939769698914801 4936595405204827274186101)
                ·
                  refine ⟨462805819237952556954947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4936595405204827274186101 462805819237952556954947)
                  ·
                    rfl

theorem cell22_4055900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_4055900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055900 prefixEnd_4055900 := by exact prefixLift 4055900
  have htrace : WordTrace (prefixWord ++ tailWord_4055900) baseStart_4055900 baseEnd_4055900 := by
    simpa [prefixWord, tailWord_4055900, baseEnd_4055900] using wordTrace_append hprefix tailTrace_4055900
  have hstable : (prefixWord ++ tailWord_4055900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055900).length < 2 ^ (prefixWord ++ tailWord_4055900).sum := by decide
  have hdescent : baseEnd_4055900 < baseStart_4055900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055938 : List Nat := [3, 4, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4055938 : Nat := 118140960795 + 4055938 * 2 ^ 59
def prefixEnd_4055938 : Nat := 4983230072969 + 3 ^ 40 * 4055938 * 2
def baseEnd_4055938 : Nat := 1388430465890438238414725

theorem tailTrace_4055938 : CollatzResearch.WordTrace tailWord_4055938 prefixEnd_4055938 1388430465890438238414725 := by
  unfold tailWord_4055938
  simp only [CollatzResearch.WordTrace]
  refine ⟨36983052995009199976730117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98621474653357866604613645 36983052995009199976730117)
  ·
    refine ⟨6934322436564224995636897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36983052995009199976730117 6934322436564224995636897)
    ·
      refine ⟨5200741827423168746727673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6934322436564224995636897 5200741827423168746727673)
      ·
        refine ⟨3900556370567376560045755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5200741827423168746727673 3900556370567376560045755)
        ·
          refine ⟨5850834555851064840068633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900556370567376560045755 5850834555851064840068633)
          ·
            refine ⟨4388125916888298630051475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850834555851064840068633 4388125916888298630051475)
            ·
              refine ⟨6582188875332447945077213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388125916888298630051475 6582188875332447945077213)
              ·
                refine ⟨2468320828249667979403955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6582188875332447945077213 2468320828249667979403955)
                ·
                  refine ⟨3702481242374501969105933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468320828249667979403955 3702481242374501969105933)
                  ·
                    refine ⟨1388430465890438238414725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702481242374501969105933 1388430465890438238414725)
                    ·
                      rfl

theorem cell22_4055938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4055938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055938 prefixEnd_4055938 := by exact prefixLift 4055938
  have htrace : WordTrace (prefixWord ++ tailWord_4055938) baseStart_4055938 baseEnd_4055938 := by
    simpa [prefixWord, tailWord_4055938, baseEnd_4055938] using wordTrace_append hprefix tailTrace_4055938
  have hstable : (prefixWord ++ tailWord_4055938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055938).length < 2 ^ (prefixWord ++ tailWord_4055938).sum := by decide
  have hdescent : baseEnd_4055938 < baseStart_4055938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055945 : List Nat := [1, 2, 1, 1, 5, 2, 3, 3, 4]
def baseStart_4055945 : Nat := 118140960795 + 4055945 * 2 ^ 59
def prefixEnd_4055945 : Nat := 4983230072969 + 3 ^ 40 * 4055945 * 2
def baseEnd_4055945 : Nat := 462810954044497517829901

theorem tailTrace_4055945 : CollatzResearch.WordTrace tailWord_4055945 prefixEnd_4055945 462810954044497517829901 := by
  unfold tailWord_4055945
  simp only [CollatzResearch.WordTrace]
  refine ⟨147932467291011440102425289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98621644860674293401616859 147932467291011440102425289)
  ·
    refine ⟨110949350468258580076818967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147932467291011440102425289 110949350468258580076818967)
    ·
      refine ⟨166424025702387870115228451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110949350468258580076818967 166424025702387870115228451)
      ·
        refine ⟨249636038553581805172842677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166424025702387870115228451 249636038553581805172842677)
        ·
          refine ⟨23403378614398294234954001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249636038553581805172842677 23403378614398294234954001)
          ·
            refine ⟨17552533960798720676215501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23403378614398294234954001 17552533960798720676215501)
            ·
              refine ⟨6582200235299520253580813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17552533960798720676215501 6582200235299520253580813)
              ·
                refine ⟨2468325088237320095092805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6582200235299520253580813 2468325088237320095092805)
                ·
                  refine ⟨462810954044497517829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468325088237320095092805 462810954044497517829901)
                  ·
                    rfl

theorem cell22_4055945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_4055945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055945 prefixEnd_4055945 := by exact prefixLift 4055945
  have htrace : WordTrace (prefixWord ++ tailWord_4055945) baseStart_4055945 baseEnd_4055945 := by
    simpa [prefixWord, tailWord_4055945, baseEnd_4055945] using wordTrace_append hprefix tailTrace_4055945
  have hstable : (prefixWord ++ tailWord_4055945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055945).length < 2 ^ (prefixWord ++ tailWord_4055945).sum := by decide
  have hdescent : baseEnd_4055945 < baseStart_4055945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055962 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_4055962 : Nat := 118140960795 + 4055962 * 2 ^ 59
def prefixEnd_4055962 : Nat := 4983230072969 + 3 ^ 40 * 4055962 * 2
def baseEnd_4055962 : Nat := 462812893860303391938217

theorem tailTrace_4055962 : CollatzResearch.WordTrace tailWord_4055962 prefixEnd_4055962 462812893860303391938217 := by
  unfold tailWord_4055962
  simp only [CollatzResearch.WordTrace]
  refine ⟨36983271832987463001448535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98622058221299901337196093 36983271832987463001448535)
  ·
    refine ⟨55474907749481194502172803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36983271832987463001448535 55474907749481194502172803)
    ·
      refine ⟨83212361624221791753259205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55474907749481194502172803 83212361624221791753259205)
      ·
        refine ⟨15602317804541585953736101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83212361624221791753259205 15602317804541585953736101)
        ·
          refine ⟨2925434588351547366325519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15602317804541585953736101 2925434588351547366325519)
          ·
            refine ⟨4388151882527321049488279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925434588351547366325519 4388151882527321049488279)
            ·
              refine ⟨6582227823790981574232419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388151882527321049488279 6582227823790981574232419)
              ·
                refine ⟨9873341735686472361348629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582227823790981574232419 9873341735686472361348629)
                ·
                  refine ⟨462812893860303391938217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9873341735686472361348629 462812893860303391938217)
                  ·
                    rfl

theorem cell22_4055962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_4055962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055962 prefixEnd_4055962 := by exact prefixLift 4055962
  have htrace : WordTrace (prefixWord ++ tailWord_4055962) baseStart_4055962 baseEnd_4055962 := by
    simpa [prefixWord, tailWord_4055962, baseEnd_4055962] using wordTrace_append hprefix tailTrace_4055962
  have hstable : (prefixWord ++ tailWord_4055962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055962).length < 2 ^ (prefixWord ++ tailWord_4055962).sum := by decide
  have hdescent : baseEnd_4055962 < baseStart_4055962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4055981 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4055981 : Nat := 118140960795 + 4055981 * 2 ^ 59
def prefixEnd_4055981 : Nat := 4983230072969 + 3 ^ 40 * 4055981 * 2
def baseEnd_4055981 : Nat := 1388445185669200459589593

theorem tailTrace_4055981 : CollatzResearch.WordTrace tailWord_4055981 prefixEnd_4055981 1388445185669200459589593 := by
  unfold tailWord_4055981
  simp only [CollatzResearch.WordTrace]
  refine ⟨147933780318881018250735797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98622520212587345500490531 147933780318881018250735797)
  ·
    refine ⟨13868791904895095461006481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147933780318881018250735797 13868791904895095461006481)
    ·
      refine ⟨10401593928671321595754861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13868791904895095461006481 10401593928671321595754861)
      ·
        refine ⟨3900597723251745598408073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10401593928671321595754861 3900597723251745598408073)
        ·
          refine ⟨2925448292438809198806055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3900597723251745598408073 2925448292438809198806055)
          ·
            refine ⟨4388172438658213798209083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925448292438809198806055 4388172438658213798209083)
            ·
              refine ⟨6582258657987320697313625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4388172438658213798209083 6582258657987320697313625)
              ·
                refine ⟨4936693993490490522985219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582258657987320697313625 4936693993490490522985219)
                ·
                  refine ⟨7405040990235735784477829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4936693993490490522985219 7405040990235735784477829)
                  ·
                    refine ⟨1388445185669200459589593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7405040990235735784477829 1388445185669200459589593)
                    ·
                      rfl

theorem cell22_4055981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4055981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4055981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4055981 prefixEnd_4055981 := by exact prefixLift 4055981
  have htrace : WordTrace (prefixWord ++ tailWord_4055981) baseStart_4055981 baseEnd_4055981 := by
    simpa [prefixWord, tailWord_4055981, baseEnd_4055981] using wordTrace_append hprefix tailTrace_4055981
  have hstable : (prefixWord ++ tailWord_4055981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4055981).length < 2 ^ (prefixWord ++ tailWord_4055981).sum := by decide
  have hdescent : baseEnd_4055981 < baseStart_4055981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4055981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056095 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 1, 5]
def baseStart_4056095 : Nat := 118140960795 + 4056095 * 2 ^ 59
def prefixEnd_4056095 : Nat := 4983230072969 + 3 ^ 40 * 4056095 * 2
def baseEnd_4056095 : Nat := 1388484210198942162239243

theorem tailTrace_4056095 : CollatzResearch.WordTrace tailWord_4056095 prefixEnd_4056095 1388484210198942162239243 := by
  unfold tailWord_4056095
  simp only [CollatzResearch.WordTrace]
  refine ⟨147937938240468015720385739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98625292160312010480257159 147937938240468015720385739)
  ·
    refine ⟨221906907360702023580578609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147937938240468015720385739 221906907360702023580578609)
    ·
      refine ⟨166430180520526517685433957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221906907360702023580578609 166430180520526517685433957)
      ·
        refine ⟨31205658847598722066018867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166430180520526517685433957 31205658847598722066018867)
        ·
          refine ⟨46808488271398083099028301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31205658847598722066018867 46808488271398083099028301)
          ·
            refine ⟨17553183101774281162135613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46808488271398083099028301 17553183101774281162135613)
            ·
              refine ⟨6582443663165355435800855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17553183101774281162135613 6582443663165355435800855)
              ·
                refine ⟨9873665494748033153701283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582443663165355435800855 9873665494748033153701283)
                ·
                  refine ⟨14810498242122049730551925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873665494748033153701283 14810498242122049730551925)
                  ·
                    refine ⟨1388484210198942162239243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14810498242122049730551925 1388484210198942162239243)
                    ·
                      rfl

theorem cell22_4056095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_4056095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056095 prefixEnd_4056095 := by exact prefixLift 4056095
  have htrace : WordTrace (prefixWord ++ tailWord_4056095) baseStart_4056095 baseEnd_4056095 := by
    simpa [prefixWord, tailWord_4056095, baseEnd_4056095] using wordTrace_append hprefix tailTrace_4056095
  have hstable : (prefixWord ++ tailWord_4056095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056095).length < 2 ^ (prefixWord ++ tailWord_4056095).sum := by decide
  have hdescent : baseEnd_4056095 < baseStart_4056095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056108 : List Nat := [2, 2, 1, 1, 1, 2, 5, 8]
def baseStart_4056108 : Nat := 118140960795 + 4056108 * 2 ^ 59
def prefixEnd_4056108 : Nat := 4983230072969 + 3 ^ 40 * 4056108 * 2
def baseEnd_4056108 : Nat := 154276517818290495740467

theorem tailTrace_4056108 : CollatzResearch.WordTrace tailWord_4056108 prefixEnd_4056108 154276517818290495740467 := by
  unfold tailWord_4056108
  simp only [CollatzResearch.WordTrace]
  refine ⟨73969206194710459470304489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98625608259613945960405985 73969206194710459470304489)
  ·
    refine ⟨55476904646032844602728367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73969206194710459470304489 55476904646032844602728367)
    ·
      refine ⟨83215356969049266904092551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55476904646032844602728367 83215356969049266904092551)
      ·
        refine ⟨124823035453573900356138827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83215356969049266904092551 124823035453573900356138827)
        ·
          refine ⟨187234553180360850534208241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124823035453573900356138827 187234553180360850534208241)
          ·
            refine ⟨140425914885270637900656181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187234553180360850534208241 140425914885270637900656181)
            ·
              refine ⟨13164929520494122303186517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140425914885270637900656181 13164929520494122303186517)
              ·
                refine ⟨154276517818290495740467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13164929520494122303186517 154276517818290495740467)
                ·
                  rfl

theorem cell22_4056108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_4056108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056108 prefixEnd_4056108 := by exact prefixLift 4056108
  have htrace : WordTrace (prefixWord ++ tailWord_4056108) baseStart_4056108 baseEnd_4056108 := by
    simpa [prefixWord, tailWord_4056108, baseEnd_4056108] using wordTrace_append hprefix tailTrace_4056108
  have hstable : (prefixWord ++ tailWord_4056108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056108).length < 2 ^ (prefixWord ++ tailWord_4056108).sum := by decide
  have hdescent : baseEnd_4056108 < baseStart_4056108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056110 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4056110 : Nat := 118140960795 + 4056110 * 2 ^ 59
def prefixEnd_4056110 : Nat := 4983230072969 + 3 ^ 40 * 4056110 * 2
def baseEnd_4056110 : Nat := 1388489345005487123114197

theorem tailTrace_4056110 : CollatzResearch.WordTrace tailWord_4056110 prefixEnd_4056110 1388489345005487123114197 := by
  unfold tailWord_4056110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18492310666926709160272723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98625656890275782188121189 18492310666926709160272723)
  ·
    refine ⟨27738466000390063740409085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18492310666926709160272723 27738466000390063740409085)
    ·
      refine ⟨10401924750146273902653407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27738466000390063740409085 10401924750146273902653407)
      ·
        refine ⟨15602887125219410853980111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10401924750146273902653407 15602887125219410853980111)
        ·
          refine ⟨23404330687829116280970167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15602887125219410853980111 23404330687829116280970167)
          ·
            refine ⟨35106496031743674421455251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23404330687829116280970167 35106496031743674421455251)
            ·
              refine ⟨52659744047615511632182877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35106496031743674421455251 52659744047615511632182877)
              ·
                refine ⟨19747404017855816862068579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52659744047615511632182877 19747404017855816862068579)
                ·
                  refine ⟨29621106026783725293102869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19747404017855816862068579 29621106026783725293102869)
                  ·
                    refine ⟨1388489345005487123114197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29621106026783725293102869 1388489345005487123114197)
                    ·
                      rfl

theorem cell22_4056110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4056110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056110 prefixEnd_4056110 := by exact prefixLift 4056110
  have htrace : WordTrace (prefixWord ++ tailWord_4056110) baseStart_4056110 baseEnd_4056110 := by
    simpa [prefixWord, tailWord_4056110, baseEnd_4056110] using wordTrace_append hprefix tailTrace_4056110
  have hstable : (prefixWord ++ tailWord_4056110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056110).length < 2 ^ (prefixWord ++ tailWord_4056110).sum := by decide
  have hdescent : baseEnd_4056110 < baseStart_4056110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056125 : List Nat := [1, 4, 1, 3, 1, 4, 8]
def baseStart_4056125 : Nat := 118140960795 + 4056125 * 2 ^ 59
def prefixEnd_4056125 : Nat := 4983230072969 + 3 ^ 40 * 4056125 * 2
def baseEnd_4056125 : Nat := 51425721474519706814413

theorem tailTrace_4056125 : CollatzResearch.WordTrace tailWord_4056125 prefixEnd_4056125 51425721474519706814413 := by
  unfold tailWord_4056125
  simp only [CollatzResearch.WordTrace]
  refine ⟨147939032430359330843977829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98626021620239553895985219 147939032430359330843977829)
  ·
    refine ⟨27738568580692374533245843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147939032430359330843977829 27738568580692374533245843)
    ·
      refine ⟨41607852871038561799868765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27738568580692374533245843 41607852871038561799868765)
      ·
        refine ⟨15602944826639460674950787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41607852871038561799868765 15602944826639460674950787)
        ·
          refine ⟨23404417239959191012426181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15602944826639460674950787 23404417239959191012426181)
          ·
            refine ⟨4388328232492348314829909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23404417239959191012426181 4388328232492348314829909)
            ·
              refine ⟨51425721474519706814413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4388328232492348314829909 51425721474519706814413)
              ·
                rfl

theorem cell22_4056125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 8].length) (baseStart_4056125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056125 prefixEnd_4056125 := by exact prefixLift 4056125
  have htrace : WordTrace (prefixWord ++ tailWord_4056125) baseStart_4056125 baseEnd_4056125 := by
    simpa [prefixWord, tailWord_4056125, baseEnd_4056125] using wordTrace_append hprefix tailTrace_4056125
  have hstable : (prefixWord ++ tailWord_4056125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056125).length < 2 ^ (prefixWord ++ tailWord_4056125).sum := by decide
  have hdescent : baseEnd_4056125 < baseStart_4056125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056146 : List Nat := [3, 2, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_4056146 : Nat := 118140960795 + 4056146 * 2 ^ 59
def prefixEnd_4056146 : Nat := 4983230072969 + 3 ^ 40 * 4056146 * 2
def baseEnd_4056146 : Nat := 1388501668541195029214087

theorem tailTrace_4056146 : CollatzResearch.WordTrace tailWord_4056146 prefixEnd_4056146 1388501668541195029214087 := by
  unfold tailWord_4056146
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984949590820812857623073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98626532242188834286994861 36984949590820812857623073)
  ·
    refine ⟨27738712193115609643217305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36984949590820812857623073 27738712193115609643217305)
    ·
      refine ⟨20804034144836707232412979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27738712193115609643217305 20804034144836707232412979)
      ·
        refine ⟨31206051217255060848619469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20804034144836707232412979 31206051217255060848619469)
        ·
          refine ⟨11702269206470647818232301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31206051217255060848619469 11702269206470647818232301)
          ·
            refine ⟨4388350952426492931837113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11702269206470647818232301 4388350952426492931837113)
            ·
              refine ⟨3291263214319869698877835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388350952426492931837113 3291263214319869698877835)
              ·
                refine ⟨4936894821479804548316753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291263214319869698877835 4936894821479804548316753)
                ·
                  refine ⟨3702671116109853411237565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936894821479804548316753 3702671116109853411237565)
                  ·
                    refine ⟨1388501668541195029214087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702671116109853411237565 1388501668541195029214087)
                    ·
                      rfl

theorem cell22_4056146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_4056146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056146 prefixEnd_4056146 := by exact prefixLift 4056146
  have htrace : WordTrace (prefixWord ++ tailWord_4056146) baseStart_4056146 baseEnd_4056146 := by
    simpa [prefixWord, tailWord_4056146, baseEnd_4056146] using wordTrace_append hprefix tailTrace_4056146
  have hstable : (prefixWord ++ tailWord_4056146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056146).length < 2 ^ (prefixWord ++ tailWord_4056146).sum := by decide
  have hdescent : baseEnd_4056146 < baseStart_4056146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056153 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 9]
def baseStart_4056153 : Nat := 118140960795 + 4056153 * 2 ^ 59
def prefixEnd_4056153 : Nat := 4983230072969 + 3 ^ 40 * 4056153 * 2
def baseEnd_4056153 : Nat := 462834688261416448096355

theorem tailTrace_4056153 : CollatzResearch.WordTrace tailWord_4056153 prefixEnd_4056153 462834688261416448096355 := by
  unfold tailWord_4056153
  simp only [CollatzResearch.WordTrace]
  refine ⟨147940053674257891625997113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98626702449505261083998075 147940053674257891625997113)
  ·
    refine ⟨110955040255693418719497835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147940053674257891625997113 110955040255693418719497835)
    ·
      refine ⟨166432560383540128079246753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110955040255693418719497835 166432560383540128079246753)
      ·
        refine ⟨124824420287655096059435065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166432560383540128079246753 124824420287655096059435065)
        ·
          refine ⟨93618315215741322044576299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124824420287655096059435065 93618315215741322044576299)
          ·
            refine ⟨140427472823611983066864449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93618315215741322044576299 140427472823611983066864449)
            ·
              refine ⟨105320604617708987300148337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140427472823611983066864449 105320604617708987300148337)
              ·
                refine ⟨78990453463281740475111253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105320604617708987300148337 78990453463281740475111253)
                ·
                  refine ⟨462834688261416448096355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78990453463281740475111253 462834688261416448096355)
                  ·
                    rfl

theorem cell22_4056153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_4056153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056153 prefixEnd_4056153 := by exact prefixLift 4056153
  have htrace : WordTrace (prefixWord ++ tailWord_4056153) baseStart_4056153 baseEnd_4056153 := by
    simpa [prefixWord, tailWord_4056153, baseEnd_4056153] using wordTrace_append hprefix tailTrace_4056153
  have hstable : (prefixWord ++ tailWord_4056153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056153).length < 2 ^ (prefixWord ++ tailWord_4056153).sum := by decide
  have hdescent : baseEnd_4056153 < baseStart_4056153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056215 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 8]
def baseStart_4056215 : Nat := 118140960795 + 4056215 * 2 ^ 59
def prefixEnd_4056215 : Nat := 4983230072969 + 3 ^ 40 * 4056215 * 2
def baseEnd_4056215 : Nat := 462841762883767283079625

theorem tailTrace_4056215 : CollatzResearch.WordTrace tailWord_4056215 prefixEnd_4056215 462841762883767283079625 := by
  unfold tailWord_4056215
  simp only [CollatzResearch.WordTrace]
  refine ⟨147942315000033276214754099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98628210000022184143169399 147942315000033276214754099)
  ·
    refine ⟨221913472500049914322131149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147942315000033276214754099 221913472500049914322131149)
    ·
      refine ⟨83217552187518717870799181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221913472500049914322131149 83217552187518717870799181)
      ·
        refine ⟨31206582070319519201549693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83217552187518717870799181 31206582070319519201549693)
        ·
          refine ⟨11702468276369819700581135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31206582070319519201549693 11702468276369819700581135)
          ·
            refine ⟨17553702414554729550871703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702468276369819700581135 17553702414554729550871703)
            ·
              refine ⟨26330553621832094326307555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17553702414554729550871703 26330553621832094326307555)
              ·
                refine ⟨39495830432748141489461333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26330553621832094326307555 39495830432748141489461333)
                ·
                  refine ⟨462841762883767283079625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39495830432748141489461333 462841762883767283079625)
                  ·
                    rfl

theorem cell22_4056215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_4056215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056215 prefixEnd_4056215 := by exact prefixLift 4056215
  have htrace : WordTrace (prefixWord ++ tailWord_4056215) baseStart_4056215 baseEnd_4056215 := by
    simpa [prefixWord, tailWord_4056215, baseEnd_4056215] using wordTrace_append hprefix tailTrace_4056215
  have hstable : (prefixWord ++ tailWord_4056215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056215).length < 2 ^ (prefixWord ++ tailWord_4056215).sum := by decide
  have hdescent : baseEnd_4056215 < baseStart_4056215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056247 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 4, 3]
def baseStart_4056247 : Nat := 118140960795 + 4056247 * 2 ^ 59
def prefixEnd_4056247 : Nat := 4983230072969 + 3 ^ 40 * 4056247 * 2
def baseEnd_4056247 : Nat := 1388536242905264432438777

theorem tailTrace_4056247 : CollatzResearch.WordTrace tailWord_4056247 prefixEnd_4056247 1388536242905264432438777 := by
  unfold tailWord_4056247
  simp only [CollatzResearch.WordTrace]
  refine ⟨147943482135917345679918995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98628988090611563786612663 147943482135917345679918995)
  ·
    refine ⟨221915223203876018519878493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147943482135917345679918995 221915223203876018519878493)
    ·
      refine ⟨83218208701453506944954435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221915223203876018519878493 83218208701453506944954435)
      ·
        refine ⟨124827313052180260417431653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83218208701453506944954435 124827313052180260417431653)
        ·
          refine ⟨23405121197283798828268435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124827313052180260417431653 23405121197283798828268435)
          ·
            refine ⟨35107681795925698242402653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23405121197283798828268435 35107681795925698242402653)
            ·
              refine ⟨13165380673472136840900995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35107681795925698242402653 13165380673472136840900995)
              ·
                refine ⟨19748071010208205261351493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165380673472136840900995 19748071010208205261351493)
                ·
                  refine ⟨3702763314414038486503405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19748071010208205261351493 3702763314414038486503405)
                  ·
                    refine ⟨1388536242905264432438777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702763314414038486503405 1388536242905264432438777)
                    ·
                      rfl

theorem cell22_4056247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_4056247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056247 prefixEnd_4056247 := by exact prefixLift 4056247
  have htrace : WordTrace (prefixWord ++ tailWord_4056247) baseStart_4056247 baseEnd_4056247 := by
    simpa [prefixWord, tailWord_4056247, baseEnd_4056247] using wordTrace_append hprefix tailTrace_4056247
  have hstable : (prefixWord ++ tailWord_4056247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056247).length < 2 ^ (prefixWord ++ tailWord_4056247).sum := by decide
  have hdescent : baseEnd_4056247 < baseStart_4056247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056277 : List Nat := [1, 3, 2, 4, 1, 2, 1, 8]
def baseStart_4056277 : Nat := 118140960795 + 4056277 * 2 ^ 59
def prefixEnd_4056277 : Nat := 4983230072969 + 3 ^ 40 * 4056277 * 2
def baseEnd_4056277 : Nat := 154282945835372706020965

theorem tailTrace_4056277 : CollatzResearch.WordTrace tailWord_4056277 prefixEnd_4056277 154282945835372706020965 := by
  unfold tailWord_4056277
  simp only [CollatzResearch.WordTrace]
  refine ⟨147944576325808660803511085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98629717550539107202340723 147944576325808660803511085)
  ·
    refine ⟨55479216122178247801316657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147944576325808660803511085 55479216122178247801316657)
    ·
      refine ⟨41609412091633685850987493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55479216122178247801316657 41609412091633685850987493)
      ·
        refine ⟨7801764767181316097060155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41609412091633685850987493 7801764767181316097060155)
        ·
          refine ⟨11702647150771974145590233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7801764767181316097060155 11702647150771974145590233)
          ·
            refine ⟨8776985363078980609192675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11702647150771974145590233 8776985363078980609192675)
            ·
              refine ⟨13165478044618470913789013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776985363078980609192675 13165478044618470913789013)
              ·
                refine ⟨154282945835372706020965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13165478044618470913789013 154282945835372706020965)
                ·
                  rfl

theorem cell22_4056277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 8].length) (baseStart_4056277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056277 prefixEnd_4056277 := by exact prefixLift 4056277
  have htrace : WordTrace (prefixWord ++ tailWord_4056277) baseStart_4056277 baseEnd_4056277 := by
    simpa [prefixWord, tailWord_4056277, baseEnd_4056277] using wordTrace_append hprefix tailTrace_4056277
  have hstable : (prefixWord ++ tailWord_4056277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056277).length < 2 ^ (prefixWord ++ tailWord_4056277).sum := by decide
  have hdescent : baseEnd_4056277 < baseStart_4056277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056292 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_4056292 : Nat := 118140960795 + 4056292 * 2 ^ 59
def prefixEnd_4056292 : Nat := 4983230072969 + 3 ^ 40 * 4056292 * 2
def baseEnd_4056292 : Nat := 1388551647324899315063639

theorem tailTrace_4056292 : CollatzResearch.WordTrace tailWord_4056292 prefixEnd_4056292 1388551647324899315063639 := by
  unfold tailWord_4056292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73972561710377159182653565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98630082280502878910204753 73972561710377159182653565)
  ·
    refine ⟨27739710641391434693495087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73972561710377159182653565 27739710641391434693495087)
    ·
      refine ⟨41609565962087152040242631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739710641391434693495087 41609565962087152040242631)
      ·
        refine ⟨62414348943130728060363947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41609565962087152040242631 62414348943130728060363947)
        ·
          refine ⟨93621523414696092090545921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62414348943130728060363947 93621523414696092090545921)
          ·
            refine ⟨70216142561022069067909441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93621523414696092090545921 70216142561022069067909441)
            ·
              refine ⟨52662106920766551800932081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70216142561022069067909441 52662106920766551800932081)
              ·
                refine ⟨39496580190574913850699061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52662106920766551800932081 39496580190574913850699061)
                ·
                  refine ⟨3702804392866398173503037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39496580190574913850699061 3702804392866398173503037)
                  ·
                    refine ⟨1388551647324899315063639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702804392866398173503037 1388551647324899315063639)
                    ·
                      rfl

theorem cell22_4056292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_4056292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056292 prefixEnd_4056292 := by exact prefixLift 4056292
  have htrace : WordTrace (prefixWord ++ tailWord_4056292) baseStart_4056292 baseEnd_4056292 := by
    simpa [prefixWord, tailWord_4056292, baseEnd_4056292] using wordTrace_append hprefix tailTrace_4056292
  have hstable : (prefixWord ++ tailWord_4056292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056292).length < 2 ^ (prefixWord ++ tailWord_4056292).sum := by decide
  have hdescent : baseEnd_4056292 < baseStart_4056292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056320 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_4056320 : Nat := 118140960795 + 4056320 * 2 ^ 59
def prefixEnd_4056320 : Nat := 4983230072969 + 3 ^ 40 * 4056320 * 2
def baseEnd_4056320 : Nat := 1388561232297116575363553

theorem tailTrace_4056320 : CollatzResearch.WordTrace tailWord_4056320 prefixEnd_4056320 1388561232297116575363553 := by
  unfold tailWord_4056320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973072332326439573663207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98630763109768586098217609 73973072332326439573663207)
  ·
    refine ⟨110959608498489659360494811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73973072332326439573663207 110959608498489659360494811)
    ·
      refine ⟨166439412747734489040742217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110959608498489659360494811 166439412747734489040742217)
      ·
        refine ⟨124829559560800866780556663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166439412747734489040742217 124829559560800866780556663)
        ·
          refine ⟨187244339341201300170834995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124829559560800866780556663 187244339341201300170834995)
          ·
            refine ⟨280866509011801950256252493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187244339341201300170834995 280866509011801950256252493)
            ·
              refine ⟨105324940879425731346094685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280866509011801950256252493 105324940879425731346094685)
              ·
                refine ⟨39496852829784649254785507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105324940879425731346094685 39496852829784649254785507)
                ·
                  refine ⟨59245279244676973882178261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39496852829784649254785507 59245279244676973882178261)
                  ·
                    refine ⟨1388561232297116575363553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59245279244676973882178261 1388561232297116575363553)
                    ·
                      rfl

theorem cell22_4056320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_4056320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056320 prefixEnd_4056320 := by exact prefixLift 4056320
  have htrace : WordTrace (prefixWord ++ tailWord_4056320) baseStart_4056320 baseEnd_4056320 := by
    simpa [prefixWord, tailWord_4056320, baseEnd_4056320] using wordTrace_append hprefix tailTrace_4056320
  have hstable : (prefixWord ++ tailWord_4056320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056320).length < 2 ^ (prefixWord ++ tailWord_4056320).sum := by decide
  have hdescent : baseEnd_4056320 < baseStart_4056320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056360 : List Nat := [2, 1, 5, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4056360 : Nat := 118140960795 + 4056360 * 2 ^ 59
def prefixEnd_4056360 : Nat := 4983230072969 + 3 ^ 40 * 4056360 * 2
def baseEnd_4056360 : Nat := 1388574925114569804363431

theorem tailTrace_4056360 : CollatzResearch.WordTrace tailWord_4056360 prefixEnd_4056360 1388574925114569804363431 := by
  unfold tailWord_4056360
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973801792253982989391267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98631735723005310652521689 73973801792253982989391267)
  ·
    refine ⟨110960702688380974484086901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73973801792253982989391267 110960702688380974484086901)
    ·
      refine ⟨10402565877035716357883147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110960702688380974484086901 10402565877035716357883147)
      ·
        refine ⟨15603848815553574536824721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10402565877035716357883147 15603848815553574536824721)
        ·
          refine ⟨11702886611665180902618541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15603848815553574536824721 11702886611665180902618541)
          ·
            refine ⟨4388582479374442838481953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11702886611665180902618541 4388582479374442838481953)
            ·
              refine ⟨3291436859530832128861465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4388582479374442838481953 3291436859530832128861465)
              ·
                refine ⟨2468577644648124096646099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291436859530832128861465 2468577644648124096646099)
                ·
                  refine ⟨3702866466972186144969149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468577644648124096646099 3702866466972186144969149)
                  ·
                    refine ⟨1388574925114569804363431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702866466972186144969149 1388574925114569804363431)
                    ·
                      rfl

theorem cell22_4056360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4056360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056360 prefixEnd_4056360 := by exact prefixLift 4056360
  have htrace : WordTrace (prefixWord ++ tailWord_4056360) baseStart_4056360 baseEnd_4056360 := by
    simpa [prefixWord, tailWord_4056360, baseEnd_4056360] using wordTrace_append hprefix tailTrace_4056360
  have hstable : (prefixWord ++ tailWord_4056360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056360).length < 2 ^ (prefixWord ++ tailWord_4056360).sum := by decide
  have hdescent : baseEnd_4056360 < baseStart_4056360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056416 : List Nat := [2, 1, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_4056416 : Nat := 118140960795 + 4056416 * 2 ^ 59
def prefixEnd_4056416 : Nat := 4983230072969 + 3 ^ 40 * 4056416 * 2
def baseEnd_4056416 : Nat := 1388594095059004324963259

theorem tailTrace_4056416 : CollatzResearch.WordTrace tailWord_4056416 prefixEnd_4056416 1388594095059004324963259 := by
  unfold tailWord_4056416
  simp only [CollatzResearch.WordTrace]
  refine ⟨73974823036152543771410551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98633097381536725028547401 73974823036152543771410551)
  ·
    refine ⟨110962234554228815657115827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73974823036152543771410551 110962234554228815657115827)
    ·
      refine ⟨166443351831343223485673741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110962234554228815657115827 166443351831343223485673741)
      ·
        refine ⟨62416256936753708807127653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166443351831343223485673741 62416256936753708807127653)
        ·
          refine ⟨11703048175641320401336435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62416256936753708807127653 11703048175641320401336435)
          ·
            refine ⟨17554572263461980602004653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11703048175641320401336435 17554572263461980602004653)
            ·
              refine ⟨6582964598798242725751745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17554572263461980602004653 6582964598798242725751745)
              ·
                refine ⟨4937223449098682044313809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582964598798242725751745 4937223449098682044313809)
                ·
                  refine ⟨3702917586824011533235357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937223449098682044313809 3702917586824011533235357)
                  ·
                    refine ⟨1388594095059004324963259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702917586824011533235357 1388594095059004324963259)
                    ·
                      rfl

theorem cell22_4056416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_4056416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056416 prefixEnd_4056416 := by exact prefixLift 4056416
  have htrace : WordTrace (prefixWord ++ tailWord_4056416) baseStart_4056416 baseEnd_4056416 := by
    simpa [prefixWord, tailWord_4056416, baseEnd_4056416] using wordTrace_append hprefix tailTrace_4056416
  have hstable : (prefixWord ++ tailWord_4056416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056416).length < 2 ^ (prefixWord ++ tailWord_4056416).sum := by decide
  have hdescent : baseEnd_4056416 < baseStart_4056416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
