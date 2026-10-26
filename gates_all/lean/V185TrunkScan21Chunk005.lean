import V185TrunkScan21Chunk004

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_60424 : List Nat := [2, 1, 3, 2, 1, 3, 4, 2, 3]
def baseStart_60424 : Nat := 118140960795 + 60424 * 2 ^ 59
def prefixEnd_60424 : Nat := 4983230072969 + 3 ^ 40 * 60424 * 2
def baseEnd_60424 : Nat := 13789580029945255343165

theorem tailTrace_60424 : CollatzResearch.WordTrace tailWord_60424 prefixEnd_60424 13789580029945255343165 := by
  unfold tailWord_60424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101922166550821221362163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1469229555401094961816217 1101922166550821221362163)
  ·
    refine ⟨1652883249826231832043245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101922166550821221362163 1652883249826231832043245)
    ·
      refine ⟨619831218684836937016217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1652883249826231832043245 619831218684836937016217)
      ·
        refine ⟨464873414013627702762163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619831218684836937016217 464873414013627702762163)
        ·
          refine ⟨697310121020441554143245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464873414013627702762163 697310121020441554143245)
          ·
            refine ⟨261491295382665582803717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 697310121020441554143245 261491295382665582803717)
            ·
              refine ⟨49029617884249796775697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261491295382665582803717 49029617884249796775697)
              ·
                refine ⟨36772213413187347581773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49029617884249796775697 36772213413187347581773)
                ·
                  refine ⟨13789580029945255343165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36772213413187347581773 13789580029945255343165)
                  ·
                    rfl

theorem cell21_60424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 2, 3].length) (baseStart_60424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60424 prefixEnd_60424 := by exact prefixLift 60424
  have htrace : WordTrace (prefixWord ++ tailWord_60424) baseStart_60424 baseEnd_60424 := by
    simpa [prefixWord, tailWord_60424, baseEnd_60424] using wordTrace_append hprefix tailTrace_60424
  have hstable : (prefixWord ++ tailWord_60424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60424).length < 2 ^ (prefixWord ++ tailWord_60424).sum := by decide
  have hdescent : baseEnd_60424 < baseStart_60424 := by decide
  rcases family_descends (prefixWord ++ tailWord_60424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60480 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_60480 : Nat := 118140960795 + 60480 * 2 ^ 59
def prefixEnd_60480 : Nat := 4983230072969 + 3 ^ 40 * 60480 * 2
def baseEnd_60480 : Nat := 13802359992901602409717

theorem tailTrace_60480 : CollatzResearch.WordTrace tailWord_60480 prefixEnd_60480 13802359992901602409717 := by
  unfold tailWord_60480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102943410449382003381447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1470591213932509337841929 1102943410449382003381447)
  ·
    refine ⟨1654415115674073005072171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102943410449382003381447 1654415115674073005072171)
    ·
      refine ⟨2481622673511109507608257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654415115674073005072171 2481622673511109507608257)
      ·
        refine ⟨1861217005133332130706193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2481622673511109507608257 1861217005133332130706193)
        ·
          refine ⟨1395912753849999098029645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861217005133332130706193 1395912753849999098029645)
          ·
            refine ⟨523467282693749661761117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395912753849999098029645 523467282693749661761117)
            ·
              refine ⟨196300231010156123160419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523467282693749661761117 196300231010156123160419)
              ·
                refine ⟨294450346515234184740629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196300231010156123160419 294450346515234184740629)
                ·
                  refine ⟨13802359992901602409717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 294450346515234184740629 13802359992901602409717)
                  ·
                    rfl

theorem cell21_60480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_60480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60480 prefixEnd_60480 := by exact prefixLift 60480
  have htrace : WordTrace (prefixWord ++ tailWord_60480) baseStart_60480 baseEnd_60480 := by
    simpa [prefixWord, tailWord_60480, baseEnd_60480] using wordTrace_append hprefix tailTrace_60480
  have hstable : (prefixWord ++ tailWord_60480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60480).length < 2 ^ (prefixWord ++ tailWord_60480).sum := by decide
  have hdescent : baseEnd_60480 < baseStart_60480 := by decide
  rcases family_descends (prefixWord ++ tailWord_60480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60593 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 3]
def baseStart_60593 : Nat := 118140960795 + 60593 * 2 ^ 59
def prefixEnd_60593 : Nat := 4983230072969 + 3 ^ 40 * 60593 * 2
def baseEnd_60593 : Nat := 13828148132438517026153

theorem tailTrace_60593 : CollatzResearch.WordTrace tailWord_60593 prefixEnd_60593 13828148132438517026153 := by
  unfold tailWord_60593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210008269489384305626433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1473338846326256203750955 2210008269489384305626433)
  ·
    refine ⟨1657506202117038229219825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2210008269489384305626433 1657506202117038229219825)
    ·
      refine ⟨1243129651587778671914869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1657506202117038229219825 1243129651587778671914869)
      ·
        refine ⟨116543404836354250492019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1243129651587778671914869 116543404836354250492019)
        ·
          refine ⟨174815107254531375738029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116543404836354250492019 174815107254531375738029)
          ·
            refine ⟨65555665220449265901761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174815107254531375738029 65555665220449265901761)
            ·
              refine ⟨49166748915336949426321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65555665220449265901761 49166748915336949426321)
              ·
                refine ⟨36875061686502712069741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49166748915336949426321 36875061686502712069741)
                ·
                  refine ⟨13828148132438517026153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36875061686502712069741 13828148132438517026153)
                  ·
                    rfl

theorem cell21_60593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_60593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60593 prefixEnd_60593 := by exact prefixLift 60593
  have htrace : WordTrace (prefixWord ++ tailWord_60593) baseStart_60593 baseEnd_60593 := by
    simpa [prefixWord, tailWord_60593, baseEnd_60593] using wordTrace_append hprefix tailTrace_60593
  have hstable : (prefixWord ++ tailWord_60593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60593).length < 2 ^ (prefixWord ++ tailWord_60593).sum := by decide
  have hdescent : baseEnd_60593 < baseStart_60593 := by decide
  rcases family_descends (prefixWord ++ tailWord_60593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60604 : List Nat := [2, 2, 2, 3, 2, 3, 1, 6]
def baseStart_60604 : Nat := 118140960795 + 60604 * 2 ^ 59
def prefixEnd_60604 : Nat := 4983230072969 + 3 ^ 40 * 60604 * 2
def baseEnd_60604 : Nat := 4610219494101647447599

theorem tailTrace_60604 : CollatzResearch.WordTrace tailWord_60604 prefixEnd_60604 4610219494101647447599 := by
  unfold tailWord_60604
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105204736224766592138433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1473606314966355456184577 1105204736224766592138433)
  ·
    refine ⟨828903552168574944103825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1105204736224766592138433 828903552168574944103825)
    ·
      refine ⟨621677664126431208077869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828903552168574944103825 621677664126431208077869)
      ·
        refine ⟨233129124047411703029201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621677664126431208077869 233129124047411703029201)
        ·
          refine ⟨174846843035558777271901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233129124047411703029201 174846843035558777271901)
          ·
            refine ⟨65567566138334541476963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174846843035558777271901 65567566138334541476963)
            ·
              refine ⟨98351349207501812215445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65567566138334541476963 98351349207501812215445)
              ·
                refine ⟨4610219494101647447599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98351349207501812215445 4610219494101647447599)
                ·
                  rfl

theorem cell21_60604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_60604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60604 prefixEnd_60604 := by exact prefixLift 60604
  have htrace : WordTrace (prefixWord ++ tailWord_60604) baseStart_60604 baseEnd_60604 := by
    simpa [prefixWord, tailWord_60604, baseEnd_60604] using wordTrace_append hprefix tailTrace_60604
  have hstable : (prefixWord ++ tailWord_60604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60604).length < 2 ^ (prefixWord ++ tailWord_60604).sum := by decide
  have hdescent : baseEnd_60604 < baseStart_60604 := by decide
  rcases family_descends (prefixWord ++ tailWord_60604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60618 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_60618 : Nat := 118140960795 + 60618 * 2 ^ 59
def prefixEnd_60618 : Nat := 4983230072969 + 3 ^ 40 * 60618 * 2
def baseEnd_60618 : Nat := 13833853473044029109435

theorem tailTrace_60618 : CollatzResearch.WordTrace tailWord_60618 prefixEnd_60618 13833853473044029109435 := by
  unfold tailWord_60618
  simp only [CollatzResearch.WordTrace]
  refine ⟨552730023599703393821627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1473946729599209050191005 552730023599703393821627)
  ·
    refine ⟨829095035399555090732441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552730023599703393821627 829095035399555090732441)
    ·
      refine ⟨621821276549666318049331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 829095035399555090732441 621821276549666318049331)
      ·
        refine ⟨932731914824499477073997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621821276549666318049331 932731914824499477073997)
        ·
          refine ⟨349774468059187303902749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 932731914824499477073997 349774468059187303902749)
          ·
            refine ⟨131165425522195238963531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349774468059187303902749 131165425522195238963531)
            ·
              refine ⟨196748138283292858445297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131165425522195238963531 196748138283292858445297)
              ·
                refine ⟨147561103712469643833973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196748138283292858445297 147561103712469643833973)
                ·
                  refine ⟨13833853473044029109435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147561103712469643833973 13833853473044029109435)
                  ·
                    rfl

theorem cell21_60618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_60618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60618 prefixEnd_60618 := by exact prefixLift 60618
  have htrace : WordTrace (prefixWord ++ tailWord_60618) baseStart_60618 baseEnd_60618 := by
    simpa [prefixWord, tailWord_60618, baseEnd_60618] using wordTrace_append hprefix tailTrace_60618
  have hstable : (prefixWord ++ tailWord_60618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60618).length < 2 ^ (prefixWord ++ tailWord_60618).sum := by decide
  have hdescent : baseEnd_60618 < baseStart_60618 := by decide
  rcases family_descends (prefixWord ++ tailWord_60618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60677 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_60677 : Nat := 118140960795 + 60677 * 2 ^ 59
def prefixEnd_60677 : Nat := 4983230072969 + 3 ^ 40 * 60677 * 2
def baseEnd_60677 : Nat := 13847318076873037625981

theorem tailTrace_60677 : CollatzResearch.WordTrace tailWord_60677 prefixEnd_60677 13847318076873037625981 := by
  unfold tailWord_60677
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213072001185066651684285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1475381334123377767789523 2213072001185066651684285)
  ·
    refine ⟨829902000444399994381607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2213072001185066651684285 829902000444399994381607)
    ·
      refine ⟨1244853000666599991572411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829902000444399994381607 1244853000666599991572411)
      ·
        refine ⟨1867279500999899987358617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244853000666599991572411 1867279500999899987358617)
        ·
          refine ⟨1400459625749924990518963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867279500999899987358617 1400459625749924990518963)
          ·
            refine ⟨2100689438624887485778445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400459625749924990518963 2100689438624887485778445)
            ·
              refine ⟨787758539484332807166917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2100689438624887485778445 787758539484332807166917)
              ·
                refine ⟨147704726153312401343797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 787758539484332807166917 147704726153312401343797)
                ·
                  refine ⟨13847318076873037625981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147704726153312401343797 13847318076873037625981)
                  ·
                    rfl

theorem cell21_60677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_60677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60677 prefixEnd_60677 := by exact prefixLift 60677
  have htrace : WordTrace (prefixWord ++ tailWord_60677) baseStart_60677 baseEnd_60677 := by
    simpa [prefixWord, tailWord_60677, baseEnd_60677] using wordTrace_append hprefix tailTrace_60677
  have hstable : (prefixWord ++ tailWord_60677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60677).length < 2 ^ (prefixWord ++ tailWord_60677).sum := by decide
  have hdescent : baseEnd_60677 < baseStart_60677 := by decide
  rcases family_descends (prefixWord ++ tailWord_60677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60708 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_60708 : Nat := 118140960795 + 60708 * 2 ^ 59
def prefixEnd_60708 : Nat := 4983230072969 + 3 ^ 40 * 60708 * 2
def baseEnd_60708 : Nat := 13854392699223872609251

theorem tailTrace_60708 : CollatzResearch.WordTrace tailWord_60708 prefixEnd_60708 13854392699223872609251 := by
  unfold tailWord_60708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1107101332036379473031389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1476135109381839297375185 1107101332036379473031389)
  ·
    refine ⟨415162999513642302386771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1107101332036379473031389 415162999513642302386771)
    ·
      refine ⟨622744499270463453580157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415162999513642302386771 622744499270463453580157)
      ·
        refine ⟨233529187226423795092559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 622744499270463453580157 233529187226423795092559)
        ·
          refine ⟨350293780839635692638839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233529187226423795092559 350293780839635692638839)
          ·
            refine ⟨525440671259453538958259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350293780839635692638839 525440671259453538958259)
            ·
              refine ⟨788161006889180308437389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525440671259453538958259 788161006889180308437389)
              ·
                refine ⟨295560377583442615664021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 788161006889180308437389 295560377583442615664021)
                ·
                  refine ⟨13854392699223872609251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 295560377583442615664021 13854392699223872609251)
                  ·
                    rfl

theorem cell21_60708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_60708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60708 prefixEnd_60708 := by exact prefixLift 60708
  have htrace : WordTrace (prefixWord ++ tailWord_60708) baseStart_60708 baseEnd_60708 := by
    simpa [prefixWord, tailWord_60708, baseEnd_60708] using wordTrace_append hprefix tailTrace_60708
  have hstable : (prefixWord ++ tailWord_60708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60708).length < 2 ^ (prefixWord ++ tailWord_60708).sum := by decide
  have hdescent : baseEnd_60708 < baseStart_60708 := by decide
  rcases family_descends (prefixWord ++ tailWord_60708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60725 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_60725 : Nat := 118140960795 + 60725 * 2 ^ 59
def prefixEnd_60725 : Nat := 4983230072969 + 3 ^ 40 * 60725 * 2
def baseEnd_60725 : Nat := 13858272330835620825883

theorem tailTrace_60725 : CollatzResearch.WordTrace tailWord_60725 prefixEnd_60725 13858272330835620825883 := by
  unfold tailWord_60725
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214822705011170849431629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1476548470007447232954419 2214822705011170849431629)
  ·
    refine ⟨830558514379189068536861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2214822705011170849431629 830558514379189068536861)
    ·
      refine ⟨311459442892195900701323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 830558514379189068536861 311459442892195900701323)
      ·
        refine ⟨467189164338293851051985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311459442892195900701323 467189164338293851051985)
        ·
          refine ⟨350391873253720388288989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467189164338293851051985 350391873253720388288989)
          ·
            refine ⟨131396952470145145608371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350391873253720388288989 131396952470145145608371)
            ·
              refine ⟨197095428705217718412557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131396952470145145608371 197095428705217718412557)
              ·
                refine ⟨73910785764456644404709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197095428705217718412557 73910785764456644404709)
                ·
                  refine ⟨13858272330835620825883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73910785764456644404709 13858272330835620825883)
                  ·
                    rfl

theorem cell21_60725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_60725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60725 prefixEnd_60725 := by exact prefixLift 60725
  have htrace : WordTrace (prefixWord ++ tailWord_60725) baseStart_60725 baseEnd_60725 := by
    simpa [prefixWord, tailWord_60725, baseEnd_60725] using wordTrace_append hprefix tailTrace_60725
  have hstable : (prefixWord ++ tailWord_60725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60725).length < 2 ^ (prefixWord ++ tailWord_60725).sum := by decide
  have hdescent : baseEnd_60725 < baseStart_60725 := by decide
  rcases family_descends (prefixWord ++ tailWord_60725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60770 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_60770 : Nat := 118140960795 + 60770 * 2 ^ 59
def prefixEnd_60770 : Nat := 4983230072969 + 3 ^ 40 * 60770 * 2
def baseEnd_60770 : Nat := 13868541943925542575791

theorem tailTrace_60770 : CollatzResearch.WordTrace tailWord_60770 prefixEnd_60770 13868541943925542575791 := by
  unfold tailWord_60770
  simp only [CollatzResearch.WordTrace]
  refine ⟨554115997462035883704941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1477642659898762356546509 554115997462035883704941)
  ·
    refine ⟨207793499048263456389353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 554115997462035883704941 207793499048263456389353)
    ·
      refine ⟨155845124286197592292015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207793499048263456389353 155845124286197592292015)
      ·
        refine ⟨233767686429296388438023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155845124286197592292015 233767686429296388438023)
        ·
          refine ⟨350651529643944582657035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233767686429296388438023 350651529643944582657035)
          ·
            refine ⟨525977294465916873985553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350651529643944582657035 525977294465916873985553)
            ·
              refine ⟨394482970849437655489165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525977294465916873985553 394482970849437655489165)
              ·
                refine ⟨147931114068539120808437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 394482970849437655489165 147931114068539120808437)
                ·
                  refine ⟨13868541943925542575791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147931114068539120808437 13868541943925542575791)
                  ·
                    rfl

theorem cell21_60770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_60770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60770 prefixEnd_60770 := by exact prefixLift 60770
  have htrace : WordTrace (prefixWord ++ tailWord_60770) baseStart_60770 baseEnd_60770 := by
    simpa [prefixWord, tailWord_60770, baseEnd_60770] using wordTrace_append hprefix tailTrace_60770
  have hstable : (prefixWord ++ tailWord_60770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60770).length < 2 ^ (prefixWord ++ tailWord_60770).sum := by decide
  have hdescent : baseEnd_60770 < baseStart_60770 := by decide
  rcases family_descends (prefixWord ++ tailWord_60770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60784 : List Nat := [2, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_60784 : Nat := 118140960795 + 60784 * 2 ^ 59
def prefixEnd_60784 : Nat := 4983230072969 + 3 ^ 40 * 60784 * 2
def baseEnd_60784 : Nat := 13871736934664629342429

theorem tailTrace_60784 : CollatzResearch.WordTrace tailWord_60784 prefixEnd_60784 13871736934664629342429 := by
  unfold tailWord_60784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108487305898711962914703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1477983074531615950552937 1108487305898711962914703)
  ·
    refine ⟨1662730958848067944372055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1108487305898711962914703 1662730958848067944372055)
    ·
      refine ⟨2494096438272101916558083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662730958848067944372055 2494096438272101916558083)
      ·
        refine ⟨3741144657408152874837125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494096438272101916558083 3741144657408152874837125)
        ·
          refine ⟨701464623264028664031961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3741144657408152874837125 701464623264028664031961)
          ·
            refine ⟨526098467448021498023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701464623264028664031961 526098467448021498023971)
            ·
              refine ⟨789147701172032247035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526098467448021498023971 789147701172032247035957)
              ·
                refine ⟨73982596984878023159621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789147701172032247035957 73982596984878023159621)
                ·
                  refine ⟨13871736934664629342429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73982596984878023159621 13871736934664629342429)
                  ·
                    rfl

theorem cell21_60784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_60784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60784 prefixEnd_60784 := by exact prefixLift 60784
  have htrace : WordTrace (prefixWord ++ tailWord_60784) baseStart_60784 baseEnd_60784 := by
    simpa [prefixWord, tailWord_60784, baseEnd_60784] using wordTrace_append hprefix tailTrace_60784
  have hstable : (prefixWord ++ tailWord_60784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60784).length < 2 ^ (prefixWord ++ tailWord_60784).sum := by decide
  have hdescent : baseEnd_60784 < baseStart_60784 := by decide
  rcases family_descends (prefixWord ++ tailWord_60784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60818 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_60818 : Nat := 118140960795 + 60818 * 2 ^ 59
def prefixEnd_60818 : Nat := 4983230072969 + 3 ^ 40 * 60818 * 2
def baseEnd_60818 : Nat := 13879496197888125775693

theorem tailTrace_60818 : CollatzResearch.WordTrace tailWord_60818 prefixEnd_60818 13879496197888125775693 := by
  unfold tailWord_60818
  simp only [CollatzResearch.WordTrace]
  refine ⟨554553673418561933141777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1478809795782831821711405 554553673418561933141777)
  ·
    refine ⟨415915255063921449856333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 554553673418561933141777 415915255063921449856333)
    ·
      refine ⟨155968220648970543696125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415915255063921449856333 155968220648970543696125)
      ·
        refine ⟨58488082743363953886047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155968220648970543696125 58488082743363953886047)
        ·
          refine ⟨87732124115045930829071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58488082743363953886047 87732124115045930829071)
          ·
            refine ⟨131598186172568896243607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87732124115045930829071 131598186172568896243607)
            ·
              refine ⟨197397279258853344365411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131598186172568896243607 197397279258853344365411)
              ·
                refine ⟨296095918888280016548117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197397279258853344365411 296095918888280016548117)
                ·
                  refine ⟨13879496197888125775693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 296095918888280016548117 13879496197888125775693)
                  ·
                    rfl

theorem cell21_60818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_60818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60818 prefixEnd_60818 := by exact prefixLift 60818
  have htrace : WordTrace (prefixWord ++ tailWord_60818) baseStart_60818 baseEnd_60818 := by
    simpa [prefixWord, tailWord_60818, baseEnd_60818] using wordTrace_append hprefix tailTrace_60818
  have hstable : (prefixWord ++ tailWord_60818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60818).length < 2 ^ (prefixWord ++ tailWord_60818).sum := by decide
  have hdescent : baseEnd_60818 < baseStart_60818 := by decide
  rcases family_descends (prefixWord ++ tailWord_60818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60874 : List Nat := [3, 1, 2, 1, 2, 3, 9]
def baseStart_60874 : Nat := 118140960795 + 60874 * 2 ^ 59
def prefixEnd_60874 : Nat := 4983230072969 + 3 ^ 40 * 60874 * 2
def baseEnd_60874 : Nat := 1543586240093830315805

theorem tailTrace_60874 : CollatzResearch.WordTrace tailWord_60874 prefixEnd_60874 1543586240093830315805 := by
  unfold tailWord_60874
  simp only [CollatzResearch.WordTrace]
  refine ⟨555064295367842324151419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1480171454314246197737117 555064295367842324151419)
  ·
    refine ⟨832596443051763486227129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 555064295367842324151419 832596443051763486227129)
    ·
      refine ⟨624447332288822614670347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832596443051763486227129 624447332288822614670347)
      ·
        refine ⟨936670998433233922005521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624447332288822614670347 936670998433233922005521)
        ·
          refine ⟨702503248824925441504141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936670998433233922005521 702503248824925441504141)
          ·
            refine ⟨263438718309347040564053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 702503248824925441504141 263438718309347040564053)
            ·
              refine ⟨1543586240093830315805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 263438718309347040564053 1543586240093830315805)
              ·
                rfl

theorem cell21_60874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 9].length) (baseStart_60874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60874 prefixEnd_60874 := by exact prefixLift 60874
  have htrace : WordTrace (prefixWord ++ tailWord_60874) baseStart_60874 baseEnd_60874 := by
    simpa [prefixWord, tailWord_60874, baseEnd_60874] using wordTrace_append hprefix tailTrace_60874
  have hstable : (prefixWord ++ tailWord_60874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60874).length < 2 ^ (prefixWord ++ tailWord_60874).sum := by decide
  have hdescent : baseEnd_60874 < baseStart_60874 := by decide
  rcases family_descends (prefixWord ++ tailWord_60874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60919 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_60919 : Nat := 118140960795 + 60919 * 2 ^ 59
def prefixEnd_60919 : Nat := 4983230072969 + 3 ^ 40 * 60919 * 2
def baseEnd_60919 : Nat := 13902545773934394592153

theorem tailTrace_60919 : CollatzResearch.WordTrace tailWord_60919 prefixEnd_60919 13902545773934394592153 := by
  unfold tailWord_60919
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221898466308341981993811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1481265644205561321329207 2221898466308341981993811)
  ·
    refine ⟨3332847699462512972990717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221898466308341981993811 3332847699462512972990717)
    ·
      refine ⟨1249817887298442364871519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3332847699462512972990717 1249817887298442364871519)
      ·
        refine ⟨1874726830947663547307279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249817887298442364871519 1874726830947663547307279)
        ·
          refine ⟨2812090246421495320960919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874726830947663547307279 2812090246421495320960919)
          ·
            refine ⟨4218135369632242981441379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2812090246421495320960919 4218135369632242981441379)
            ·
              refine ⟨6327203054448364472162069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4218135369632242981441379 6327203054448364472162069)
              ·
                refine ⟨296587643177267084632597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6327203054448364472162069 296587643177267084632597)
                ·
                  refine ⟨13902545773934394592153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 296587643177267084632597 13902545773934394592153)
                  ·
                    rfl

theorem cell21_60919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_60919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60919 prefixEnd_60919 := by exact prefixLift 60919
  have htrace : WordTrace (prefixWord ++ tailWord_60919) baseStart_60919 baseEnd_60919 := by
    simpa [prefixWord, tailWord_60919, baseEnd_60919] using wordTrace_append hprefix tailTrace_60919
  have hstable : (prefixWord ++ tailWord_60919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60919).length < 2 ^ (prefixWord ++ tailWord_60919).sum := by decide
  have hdescent : baseEnd_60919 < baseStart_60919 := by decide
  rcases family_descends (prefixWord ++ tailWord_60919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60922 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_60922 : Nat := 118140960795 + 60922 * 2 ^ 59
def prefixEnd_60922 : Nat := 4983230072969 + 3 ^ 40 * 60922 * 2
def baseEnd_60922 : Nat := 13903230414807056042147

theorem tailTrace_60922 : CollatzResearch.WordTrace tailWord_60922 prefixEnd_60922 13903230414807056042147 := by
  unfold tailWord_60922
  simp only [CollatzResearch.WordTrace]
  refine ⟨555501971324368373588255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1481338590198315662902013 555501971324368373588255)
  ·
    refine ⟨833252956986552560382383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 555501971324368373588255 833252956986552560382383)
    ·
      refine ⟨1249879435479828840573575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833252956986552560382383 1249879435479828840573575)
      ·
        refine ⟨1874819153219743260860363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249879435479828840573575 1874819153219743260860363)
        ·
          refine ⟨2812228729829614891290545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1874819153219743260860363 2812228729829614891290545)
          ·
            refine ⟨2109171547372211168467909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2812228729829614891290545 2109171547372211168467909)
            ·
              refine ⟨395469665132289594087733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2109171547372211168467909 395469665132289594087733)
              ·
                refine ⟨37075281106152149445725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395469665132289594087733 37075281106152149445725)
                ·
                  refine ⟨13903230414807056042147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37075281106152149445725 13903230414807056042147)
                  ·
                    rfl

theorem cell21_60922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_60922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60922 prefixEnd_60922 := by exact prefixLift 60922
  have htrace : WordTrace (prefixWord ++ tailWord_60922) baseStart_60922 baseEnd_60922 := by
    simpa [prefixWord, tailWord_60922, baseEnd_60922] using wordTrace_append hprefix tailTrace_60922
  have hstable : (prefixWord ++ tailWord_60922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60922).length < 2 ^ (prefixWord ++ tailWord_60922).sum := by decide
  have hdescent : baseEnd_60922 < baseStart_60922 := by decide
  rcases family_descends (prefixWord ++ tailWord_60922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60936 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 4]
def baseStart_60936 : Nat := 118140960795 + 60936 * 2 ^ 59
def prefixEnd_60936 : Nat := 4983230072969 + 3 ^ 40 * 60936 * 2
def baseEnd_60936 : Nat := 13906425405546142808785

theorem tailTrace_60936 : CollatzResearch.WordTrace tailWord_60936 prefixEnd_60936 13906425405546142808785 := by
  unfold tailWord_60936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111259253623376942681331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1481679004831169256908441 1111259253623376942681331)
  ·
    refine ⟨1666888880435065414021997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111259253623376942681331 1666888880435065414021997)
    ·
      refine ⟨625083330163149530258249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1666888880435065414021997 625083330163149530258249)
      ·
        refine ⟨468812497622362147693687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625083330163149530258249 468812497622362147693687)
        ·
          refine ⟨703218746433543221540531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468812497622362147693687 703218746433543221540531)
          ·
            refine ⟨1054828119650314832310797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703218746433543221540531 1054828119650314832310797)
            ·
              refine ⟨395560544868868062116549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054828119650314832310797 395560544868868062116549)
              ·
                refine ⟨74167602162912761646853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395560544868868062116549 74167602162912761646853)
                ·
                  refine ⟨13906425405546142808785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74167602162912761646853 13906425405546142808785)
                  ·
                    rfl

theorem cell21_60936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_60936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60936 prefixEnd_60936 := by exact prefixLift 60936
  have htrace : WordTrace (prefixWord ++ tailWord_60936) baseStart_60936 baseEnd_60936 := by
    simpa [prefixWord, tailWord_60936, baseEnd_60936] using wordTrace_append hprefix tailTrace_60936
  have hstable : (prefixWord ++ tailWord_60936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60936).length < 2 ^ (prefixWord ++ tailWord_60936).sum := by decide
  have hdescent : baseEnd_60936 < baseStart_60936 := by decide
  rcases family_descends (prefixWord ++ tailWord_60936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60939 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 3]
def baseStart_60939 : Nat := 118140960795 + 60939 * 2 ^ 59
def prefixEnd_60939 : Nat := 4983230072969 + 3 ^ 40 * 60939 * 2
def baseEnd_60939 : Nat := 13907110046418804258779

theorem tailTrace_60939 : CollatzResearch.WordTrace tailWord_60939 prefixEnd_60939 13907110046418804258779 := by
  unfold tailWord_60939
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222627926235885397721871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1481751950823923598481247 2222627926235885397721871)
  ·
    refine ⟨3333941889353828096582807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2222627926235885397721871 3333941889353828096582807)
    ·
      refine ⟨5000912834030742144874211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3333941889353828096582807 5000912834030742144874211)
      ·
        refine ⟨7501369251046113217311317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5000912834030742144874211 7501369251046113217311317)
        ·
          refine ⟨87906670910696639265367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 7501369251046113217311317 87906670910696639265367)
          ·
            refine ⟨131860006366044958898051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87906670910696639265367 131860006366044958898051)
            ·
              refine ⟨197790009549067438347077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131860006366044958898051 197790009549067438347077)
              ·
                refine ⟨37085626790450144690077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197790009549067438347077 37085626790450144690077)
                ·
                  refine ⟨13907110046418804258779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37085626790450144690077 13907110046418804258779)
                  ·
                    rfl

theorem cell21_60939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 3].length) (baseStart_60939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_60939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_60939 prefixEnd_60939 := by exact prefixLift 60939
  have htrace : WordTrace (prefixWord ++ tailWord_60939) baseStart_60939 baseEnd_60939 := by
    simpa [prefixWord, tailWord_60939, baseEnd_60939] using wordTrace_append hprefix tailTrace_60939
  have hstable : (prefixWord ++ tailWord_60939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60939).length < 2 ^ (prefixWord ++ tailWord_60939).sum := by decide
  have hdescent : baseEnd_60939 < baseStart_60939 := by decide
  rcases family_descends (prefixWord ++ tailWord_60939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61032 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_61032 : Nat := 118140960795 + 61032 * 2 ^ 59
def prefixEnd_61032 : Nat := 4983230072969 + 3 ^ 40 * 61032 * 2
def baseEnd_61032 : Nat := 13928333913471309208589

theorem tailTrace_61032 : CollatzResearch.WordTrace tailWord_61032 prefixEnd_61032 13928333913471309208589 := by
  unfold tailWord_61032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113009957449481140428675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1484013276599308187238233 1113009957449481140428675)
  ·
    refine ⟨1669514936174221710643013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113009957449481140428675 1669514936174221710643013)
    ·
      refine ⟨313034050532666570745565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1669514936174221710643013 313034050532666570745565)
      ·
        refine ⟨117387768949749964029587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313034050532666570745565 117387768949749964029587)
        ·
          refine ⟨176081653424624946044381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117387768949749964029587 176081653424624946044381)
          ·
            refine ⟨66030620034234354766643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176081653424624946044381 66030620034234354766643)
            ·
              refine ⟨99045930051351532149965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66030620034234354766643 99045930051351532149965)
              ·
                refine ⟨37142223769256824556237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99045930051351532149965 37142223769256824556237)
                ·
                  refine ⟨13928333913471309208589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37142223769256824556237 13928333913471309208589)
                  ·
                    rfl

theorem cell21_61032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_61032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61032 prefixEnd_61032 := by exact prefixLift 61032
  have htrace : WordTrace (prefixWord ++ tailWord_61032) baseStart_61032 baseEnd_61032 := by
    simpa [prefixWord, tailWord_61032, baseEnd_61032] using wordTrace_append hprefix tailTrace_61032
  have hstable : (prefixWord ++ tailWord_61032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61032).length < 2 ^ (prefixWord ++ tailWord_61032).sum := by decide
  have hdescent : baseEnd_61032 < baseStart_61032 := by decide
  rcases family_descends (prefixWord ++ tailWord_61032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61164 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_61164 : Nat := 118140960795 + 61164 * 2 ^ 59
def prefixEnd_61164 : Nat := 4983230072969 + 3 ^ 40 * 61164 * 2
def baseEnd_61164 : Nat := 13958458111868413008319

theorem tailTrace_61164 : CollatzResearch.WordTrace tailWord_61164 prefixEnd_61164 13958458111868413008319 := by
  unfold tailWord_61164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1115417175210374412331273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1487222900280499216441697 1115417175210374412331273)
  ·
    refine ⟨836562881407780809248455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1115417175210374412331273 836562881407780809248455)
    ·
      refine ⟨1254844322111671213872683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836562881407780809248455 1254844322111671213872683)
      ·
        refine ⟨1882266483167506820809025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1254844322111671213872683 1882266483167506820809025)
        ·
          refine ⟨1411699862375630115606769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882266483167506820809025 1411699862375630115606769)
          ·
            refine ⟨1058774896781722586705077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1411699862375630115606769 1058774896781722586705077)
            ·
              refine ⟨99260146573286492503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1058774896781722586705077 99260146573286492503601)
              ·
                refine ⟨74445109929964869377701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99260146573286492503601 74445109929964869377701)
                ·
                  refine ⟨13958458111868413008319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74445109929964869377701 13958458111868413008319)
                  ·
                    rfl

theorem cell21_61164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_61164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61164 prefixEnd_61164 := by exact prefixLift 61164
  have htrace : WordTrace (prefixWord ++ tailWord_61164) baseStart_61164 baseEnd_61164 := by
    simpa [prefixWord, tailWord_61164, baseEnd_61164] using wordTrace_append hprefix tailTrace_61164
  have hstable : (prefixWord ++ tailWord_61164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61164).length < 2 ^ (prefixWord ++ tailWord_61164).sum := by decide
  have hdescent : baseEnd_61164 < baseStart_61164 := by decide
  rcases family_descends (prefixWord ++ tailWord_61164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61240 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_61240 : Nat := 118140960795 + 61240 * 2 ^ 59
def prefixEnd_61240 : Nat := 4983230072969 + 3 ^ 40 * 61240 * 2
def baseEnd_61240 : Nat := 13975802347309169741497

theorem tailTrace_61240 : CollatzResearch.WordTrace tailWord_61240 prefixEnd_61240 13975802347309169741497 := by
  unfold tailWord_61240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116803149072706902214587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1489070865430275869619449 1116803149072706902214587)
  ·
    refine ⟨1675204723609060353321881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1116803149072706902214587 1675204723609060353321881)
    ·
      refine ⟨1256403542706795264991411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1675204723609060353321881 1256403542706795264991411)
      ·
        refine ⟨1884605314060192897487117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256403542706795264991411 1884605314060192897487117)
        ·
          refine ⟨706726992772572336557669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1884605314060192897487117 706726992772572336557669)
          ·
            refine ⟨132511311144857313104563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 706726992772572336557669 132511311144857313104563)
            ·
              refine ⟨198766966717285969656845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132511311144857313104563 198766966717285969656845)
              ·
                refine ⟨74537612518982238621317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198766966717285969656845 74537612518982238621317)
                ·
                  refine ⟨13975802347309169741497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74537612518982238621317 13975802347309169741497)
                  ·
                    rfl

theorem cell21_61240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_61240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61240 prefixEnd_61240 := by exact prefixLift 61240
  have htrace : WordTrace (prefixWord ++ tailWord_61240) baseStart_61240 baseEnd_61240 := by
    simpa [prefixWord, tailWord_61240, baseEnd_61240] using wordTrace_append hprefix tailTrace_61240
  have hstable : (prefixWord ++ tailWord_61240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61240).length < 2 ^ (prefixWord ++ tailWord_61240).sum := by decide
  have hdescent : baseEnd_61240 < baseStart_61240 := by decide
  rcases family_descends (prefixWord ++ tailWord_61240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61319 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 3]
def baseStart_61319 : Nat := 118140960795 + 61319 * 2 ^ 59
def prefixEnd_61319 : Nat := 4983230072969 + 3 ^ 40 * 61319 * 2
def baseEnd_61319 : Nat := 13993831223622587924669

theorem tailTrace_61319 : CollatzResearch.WordTrace tailWord_61319 prefixEnd_61319 13993831223622587924669 := by
  unfold tailWord_61319
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236487664859210296555011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1490991776572806864370007 2236487664859210296555011)
  ·
    refine ⟨3354731497288815444832517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2236487664859210296555011 3354731497288815444832517)
    ·
      refine ⟨629012155741652895906097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3354731497288815444832517 629012155741652895906097)
      ·
        refine ⟨471759116806239671929573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629012155741652895906097 471759116806239671929573)
        ·
          refine ⟨88454834401169938486795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 471759116806239671929573 88454834401169938486795)
          ·
            refine ⟨132682251601754907730193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88454834401169938486795 132682251601754907730193)
            ·
              refine ⟨99511688701316180797645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132682251601754907730193 99511688701316180797645)
              ·
                refine ⟨37316883262993567799117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99511688701316180797645 37316883262993567799117)
                ·
                  refine ⟨13993831223622587924669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37316883262993567799117 13993831223622587924669)
                  ·
                    rfl

theorem cell21_61319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3].length) (baseStart_61319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61319 prefixEnd_61319 := by exact prefixLift 61319
  have htrace : WordTrace (prefixWord ++ tailWord_61319) baseStart_61319 baseEnd_61319 := by
    simpa [prefixWord, tailWord_61319, baseEnd_61319] using wordTrace_append hprefix tailTrace_61319
  have hstable : (prefixWord ++ tailWord_61319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61319).length < 2 ^ (prefixWord ++ tailWord_61319).sum := by decide
  have hdescent : baseEnd_61319 < baseStart_61319 := by decide
  rcases family_descends (prefixWord ++ tailWord_61319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61361 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_61361 : Nat := 118140960795 + 61361 * 2 ^ 59
def prefixEnd_61361 : Nat := 4983230072969 + 3 ^ 40 * 61361 * 2
def baseEnd_61361 : Nat := 14003416195839848224583

theorem tailTrace_61361 : CollatzResearch.WordTrace tailWord_61361 prefixEnd_61361 14003416195839848224583 := by
  unfold tailWord_61361
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238019530707051469583937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1492013020471367646389291 2238019530707051469583937)
  ·
    refine ⟨1678514648030288602187953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2238019530707051469583937 1678514648030288602187953)
    ·
      refine ⟨1258885986022716451640965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1678514648030288602187953 1258885986022716451640965)
      ·
        refine ⟨236041122379259334682681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1258885986022716451640965 236041122379259334682681)
        ·
          refine ⟨177030841784444501012011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236041122379259334682681 177030841784444501012011)
          ·
            refine ⟨265546262676666751518017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177030841784444501012011 265546262676666751518017)
            ·
              refine ⟨199159697007500063638513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265546262676666751518017 199159697007500063638513)
              ·
                refine ⟨149369772755625047728885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199159697007500063638513 149369772755625047728885)
                ·
                  refine ⟨14003416195839848224583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149369772755625047728885 14003416195839848224583)
                  ·
                    rfl

theorem cell21_61361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_61361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61361 prefixEnd_61361 := by exact prefixLift 61361
  have htrace : WordTrace (prefixWord ++ tailWord_61361) baseStart_61361 baseEnd_61361 := by
    simpa [prefixWord, tailWord_61361, baseEnd_61361] using wordTrace_append hprefix tailTrace_61361
  have hstable : (prefixWord ++ tailWord_61361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61361).length < 2 ^ (prefixWord ++ tailWord_61361).sum := by decide
  have hdescent : baseEnd_61361 < baseStart_61361 := by decide
  rcases family_descends (prefixWord ++ tailWord_61361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61364 : List Nat := [2, 5, 2, 1, 2, 1, 1, 7]
def baseStart_61364 : Nat := 118140960795 + 61364 * 2 ^ 59
def prefixEnd_61364 : Nat := 4983230072969 + 3 ^ 40 * 61364 * 2
def baseEnd_61364 : Nat := 4668033612237503224859

theorem tailTrace_61364 : CollatzResearch.WordTrace tailWord_61364 prefixEnd_61364 4668033612237503224859 := by
  unfold tailWord_61364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119064474848091490971573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1492085966464121987962097 1119064474848091490971573)
  ·
    refine ⟨104912294517008577278585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1119064474848091490971573 104912294517008577278585)
    ·
      refine ⟨78684220887756432958939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104912294517008577278585 78684220887756432958939)
      ·
        refine ⟨118026331331634649438409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78684220887756432958939 118026331331634649438409)
        ·
          refine ⟨88519748498725987078807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118026331331634649438409 88519748498725987078807)
          ·
            refine ⟨132779622748088980618211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88519748498725987078807 132779622748088980618211)
            ·
              refine ⟨199169434122133470927317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132779622748088980618211 199169434122133470927317)
              ·
                refine ⟨4668033612237503224859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199169434122133470927317 4668033612237503224859)
                ·
                  rfl

theorem cell21_61364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_61364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61364 prefixEnd_61364 := by exact prefixLift 61364
  have htrace : WordTrace (prefixWord ++ tailWord_61364) baseStart_61364 baseEnd_61364 := by
    simpa [prefixWord, tailWord_61364, baseEnd_61364] using wordTrace_append hprefix tailTrace_61364
  have hstable : (prefixWord ++ tailWord_61364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61364).length < 2 ^ (prefixWord ++ tailWord_61364).sum := by decide
  have hdescent : baseEnd_61364 < baseStart_61364 := by decide
  rcases family_descends (prefixWord ++ tailWord_61364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61420 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_61420 : Nat := 118140960795 + 61420 * 2 ^ 59
def prefixEnd_61420 : Nat := 4983230072969 + 3 ^ 40 * 61420 * 2
def baseEnd_61420 : Nat := 14016880799668856741129

theorem tailTrace_61420 : CollatzResearch.WordTrace tailWord_61420 prefixEnd_61420 14016880799668856741129 := by
  unfold tailWord_61420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120085718746652272990857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1493447624995536363987809 1120085718746652272990857)
  ·
    refine ⟨840064289059989204743143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1120085718746652272990857 840064289059989204743143)
    ·
      refine ⟨1260096433589983807114715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840064289059989204743143 1260096433589983807114715)
      ·
        refine ⟨1890144650384975710672073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260096433589983807114715 1890144650384975710672073)
        ·
          refine ⟨1417608487788731783004055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1890144650384975710672073 1417608487788731783004055)
          ·
            refine ⟨2126412731683097674506083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417608487788731783004055 2126412731683097674506083)
            ·
              refine ⟨3189619097524646511759125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2126412731683097674506083 3189619097524646511759125)
              ·
                refine ⟨149513395196467805238709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3189619097524646511759125 149513395196467805238709)
                ·
                  refine ⟨14016880799668856741129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149513395196467805238709 14016880799668856741129)
                  ·
                    rfl

theorem cell21_61420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_61420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61420 prefixEnd_61420 := by exact prefixLift 61420
  have htrace : WordTrace (prefixWord ++ tailWord_61420) baseStart_61420 baseEnd_61420 := by
    simpa [prefixWord, tailWord_61420, baseEnd_61420] using wordTrace_append hprefix tailTrace_61420
  have hstable : (prefixWord ++ tailWord_61420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61420).length < 2 ^ (prefixWord ++ tailWord_61420).sum := by decide
  have hdescent : baseEnd_61420 < baseStart_61420 := by decide
  rcases family_descends (prefixWord ++ tailWord_61420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61446 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_61446 : Nat := 118140960795 + 61446 * 2 ^ 59
def prefixEnd_61446 : Nat := 4983230072969 + 3 ^ 40 * 61446 * 2
def baseEnd_61446 : Nat := 14022814353898589307743

theorem tailTrace_61446 : CollatzResearch.WordTrace tailWord_61446 prefixEnd_61446 14022814353898589307743 := by
  unfold tailWord_61446
  simp only [CollatzResearch.WordTrace]
  refine ⟨70034991731222218325881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1494079823599407324285461 70034991731222218325881)
  ·
    refine ⟨52526243798416663744411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70034991731222218325881 52526243798416663744411)
    ·
      refine ⟨78789365697624995616617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52526243798416663744411 78789365697624995616617)
      ·
        refine ⟨59092024273218746712463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78789365697624995616617 59092024273218746712463)
        ·
          refine ⟨88638036409828120068695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59092024273218746712463 88638036409828120068695)
          ·
            refine ⟨132957054614742180103043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88638036409828120068695 132957054614742180103043)
            ·
              refine ⟨199435581922113270154565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132957054614742180103043 199435581922113270154565)
              ·
                refine ⟨37394171610396238153981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199435581922113270154565 37394171610396238153981)
                ·
                  refine ⟨14022814353898589307743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37394171610396238153981 14022814353898589307743)
                  ·
                    rfl

theorem cell21_61446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_61446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61446 prefixEnd_61446 := by exact prefixLift 61446
  have htrace : WordTrace (prefixWord ++ tailWord_61446) baseStart_61446 baseEnd_61446 := by
    simpa [prefixWord, tailWord_61446, baseEnd_61446] using wordTrace_append hprefix tailTrace_61446
  have hstable : (prefixWord ++ tailWord_61446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61446).length < 2 ^ (prefixWord ++ tailWord_61446).sum := by decide
  have hdescent : baseEnd_61446 < baseStart_61446 := by decide
  rcases family_descends (prefixWord ++ tailWord_61446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61454 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_61454 : Nat := 118140960795 + 61454 * 2 ^ 59
def prefixEnd_61454 : Nat := 4983230072969 + 3 ^ 40 * 61454 * 2
def baseEnd_61454 : Nat := 14024640062892353174393

theorem tailTrace_61454 : CollatzResearch.WordTrace tailWord_61454 prefixEnd_61454 14024640062892353174393 := by
  unfold tailWord_61454
  simp only [CollatzResearch.WordTrace]
  refine ⟨280176439921266044089927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1494274346246752235146277 280176439921266044089927)
  ·
    refine ⟨420264659881899066134891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280176439921266044089927 420264659881899066134891)
    ·
      refine ⟨630396989822848599202337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420264659881899066134891 630396989822848599202337)
      ·
        refine ⟨472797742367136449401753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630396989822848599202337 472797742367136449401753)
        ·
          refine ⟨354598306775352337051315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472797742367136449401753 354598306775352337051315)
          ·
            refine ⟨531897460163028505576973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354598306775352337051315 531897460163028505576973)
            ·
              refine ⟨199461547561135689591365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531897460163028505576973 199461547561135689591365)
              ·
                refine ⟨37399040167712941798381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199461547561135689591365 37399040167712941798381)
                ·
                  refine ⟨14024640062892353174393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37399040167712941798381 14024640062892353174393)
                  ·
                    rfl

theorem cell21_61454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_61454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61454 prefixEnd_61454 := by exact prefixLift 61454
  have htrace : WordTrace (prefixWord ++ tailWord_61454) baseStart_61454 baseEnd_61454 := by
    simpa [prefixWord, tailWord_61454, baseEnd_61454] using wordTrace_append hprefix tailTrace_61454
  have hstable : (prefixWord ++ tailWord_61454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61454).length < 2 ^ (prefixWord ++ tailWord_61454).sum := by decide
  have hdescent : baseEnd_61454 < baseStart_61454 := by decide
  rcases family_descends (prefixWord ++ tailWord_61454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61468 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_61468 : Nat := 118140960795 + 61468 * 2 ^ 59
def prefixEnd_61468 : Nat := 4983230072969 + 3 ^ 40 * 61468 * 2
def baseEnd_61468 : Nat := 14027835053631439941031

theorem tailTrace_61468 : CollatzResearch.WordTrace tailWord_61468 prefixEnd_61468 14027835053631439941031 := by
  unfold tailWord_61468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120961070659704371864529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1494614760879605829152705 1120961070659704371864529)
  ·
    refine ⟨840720802994778278898397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1120961070659704371864529 840720802994778278898397)
    ·
      refine ⟨315270301123041854586899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 840720802994778278898397 315270301123041854586899)
      ·
        refine ⟨472905451684562781880349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315270301123041854586899 472905451684562781880349)
        ·
          refine ⟨177339544381711043205131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472905451684562781880349 177339544381711043205131)
          ·
            refine ⟨266009316572566564807697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177339544381711043205131 266009316572566564807697)
            ·
              refine ⟨199506987429424923605773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266009316572566564807697 199506987429424923605773)
              ·
                refine ⟨74815120286034346352165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199506987429424923605773 74815120286034346352165)
                ·
                  refine ⟨14027835053631439941031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74815120286034346352165 14027835053631439941031)
                  ·
                    rfl

theorem cell21_61468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_61468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61468 prefixEnd_61468 := by exact prefixLift 61468
  have htrace : WordTrace (prefixWord ++ tailWord_61468) baseStart_61468 baseEnd_61468 := by
    simpa [prefixWord, tailWord_61468, baseEnd_61468] using wordTrace_append hprefix tailTrace_61468
  have hstable : (prefixWord ++ tailWord_61468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61468).length < 2 ^ (prefixWord ++ tailWord_61468).sum := by decide
  have hdescent : baseEnd_61468 < baseStart_61468 := by decide
  rcases family_descends (prefixWord ++ tailWord_61468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61502 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_61502 : Nat := 118140960795 + 61502 * 2 ^ 59
def prefixEnd_61502 : Nat := 4983230072969 + 3 ^ 40 * 61502 * 2
def baseEnd_61502 : Nat := 14035594316854936374295

theorem tailTrace_61502 : CollatzResearch.WordTrace tailWord_61502 prefixEnd_61502 14035594316854936374295 := by
  unfold tailWord_61502
  simp only [CollatzResearch.WordTrace]
  refine ⟨280395277899529068808345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1495441482130821700311173 280395277899529068808345)
  ·
    refine ⟨210296458424646801606259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280395277899529068808345 210296458424646801606259)
    ·
      refine ⟨315444687636970202409389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210296458424646801606259 315444687636970202409389)
      ·
        refine ⟨118291757863863825903521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315444687636970202409389 118291757863863825903521)
        ·
          refine ⟨88718818397897869427641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118291757863863825903521 88718818397897869427641)
          ·
            refine ⟨66539113798423402070731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88718818397897869427641 66539113798423402070731)
            ·
              refine ⟨99808670697635103106097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66539113798423402070731 99808670697635103106097)
              ·
                refine ⟨74856503023226327329573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99808670697635103106097 74856503023226327329573)
                ·
                  refine ⟨14035594316854936374295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74856503023226327329573 14035594316854936374295)
                  ·
                    rfl

theorem cell21_61502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_61502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61502 prefixEnd_61502 := by exact prefixLift 61502
  have htrace : WordTrace (prefixWord ++ tailWord_61502) baseStart_61502 baseEnd_61502 := by
    simpa [prefixWord, tailWord_61502, baseEnd_61502] using wordTrace_append hprefix tailTrace_61502
  have hstable : (prefixWord ++ tailWord_61502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61502).length < 2 ^ (prefixWord ++ tailWord_61502).sum := by decide
  have hdescent : baseEnd_61502 < baseStart_61502 := by decide
  rcases family_descends (prefixWord ++ tailWord_61502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61513 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 3]
def baseStart_61513 : Nat := 118140960795 + 61513 * 2 ^ 59
def prefixEnd_61513 : Nat := 4983230072969 + 3 ^ 40 * 61513 * 2
def baseEnd_61513 : Nat := 14038104666721361690939

theorem tailTrace_61513 : CollatzResearch.WordTrace tailWord_61513 prefixEnd_61513 14038104666721361690939 := by
  unfold tailWord_61513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2243563426156381429117193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1495708950770920952744795 2243563426156381429117193)
  ·
    refine ⟨1682672569617286071837895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2243563426156381429117193 1682672569617286071837895)
    ·
      refine ⟨2524008854425929107756843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1682672569617286071837895 2524008854425929107756843)
      ·
        refine ⟨3786013281638893661635265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2524008854425929107756843 3786013281638893661635265)
        ·
          refine ⟨2839509961229170246226449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3786013281638893661635265 2839509961229170246226449)
          ·
            refine ⟨2129632470921877684669837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2839509961229170246226449 2129632470921877684669837)
            ·
              refine ⟨798612176595704131751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129632470921877684669837 798612176595704131751189)
              ·
                refine ⟨37434945777923631175837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 798612176595704131751189 37434945777923631175837)
                ·
                  refine ⟨14038104666721361690939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37434945777923631175837 14038104666721361690939)
                  ·
                    rfl

theorem cell21_61513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_61513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61513 prefixEnd_61513 := by exact prefixLift 61513
  have htrace : WordTrace (prefixWord ++ tailWord_61513) baseStart_61513 baseEnd_61513 := by
    simpa [prefixWord, tailWord_61513, baseEnd_61513] using wordTrace_append hprefix tailTrace_61513
  have hstable : (prefixWord ++ tailWord_61513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61513).length < 2 ^ (prefixWord ++ tailWord_61513).sum := by decide
  have hdescent : baseEnd_61513 < baseStart_61513 := by decide
  rcases family_descends (prefixWord ++ tailWord_61513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61527 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_61527 : Nat := 118140960795 + 61527 * 2 ^ 59
def prefixEnd_61527 : Nat := 4983230072969 + 3 ^ 40 * 61527 * 2
def baseEnd_61527 : Nat := 14041299657460448457577

theorem tailTrace_61527 : CollatzResearch.WordTrace tailWord_61527 prefixEnd_61527 14041299657460448457577 := by
  unfold tailWord_61527
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244074048105661820126835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1496049365403774546751223 2244074048105661820126835)
  ·
    refine ⟨3366111072158492730190253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2244074048105661820126835 3366111072158492730190253)
    ·
      refine ⟨1262291652059434773821345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3366111072158492730190253 1262291652059434773821345)
      ·
        refine ⟨946718739044576080366009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1262291652059434773821345 946718739044576080366009)
        ·
          refine ⟨710039054283432060274507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946718739044576080366009 710039054283432060274507)
          ·
            refine ⟨1065058581425148090411761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710039054283432060274507 1065058581425148090411761)
            ·
              refine ⟨798793936068861067808821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065058581425148090411761 798793936068861067808821)
              ·
                refine ⟨74886931506455725107077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 798793936068861067808821 74886931506455725107077)
                ·
                  refine ⟨14041299657460448457577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74886931506455725107077 14041299657460448457577)
                  ·
                    rfl

theorem cell21_61527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_61527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61527 prefixEnd_61527 := by exact prefixLift 61527
  have htrace : WordTrace (prefixWord ++ tailWord_61527) baseStart_61527 baseEnd_61527 := by
    simpa [prefixWord, tailWord_61527, baseEnd_61527] using wordTrace_append hprefix tailTrace_61527
  have hstable : (prefixWord ++ tailWord_61527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61527).length < 2 ^ (prefixWord ++ tailWord_61527).sum := by decide
  have hdescent : baseEnd_61527 < baseStart_61527 := by decide
  rcases family_descends (prefixWord ++ tailWord_61527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61558 : List Nat := [5, 1, 1, 2, 1, 2, 9]
def baseStart_61558 : Nat := 118140960795 + 61558 * 2 ^ 59
def prefixEnd_61558 : Nat := 4983230072969 + 3 ^ 40 * 61558 * 2
def baseEnd_61558 : Nat := 1560930475534587048983

theorem tailTrace_61558 : CollatzResearch.WordTrace tailWord_61558 prefixEnd_61558 1560930475534587048983 := by
  unfold tailWord_61558
  simp only [CollatzResearch.WordTrace]
  refine ⟨140325294437084632156583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1496803140662236076336885 140325294437084632156583)
  ·
    refine ⟨210487941655626948234875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140325294437084632156583 210487941655626948234875)
    ·
      refine ⟨315731912483440422352313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210487941655626948234875 315731912483440422352313)
      ·
        refine ⟨236798934362580316764235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315731912483440422352313 236798934362580316764235)
        ·
          refine ⟨355198401543870475146353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236798934362580316764235 355198401543870475146353)
          ·
            refine ⟨266398801157902856359765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355198401543870475146353 266398801157902856359765)
            ·
              refine ⟨1560930475534587048983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 266398801157902856359765 1560930475534587048983)
              ·
                rfl

theorem cell21_61558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 9].length) (baseStart_61558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61558 prefixEnd_61558 := by exact prefixLift 61558
  have htrace : WordTrace (prefixWord ++ tailWord_61558) baseStart_61558 baseEnd_61558 := by
    simpa [prefixWord, tailWord_61558, baseEnd_61558] using wordTrace_append hprefix tailTrace_61558
  have hstable : (prefixWord ++ tailWord_61558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61558).length < 2 ^ (prefixWord ++ tailWord_61558).sum := by decide
  have hdescent : baseEnd_61558 < baseStart_61558 := by decide
  rcases family_descends (prefixWord ++ tailWord_61558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61617 : List Nat := [1, 2, 2, 5, 11]
def baseStart_61617 : Nat := 118140960795 + 61617 * 2 ^ 59
def prefixEnd_61617 : Nat := 4983230072969 + 3 ^ 40 * 61617 * 2
def baseEnd_61617 : Nat := 173602949180744345153

theorem tailTrace_61617 : CollatzResearch.WordTrace tailWord_61617 prefixEnd_61617 173602949180744345153 := by
  unfold tailWord_61617
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247356617779607190903105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1498237745186404793935403 2247356617779607190903105)
  ·
    refine ⟨1685517463334705393177329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2247356617779607190903105 1685517463334705393177329)
    ·
      refine ⟨1264138097501029044882997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1685517463334705393177329 1264138097501029044882997)
      ·
        refine ⟨118512946640721472957781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1264138097501029044882997 118512946640721472957781)
        ·
          refine ⟨173602949180744345153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 118512946640721472957781 173602949180744345153)
          ·
            rfl

theorem cell21_61617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 11].length) (baseStart_61617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61617 prefixEnd_61617 := by exact prefixLift 61617
  have htrace : WordTrace (prefixWord ++ tailWord_61617) baseStart_61617 baseEnd_61617 := by
    simpa [prefixWord, tailWord_61617, baseEnd_61617] using wordTrace_append hprefix tailTrace_61617
  have hstable : (prefixWord ++ tailWord_61617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61617).length < 2 ^ (prefixWord ++ tailWord_61617).sum := by decide
  have hdescent : baseEnd_61617 < baseStart_61617 := by decide
  rcases family_descends (prefixWord ++ tailWord_61617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61623 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 3]
def baseStart_61623 : Nat := 118140960795 + 61623 * 2 ^ 59
def prefixEnd_61623 : Nat := 4983230072969 + 3 ^ 40 * 61623 * 2
def baseEnd_61623 : Nat := 14063208165385614857381

theorem tailTrace_61623 : CollatzResearch.WordTrace tailWord_61623 prefixEnd_61623 14063208165385614857381 := by
  unfold tailWord_61623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247575455757870215621523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1498383637171913477081015 2247575455757870215621523)
  ·
    refine ⟨3371363183636805323432285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2247575455757870215621523 3371363183636805323432285)
    ·
      refine ⟨1264261193863801996287107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3371363183636805323432285 1264261193863801996287107)
      ·
        refine ⟨1896391790795702994430661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264261193863801996287107 1896391790795702994430661)
        ·
          refine ⟨355573460774194311455749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1896391790795702994430661 355573460774194311455749)
          ·
            refine ⟨66670023895161433397953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355573460774194311455749 66670023895161433397953)
            ·
              refine ⟨50002517921371075048465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66670023895161433397953 50002517921371075048465)
              ·
                refine ⟨37501888441028306286349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50002517921371075048465 37501888441028306286349)
                ·
                  refine ⟨14063208165385614857381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37501888441028306286349 14063208165385614857381)
                  ·
                    rfl

theorem cell21_61623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 3].length) (baseStart_61623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61623 prefixEnd_61623 := by exact prefixLift 61623
  have htrace : WordTrace (prefixWord ++ tailWord_61623) baseStart_61623 baseEnd_61623 := by
    simpa [prefixWord, tailWord_61623, baseEnd_61623] using wordTrace_append hprefix tailTrace_61623
  have hstable : (prefixWord ++ tailWord_61623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61623).length < 2 ^ (prefixWord ++ tailWord_61623).sum := by decide
  have hdescent : baseEnd_61623 < baseStart_61623 := by decide
  rcases family_descends (prefixWord ++ tailWord_61623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61679 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_61679 : Nat := 118140960795 + 61679 * 2 ^ 59
def prefixEnd_61679 : Nat := 4983230072969 + 3 ^ 40 * 61679 * 2
def baseEnd_61679 : Nat := 14075988128341961923933

theorem tailTrace_61679 : CollatzResearch.WordTrace tailWord_61679 prefixEnd_61679 14075988128341961923933 := by
  unfold tailWord_61679
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249617943554991779660091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1499745295703327853106727 2249617943554991779660091)
  ·
    refine ⟨3374426915332487669490137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249617943554991779660091 3374426915332487669490137)
    ·
      refine ⟨2530820186499365752117603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3374426915332487669490137 2530820186499365752117603)
      ·
        refine ⟨3796230279749048628176405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530820186499365752117603 3796230279749048628176405)
        ·
          refine ⟨177948294363236654445769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3796230279749048628176405 177948294363236654445769)
          ·
            refine ⟨133461220772427490834327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177948294363236654445769 133461220772427490834327)
            ·
              refine ⟨200191831158641236251491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133461220772427490834327 200191831158641236251491)
              ·
                refine ⟨300287746737961854377237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200191831158641236251491 300287746737961854377237)
                ·
                  refine ⟨14075988128341961923933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 300287746737961854377237 14075988128341961923933)
                  ·
                    rfl

theorem cell21_61679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_61679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61679 prefixEnd_61679 := by exact prefixLift 61679
  have htrace : WordTrace (prefixWord ++ tailWord_61679) baseStart_61679 baseEnd_61679 := by
    simpa [prefixWord, tailWord_61679, baseEnd_61679] using wordTrace_append hprefix tailTrace_61679
  have hstable : (prefixWord ++ tailWord_61679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61679).length < 2 ^ (prefixWord ++ tailWord_61679).sum := by decide
  have hdescent : baseEnd_61679 < baseStart_61679 := by decide
  rcases family_descends (prefixWord ++ tailWord_61679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61682 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_61682 : Nat := 118140960795 + 61682 * 2 ^ 59
def prefixEnd_61682 : Nat := 4983230072969 + 3 ^ 40 * 61682 * 2
def baseEnd_61682 : Nat := 14076672769214623373927

theorem tailTrace_61682 : CollatzResearch.WordTrace tailWord_61682 prefixEnd_61682 14076672769214623373927 := by
  unfold tailWord_61682
  simp only [CollatzResearch.WordTrace]
  refine ⟨562431840636030823004825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1499818241696082194679533 562431840636030823004825)
  ·
    refine ⟨421823880477023117253619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562431840636030823004825 421823880477023117253619)
    ·
      refine ⟨632735820715534675880429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421823880477023117253619 632735820715534675880429)
      ·
        refine ⟨237275932768325503455161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 632735820715534675880429 237275932768325503455161)
        ·
          refine ⟨177956949576244127591371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237275932768325503455161 177956949576244127591371)
          ·
            refine ⟨266935424364366191387057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177956949576244127591371 266935424364366191387057)
            ·
              refine ⟨200201568273274643540293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266935424364366191387057 200201568273274643540293)
              ·
                refine ⟨37537794051238995663805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200201568273274643540293 37537794051238995663805)
                ·
                  refine ⟨14076672769214623373927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37537794051238995663805 14076672769214623373927)
                  ·
                    rfl

theorem cell21_61682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_61682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61682 prefixEnd_61682 := by exact prefixLift 61682
  have htrace : WordTrace (prefixWord ++ tailWord_61682) baseStart_61682 baseEnd_61682 := by
    simpa [prefixWord, tailWord_61682, baseEnd_61682] using wordTrace_append hprefix tailTrace_61682
  have hstable : (prefixWord ++ tailWord_61682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61682).length < 2 ^ (prefixWord ++ tailWord_61682).sum := by decide
  have hdescent : baseEnd_61682 < baseStart_61682 := by decide
  rcases family_descends (prefixWord ++ tailWord_61682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61792 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 3]
def baseStart_61792 : Nat := 118140960795 + 61792 * 2 ^ 59
def prefixEnd_61792 : Nat := 4983230072969 + 3 ^ 40 * 61792 * 2
def baseEnd_61792 : Nat := 14101776267878876540369

theorem tailTrace_61792 : CollatzResearch.WordTrace tailWord_61792 prefixEnd_61792 14101776267878876540369 := by
  unfold tailWord_61792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126869696072806039261815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1502492928097074719015753 1126869696072806039261815)
  ·
    refine ⟨1690304544109209058892723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1126869696072806039261815 1690304544109209058892723)
    ·
      refine ⟨2535456816163813588339085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1690304544109209058892723 2535456816163813588339085)
      ·
        refine ⟨950796306061430095627157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2535456816163813588339085 950796306061430095627157)
        ·
          refine ⟨44568576846629535732523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 950796306061430095627157 44568576846629535732523)
          ·
            refine ⟨66852865269944303598785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44568576846629535732523 66852865269944303598785)
            ·
              refine ⟨50139648952458227699089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66852865269944303598785 50139648952458227699089)
              ·
                refine ⟨37604736714343670774317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50139648952458227699089 37604736714343670774317)
                ·
                  refine ⟨14101776267878876540369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37604736714343670774317 14101776267878876540369)
                  ·
                    rfl

theorem cell21_61792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 3].length) (baseStart_61792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61792 prefixEnd_61792 := by exact prefixLift 61792
  have htrace : WordTrace (prefixWord ++ tailWord_61792) baseStart_61792 baseEnd_61792 := by
    simpa [prefixWord, tailWord_61792, baseEnd_61792] using wordTrace_append hprefix tailTrace_61792
  have hstable : (prefixWord ++ tailWord_61792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61792).length < 2 ^ (prefixWord ++ tailWord_61792).sum := by decide
  have hdescent : baseEnd_61792 < baseStart_61792 := by decide
  rcases family_descends (prefixWord ++ tailWord_61792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61848 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_61848 : Nat := 118140960795 + 61848 * 2 ^ 59
def prefixEnd_61848 : Nat := 4983230072969 + 3 ^ 40 * 61848 * 2
def baseEnd_61848 : Nat := 14114556230835223606921

theorem tailTrace_61848 : CollatzResearch.WordTrace tailWord_61848 prefixEnd_61848 14114556230835223606921 := by
  unfold tailWord_61848
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127890939971366821281099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1503854586628489095041465 1127890939971366821281099)
  ·
    refine ⟨1691836409957050231921649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127890939971366821281099 1691836409957050231921649)
    ·
      refine ⟨1268877307467787673941237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691836409957050231921649 1268877307467787673941237)
      ·
        refine ⟨118957247575105094431991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1268877307467787673941237 118957247575105094431991)
        ·
          refine ⟨178435871362657641647987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118957247575105094431991 178435871362657641647987)
          ·
            refine ⟨267653807043986462471981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178435871362657641647987 267653807043986462471981)
            ·
              refine ⟨100370177641494923426993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267653807043986462471981 100370177641494923426993)
              ·
                refine ⟨75277633231121192570245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100370177641494923426993 75277633231121192570245)
                ·
                  refine ⟨14114556230835223606921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75277633231121192570245 14114556230835223606921)
                  ·
                    rfl

theorem cell21_61848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_61848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61848 prefixEnd_61848 := by exact prefixLift 61848
  have htrace : WordTrace (prefixWord ++ tailWord_61848) baseStart_61848 baseEnd_61848 := by
    simpa [prefixWord, tailWord_61848, baseEnd_61848] using wordTrace_append hprefix tailTrace_61848
  have hstable : (prefixWord ++ tailWord_61848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61848).length < 2 ^ (prefixWord ++ tailWord_61848).sum := by decide
  have hdescent : baseEnd_61848 < baseStart_61848 := by decide
  rcases family_descends (prefixWord ++ tailWord_61848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61921 : List Nat := [1, 2, 3, 1, 2, 2, 4, 6]
def baseStart_61921 : Nat := 118140960795 + 61921 * 2 ^ 59
def prefixEnd_61921 : Nat := 4983230072969 + 3 ^ 40 * 61921 * 2
def baseEnd_61921 : Nat := 4710405275134439630035

theorem tailTrace_61921 : CollatzResearch.WordTrace tailWord_61921 prefixEnd_61921 4710405275134439630035 := by
  unfold tailWord_61921
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258444408678267109969617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1505629605785511406646411 2258444408678267109969617)
  ·
    refine ⟨1693833306508700332477213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2258444408678267109969617 1693833306508700332477213)
    ·
      refine ⟨635187489940762624678955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1693833306508700332477213 635187489940762624678955)
      ·
        refine ⟨952781234911143937018433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635187489940762624678955 952781234911143937018433)
        ·
          refine ⟨714585926183357952763825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952781234911143937018433 714585926183357952763825)
          ·
            refine ⟨535939444637518464572869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714585926183357952763825 535939444637518464572869)
            ·
              refine ⟨100488645869534712107413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 535939444637518464572869 100488645869534712107413)
              ·
                refine ⟨4710405275134439630035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100488645869534712107413 4710405275134439630035)
                ·
                  rfl

theorem cell21_61921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_61921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61921 prefixEnd_61921 := by exact prefixLift 61921
  have htrace : WordTrace (prefixWord ++ tailWord_61921) baseStart_61921 baseEnd_61921 := by
    simpa [prefixWord, tailWord_61921, baseEnd_61921] using wordTrace_append hprefix tailTrace_61921
  have hstable : (prefixWord ++ tailWord_61921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61921).length < 2 ^ (prefixWord ++ tailWord_61921).sum := by decide
  have hdescent : baseEnd_61921 < baseStart_61921 := by decide
  rcases family_descends (prefixWord ++ tailWord_61921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61935 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_61935 : Nat := 118140960795 + 61935 * 2 ^ 59
def prefixEnd_61935 : Nat := 4983230072969 + 3 ^ 40 * 61935 * 2
def baseEnd_61935 : Nat := 14134410816142405656743

theorem tailTrace_61935 : CollatzResearch.WordTrace tailWord_61935 prefixEnd_61935 14134410816142405656743 := by
  unfold tailWord_61935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258955030627547500979259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1505970020418365000652839 2258955030627547500979259)
  ·
    refine ⟨3388432545941321251468889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2258955030627547500979259 3388432545941321251468889)
    ·
      refine ⟨2541324409455990938601667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3388432545941321251468889 2541324409455990938601667)
      ·
        refine ⟨3811986614183986407902501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541324409455990938601667 3811986614183986407902501)
        ·
          refine ⟨714747490159497451481719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3811986614183986407902501 714747490159497451481719)
          ·
            refine ⟨1072121235239246177222579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714747490159497451481719 1072121235239246177222579)
            ·
              refine ⟨1608181852858869265833869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072121235239246177222579 1608181852858869265833869)
              ·
                refine ⟨603068194822075974687701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608181852858869265833869 603068194822075974687701)
                ·
                  refine ⟨14134410816142405656743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 603068194822075974687701 14134410816142405656743)
                  ·
                    rfl

theorem cell21_61935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_61935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61935 prefixEnd_61935 := by exact prefixLift 61935
  have htrace : WordTrace (prefixWord ++ tailWord_61935) baseStart_61935 baseEnd_61935 := by
    simpa [prefixWord, tailWord_61935, baseEnd_61935] using wordTrace_append hprefix tailTrace_61935
  have hstable : (prefixWord ++ tailWord_61935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61935).length < 2 ^ (prefixWord ++ tailWord_61935).sum := by decide
  have hdescent : baseEnd_61935 < baseStart_61935 := by decide
  rcases family_descends (prefixWord ++ tailWord_61935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61958 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_61958 : Nat := 118140960795 + 61958 * 2 ^ 59
def prefixEnd_61958 : Nat := 4983230072969 + 3 ^ 40 * 61958 * 2
def baseEnd_61958 : Nat := 14139659729499476773363

theorem tailTrace_61958 : CollatzResearch.WordTrace tailWord_61958 prefixEnd_61958 14139659729499476773363 := by
  unfold tailWord_61958
  simp only [CollatzResearch.WordTrace]
  refine ⟨70618559673256950908329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1506529273029481619377685 70618559673256950908329)
  ·
    refine ⟨52963919754942713181247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70618559673256950908329 52963919754942713181247)
    ·
      refine ⟨79445879632414069771871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52963919754942713181247 79445879632414069771871)
      ·
        refine ⟨119168819448621104657807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79445879632414069771871 119168819448621104657807)
        ·
          refine ⟨178753229172931656986711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119168819448621104657807 178753229172931656986711)
          ·
            refine ⟨268129843759397485480067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178753229172931656986711 268129843759397485480067)
            ·
              refine ⟨402194765639096228220101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268129843759397485480067 402194765639096228220101)
              ·
                refine ⟨75411518557330542791269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402194765639096228220101 75411518557330542791269)
                ·
                  refine ⟨14139659729499476773363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75411518557330542791269 14139659729499476773363)
                  ·
                    rfl

theorem cell21_61958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_61958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_61958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_61958 prefixEnd_61958 := by exact prefixLift 61958
  have htrace : WordTrace (prefixWord ++ tailWord_61958) baseStart_61958 baseEnd_61958 := by
    simpa [prefixWord, tailWord_61958, baseEnd_61958] using wordTrace_append hprefix tailTrace_61958
  have hstable : (prefixWord ++ tailWord_61958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61958).length < 2 ^ (prefixWord ++ tailWord_61958).sum := by decide
  have hdescent : baseEnd_61958 < baseStart_61958 := by decide
  rcases family_descends (prefixWord ++ tailWord_61958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62028 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_62028 : Nat := 118140960795 + 62028 * 2 ^ 59
def prefixEnd_62028 : Nat := 4983230072969 + 3 ^ 40 * 62028 * 2
def baseEnd_62028 : Nat := 14155634683194910606553

theorem tailTrace_62028 : CollatzResearch.WordTrace tailWord_62028 prefixEnd_62028 14155634683194910606553 := by
  unfold tailWord_62028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1131173509645312192057369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1508231346193749589409825 1131173509645312192057369)
  ·
    refine ⟨848380132233984144043027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1131173509645312192057369 848380132233984144043027)
    ·
      refine ⟨1272570198350976216064541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848380132233984144043027 1272570198350976216064541)
      ·
        refine ⟨477213824381616081024203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1272570198350976216064541 477213824381616081024203)
        ·
          refine ⟨715820736572424121536305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477213824381616081024203 715820736572424121536305)
          ·
            refine ⟨536865552429318091152229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715820736572424121536305 536865552429318091152229)
            ·
              refine ⟨100662291080497142091043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536865552429318091152229 100662291080497142091043)
              ·
                refine ⟨150993436620745713136565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100662291080497142091043 150993436620745713136565)
                ·
                  refine ⟨14155634683194910606553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150993436620745713136565 14155634683194910606553)
                  ·
                    rfl

theorem cell21_62028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_62028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62028 prefixEnd_62028 := by exact prefixLift 62028
  have htrace : WordTrace (prefixWord ++ tailWord_62028) baseStart_62028 baseEnd_62028 := by
    simpa [prefixWord, tailWord_62028, baseEnd_62028] using wordTrace_append hprefix tailTrace_62028
  have hstable : (prefixWord ++ tailWord_62028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62028).length < 2 ^ (prefixWord ++ tailWord_62028).sum := by decide
  have hdescent : baseEnd_62028 < baseStart_62028 := by decide
  rcases family_descends (prefixWord ++ tailWord_62028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62062 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_62062 : Nat := 118140960795 + 62062 * 2 ^ 59
def prefixEnd_62062 : Nat := 4983230072969 + 3 ^ 40 * 62062 * 2
def baseEnd_62062 : Nat := 14163393946418407039817

theorem tailTrace_62062 : CollatzResearch.WordTrace tailWord_62062 prefixEnd_62062 14163393946418407039817 := by
  unfold tailWord_62062
  simp only [CollatzResearch.WordTrace]
  refine ⟨282948387645931023856555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1509058067444965460568293 282948387645931023856555)
  ·
    refine ⟨424422581468896535784833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282948387645931023856555 424422581468896535784833)
    ·
      refine ⟨318316936101672401838625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424422581468896535784833 318316936101672401838625)
      ·
        refine ⟨238737702076254301378969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318316936101672401838625 238737702076254301378969)
        ·
          refine ⟨179053276557190726034227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238737702076254301378969 179053276557190726034227)
          ·
            refine ⟨268579914835786089051341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179053276557190726034227 268579914835786089051341)
            ·
              refine ⟨100717468063419783394253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268579914835786089051341 100717468063419783394253)
              ·
                refine ⟨37769050523782418772845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100717468063419783394253 37769050523782418772845)
                ·
                  refine ⟨14163393946418407039817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37769050523782418772845 14163393946418407039817)
                  ·
                    rfl

theorem cell21_62062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_62062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62062 prefixEnd_62062 := by exact prefixLift 62062
  have htrace : WordTrace (prefixWord ++ tailWord_62062) baseStart_62062 baseEnd_62062 := by
    simpa [prefixWord, tailWord_62062, baseEnd_62062] using wordTrace_append hprefix tailTrace_62062
  have hstable : (prefixWord ++ tailWord_62062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62062).length < 2 ^ (prefixWord ++ tailWord_62062).sum := by decide
  have hdescent : baseEnd_62062 < baseStart_62062 := by decide
  rcases family_descends (prefixWord ++ tailWord_62062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62073 : List Nat := [1, 2, 1, 3, 3, 4, 7]
def baseStart_62073 : Nat := 118140960795 + 62073 * 2 ^ 59
def prefixEnd_62073 : Nat := 4983230072969 + 3 ^ 40 * 62073 * 2
def baseEnd_62073 : Nat := 1573989366253870261829

theorem tailTrace_62073 : CollatzResearch.WordTrace tailWord_62073 prefixEnd_62073 1573989366253870261829 := by
  unfold tailWord_62073
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263988304127597069502873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1509325536085064713001915 2263988304127597069502873)
  ·
    refine ⟨1697991228095697802127155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2263988304127597069502873 1697991228095697802127155)
    ·
      refine ⟨2546986842143546703190733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697991228095697802127155 2546986842143546703190733)
      ·
        refine ⟨955120065803830013696525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2546986842143546703190733 955120065803830013696525)
        ·
          refine ⟨358170024676436255136197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 955120065803830013696525 358170024676436255136197)
          ·
            refine ⟨67156879626831797838037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358170024676436255136197 67156879626831797838037)
            ·
              refine ⟨1573989366253870261829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67156879626831797838037 1573989366253870261829)
              ·
                rfl

theorem cell21_62073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 7].length) (baseStart_62073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62073 prefixEnd_62073 := by exact prefixLift 62073
  have htrace : WordTrace (prefixWord ++ tailWord_62073) baseStart_62073 baseEnd_62073 := by
    simpa [prefixWord, tailWord_62073, baseEnd_62073] using wordTrace_append hprefix tailTrace_62073
  have hstable : (prefixWord ++ tailWord_62073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62073).length < 2 ^ (prefixWord ++ tailWord_62073).sum := by decide
  have hdescent : baseEnd_62073 < baseStart_62073 := by decide
  rcases family_descends (prefixWord ++ tailWord_62073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62090 : List Nat := [3, 1, 2, 3, 3, 1, 2, 6]
def baseStart_62090 : Nat := 118140960795 + 62090 * 2 ^ 59
def prefixEnd_62090 : Nat := 4983230072969 + 3 ^ 40 * 62090 * 2
def baseEnd_62090 : Nat := 4723261309298860191031

theorem tailTrace_62090 : CollatzResearch.WordTrace tailWord_62090 prefixEnd_62090 4723261309298860191031 := by
  unfold tailWord_62090
  simp only [CollatzResearch.WordTrace]
  refine ⟨566152086266502243217931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1509738896710672648581149 566152086266502243217931)
  ·
    refine ⟨849228129399753364826897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566152086266502243217931 849228129399753364826897)
    ·
      refine ⟨636921097049815023620173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 849228129399753364826897 636921097049815023620173)
      ·
        refine ⟨238845411393680633857565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636921097049815023620173 238845411393680633857565)
        ·
          refine ⟨89567029272630237696587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238845411393680633857565 89567029272630237696587)
          ·
            refine ⟨134350543908945356544881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89567029272630237696587 134350543908945356544881)
            ·
              refine ⟨100762907931709017408661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134350543908945356544881 100762907931709017408661)
              ·
                refine ⟨4723261309298860191031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100762907931709017408661 4723261309298860191031)
                ·
                  rfl

theorem cell21_62090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_62090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62090 prefixEnd_62090 := by exact prefixLift 62090
  have htrace : WordTrace (prefixWord ++ tailWord_62090) baseStart_62090 baseEnd_62090 := by
    simpa [prefixWord, tailWord_62090, baseEnd_62090] using wordTrace_append hprefix tailTrace_62090
  have hstable : (prefixWord ++ tailWord_62090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62090).length < 2 ^ (prefixWord ++ tailWord_62090).sum := by decide
  have hdescent : baseEnd_62090 < baseStart_62090 := by decide
  rcases family_descends (prefixWord ++ tailWord_62090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62225 : List Nat := [1, 2, 2, 1, 1, 3, 6, 5]
def baseStart_62225 : Nat := 118140960795 + 62225 * 2 ^ 59
def prefixEnd_62225 : Nat := 4983230072969 + 3 ^ 40 * 62225 * 2
def baseEnd_62225 : Nat := 4733530922388781940939

theorem tailTrace_62225 : CollatzResearch.WordTrace tailWord_62225 prefixEnd_62225 4733530922388781940939 := by
  unfold tailWord_62225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269532199576927029036129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1513021466384618019357419 2269532199576927029036129)
  ·
    refine ⟨1702149149682695271777097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2269532199576927029036129 1702149149682695271777097)
    ·
      refine ⟨1276611862262021453832823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1702149149682695271777097 1276611862262021453832823)
      ·
        refine ⟨1914917793393032180749235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276611862262021453832823 1914917793393032180749235)
        ·
          refine ⟨2872376690089548271123853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914917793393032180749235 2872376690089548271123853)
          ·
            refine ⟨1077141258783580601671445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2872376690089548271123853 1077141258783580601671445)
            ·
              refine ⟨50490996505480340703349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1077141258783580601671445 50490996505480340703349)
              ·
                refine ⟨4733530922388781940939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50490996505480340703349 4733530922388781940939)
                ·
                  rfl

theorem cell21_62225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 5].length) (baseStart_62225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62225 prefixEnd_62225 := by exact prefixLift 62225
  have htrace : WordTrace (prefixWord ++ tailWord_62225) baseStart_62225 baseEnd_62225 := by
    simpa [prefixWord, tailWord_62225, baseEnd_62225] using wordTrace_append hprefix tailTrace_62225
  have hstable : (prefixWord ++ tailWord_62225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62225).length < 2 ^ (prefixWord ++ tailWord_62225).sum := by decide
  have hdescent : baseEnd_62225 < baseStart_62225 := by decide
  rcases family_descends (prefixWord ++ tailWord_62225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62231 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 3]
def baseStart_62231 : Nat := 118140960795 + 62231 * 2 ^ 59
def prefixEnd_62231 : Nat := 4983230072969 + 3 ^ 40 * 62231 * 2
def baseEnd_62231 : Nat := 14201962048911668722805

theorem tailTrace_62231 : CollatzResearch.WordTrace tailWord_62231 prefixEnd_62231 14201962048911668722805 := by
  unfold tailWord_62231
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269751037555190053754547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1513167358370126702503031 2269751037555190053754547)
  ·
    refine ⟨3404626556332785080631821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2269751037555190053754547 3404626556332785080631821)
    ·
      refine ⟨1276734958624794405236933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3404626556332785080631821 1276734958624794405236933)
      ·
        refine ⟨239387804742148950981925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1276734958624794405236933 239387804742148950981925)
        ·
          refine ⟨44885213389152928309111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239387804742148950981925 44885213389152928309111)
          ·
            refine ⟨67327820083729392463667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44885213389152928309111 67327820083729392463667)
            ·
              refine ⟨100991730125594088695501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67327820083729392463667 100991730125594088695501)
              ·
                refine ⟨37871898797097783260813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100991730125594088695501 37871898797097783260813)
                ·
                  refine ⟨14201962048911668722805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37871898797097783260813 14201962048911668722805)
                  ·
                    rfl

theorem cell21_62231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3].length) (baseStart_62231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62231 prefixEnd_62231 := by exact prefixLift 62231
  have htrace : WordTrace (prefixWord ++ tailWord_62231) baseStart_62231 baseEnd_62231 := by
    simpa [prefixWord, tailWord_62231, baseEnd_62231] using wordTrace_append hprefix tailTrace_62231
  have hstable : (prefixWord ++ tailWord_62231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62231).length < 2 ^ (prefixWord ++ tailWord_62231).sum := by decide
  have hdescent : baseEnd_62231 < baseStart_62231 := by decide
  rcases family_descends (prefixWord ++ tailWord_62231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62256 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_62256 : Nat := 118140960795 + 62256 * 2 ^ 59
def prefixEnd_62256 : Nat := 4983230072969 + 3 ^ 40 * 62256 * 2
def baseEnd_62256 : Nat := 14207667389517180806087

theorem tailTrace_62256 : CollatzResearch.WordTrace tailWord_62256 prefixEnd_62256 14207667389517180806087 := by
  unfold tailWord_62256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135331431232309661707311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1513775241643079548943081 1135331431232309661707311)
  ·
    refine ⟨1702997146848464492560967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135331431232309661707311 1702997146848464492560967)
    ·
      refine ⟨2554495720272696738841451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702997146848464492560967 2554495720272696738841451)
      ·
        refine ⟨3831743580409045108262177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2554495720272696738841451 3831743580409045108262177)
        ·
          refine ⟨2873807685306783831196633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3831743580409045108262177 2873807685306783831196633)
          ·
            refine ⟨2155355763980087873397475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2873807685306783831196633 2155355763980087873397475)
            ·
              refine ⟨3233033645970131810096213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155355763980087873397475 3233033645970131810096213)
              ·
                refine ⟨37887113038712482149565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3233033645970131810096213 37887113038712482149565)
                ·
                  refine ⟨14207667389517180806087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37887113038712482149565 14207667389517180806087)
                  ·
                    rfl

theorem cell21_62256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_62256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62256 prefixEnd_62256 := by exact prefixLift 62256
  have htrace : WordTrace (prefixWord ++ tailWord_62256) baseStart_62256 baseEnd_62256 := by
    simpa [prefixWord, tailWord_62256, baseEnd_62256] using wordTrace_append hprefix tailTrace_62256
  have hstable : (prefixWord ++ tailWord_62256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62256).length < 2 ^ (prefixWord ++ tailWord_62256).sum := by decide
  have hdescent : baseEnd_62256 < baseStart_62256 := by decide
  rcases family_descends (prefixWord ++ tailWord_62256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62262 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_62262 : Nat := 118140960795 + 62262 * 2 ^ 59
def prefixEnd_62262 : Nat := 4983230072969 + 3 ^ 40 * 62262 * 2
def baseEnd_62262 : Nat := 14209036671262503706075

theorem tailTrace_62262 : CollatzResearch.WordTrace tailWord_62262 prefixEnd_62262 14209036671262503706075 := by
  unfold tailWord_62262
  simp only [CollatzResearch.WordTrace]
  refine ⟨141930106277680146758315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1513921133628588232088693 141930106277680146758315)
  ·
    refine ⟨212895159416520220137473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141930106277680146758315 212895159416520220137473)
    ·
      refine ⟨159671369562390165103105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212895159416520220137473 159671369562390165103105)
      ·
        refine ⟨119753527171792623827329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159671369562390165103105 119753527171792623827329)
        ·
          refine ⟨89815145378844467870497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119753527171792623827329 89815145378844467870497)
          ·
            refine ⟨67361359034133350902873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89815145378844467870497 67361359034133350902873)
            ·
              refine ⟨50521019275600013177155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67361359034133350902873 50521019275600013177155)
              ·
                refine ⟨75781528913400019765733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50521019275600013177155 75781528913400019765733)
                ·
                  refine ⟨14209036671262503706075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75781528913400019765733 14209036671262503706075)
                  ·
                    rfl

theorem cell21_62262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_62262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62262 prefixEnd_62262 := by exact prefixLift 62262
  have htrace : WordTrace (prefixWord ++ tailWord_62262) baseStart_62262 baseEnd_62262 := by
    simpa [prefixWord, tailWord_62262, baseEnd_62262] using wordTrace_append hprefix tailTrace_62262
  have hstable : (prefixWord ++ tailWord_62262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62262).length < 2 ^ (prefixWord ++ tailWord_62262).sum := by decide
  have hdescent : baseEnd_62262 < baseStart_62262 := by decide
  rcases family_descends (prefixWord ++ tailWord_62262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62391 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_62391 : Nat := 118140960795 + 62391 * 2 ^ 59
def prefixEnd_62391 : Nat := 4983230072969 + 3 ^ 40 * 62391 * 2
def baseEnd_62391 : Nat := 14238476228786946055811

theorem tailTrace_62391 : CollatzResearch.WordTrace tailWord_62391 prefixEnd_62391 14238476228786946055811 := by
  unfold tailWord_62391
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275586716975537379579027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1517057811317024919719351 2275586716975537379579027)
  ·
    refine ⟨3413380075463306069368541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2275586716975537379579027 3413380075463306069368541)
    ·
      refine ⟨1280017528298739776013203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3413380075463306069368541 1280017528298739776013203)
      ·
        refine ⟨1920026292448109664019805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1280017528298739776013203 1920026292448109664019805)
        ·
          refine ⟨720009859668041124007427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1920026292448109664019805 720009859668041124007427)
          ·
            refine ⟨1080014789502061686011141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720009859668041124007427 1080014789502061686011141)
            ·
              refine ⟨202502773031636566127089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1080014789502061686011141 202502773031636566127089)
              ·
                refine ⟨151877079773727424595317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202502773031636566127089 151877079773727424595317)
                ·
                  refine ⟨14238476228786946055811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151877079773727424595317 14238476228786946055811)
                  ·
                    rfl

theorem cell21_62391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_62391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62391 prefixEnd_62391 := by exact prefixLift 62391
  have htrace : WordTrace (prefixWord ++ tailWord_62391) baseStart_62391 baseEnd_62391 := by
    simpa [prefixWord, tailWord_62391, baseEnd_62391] using wordTrace_append hprefix tailTrace_62391
  have hstable : (prefixWord ++ tailWord_62391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62391).length < 2 ^ (prefixWord ++ tailWord_62391).sum := by decide
  have hdescent : baseEnd_62391 < baseStart_62391 := by decide
  rcases family_descends (prefixWord ++ tailWord_62391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62439 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_62439 : Nat := 118140960795 + 62439 * 2 ^ 59
def prefixEnd_62439 : Nat := 4983230072969 + 3 ^ 40 * 62439 * 2
def baseEnd_62439 : Nat := 14249430482749529255713

theorem tailTrace_62439 : CollatzResearch.WordTrace tailWord_62439 prefixEnd_62439 14249430482749529255713 := by
  unfold tailWord_62439
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277337420801641577326371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1518224947201094384884247 2277337420801641577326371)
  ·
    refine ⟨3416006131202462365989557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2277337420801641577326371 3416006131202462365989557)
    ·
      refine ⟨320250574800230846811521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3416006131202462365989557 320250574800230846811521)
      ·
        refine ⟨240187931100173135108641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320250574800230846811521 240187931100173135108641)
        ·
          refine ⟨180140948325129851331481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240187931100173135108641 180140948325129851331481)
          ·
            refine ⟨135105711243847388498611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180140948325129851331481 135105711243847388498611)
            ·
              refine ⟨202658566865771082747917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135105711243847388498611 202658566865771082747917)
              ·
                refine ⟨75996962574664156030469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202658566865771082747917 75996962574664156030469)
                ·
                  refine ⟨14249430482749529255713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75996962574664156030469 14249430482749529255713)
                  ·
                    rfl

theorem cell21_62439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_62439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62439 prefixEnd_62439 := by exact prefixLift 62439
  have htrace : WordTrace (prefixWord ++ tailWord_62439) baseStart_62439 baseEnd_62439 := by
    simpa [prefixWord, tailWord_62439, baseEnd_62439] using wordTrace_append hprefix tailTrace_62439
  have hstable : (prefixWord ++ tailWord_62439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62439).length < 2 ^ (prefixWord ++ tailWord_62439).sum := by decide
  have hdescent : baseEnd_62439 < baseStart_62439 := by decide
  rcases family_descends (prefixWord ++ tailWord_62439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62470 : List Nat := [6, 2, 1, 12]
def baseStart_62470 : Nat := 118140960795 + 62470 * 2 ^ 59
def prefixEnd_62470 : Nat := 4983230072969 + 3 ^ 40 * 62470 * 2
def baseEnd_62470 : Nat := 58668745288478865181

theorem tailTrace_62470 : CollatzResearch.WordTrace tailWord_62470 prefixEnd_62470 58668745288478865181 := by
  unfold tailWord_62470
  simp only [CollatzResearch.WordTrace]
  refine ⟨71202127615291683490777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1518978722459555914469909 71202127615291683490777)
  ·
    refine ⟨53401595711468762618083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71202127615291683490777 53401595711468762618083)
    ·
      refine ⟨80102393567203143927125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53401595711468762618083 80102393567203143927125)
      ·
        refine ⟨58668745288478865181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 80102393567203143927125 58668745288478865181)
        ·
          rfl

theorem cell21_62470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 12].length) (baseStart_62470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62470 prefixEnd_62470 := by exact prefixLift 62470
  have htrace : WordTrace (prefixWord ++ tailWord_62470) baseStart_62470 baseEnd_62470 := by
    simpa [prefixWord, tailWord_62470, baseEnd_62470] using wordTrace_append hprefix tailTrace_62470
  have hstable : (prefixWord ++ tailWord_62470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62470).length < 2 ^ (prefixWord ++ tailWord_62470).sum := by decide
  have hdescent : baseEnd_62470 < baseStart_62470 := by decide
  rcases family_descends (prefixWord ++ tailWord_62470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62481 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_62481 : Nat := 118140960795 + 62481 * 2 ^ 59
def prefixEnd_62481 : Nat := 4983230072969 + 3 ^ 40 * 62481 * 2
def baseEnd_62481 : Nat := 14259015454966789555627

theorem tailTrace_62481 : CollatzResearch.WordTrace tailWord_62481 prefixEnd_62481 14259015454966789555627 := by
  unfold tailWord_62481
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278869286649482750355297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1519246191099655166903531 2278869286649482750355297)
  ·
    refine ⟨1709151964987112062766473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2278869286649482750355297 1709151964987112062766473)
    ·
      refine ⟨1281863973740334047074855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1709151964987112062766473 1281863973740334047074855)
      ·
        refine ⟨1922795960610501070612283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281863973740334047074855 1922795960610501070612283)
        ·
          refine ⟨2884193940915751605918425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922795960610501070612283 2884193940915751605918425)
          ·
            refine ⟨2163145455686813704438819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884193940915751605918425 2163145455686813704438819)
            ·
              refine ⟨3244718183530220556658229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163145455686813704438819 3244718183530220556658229)
              ·
                refine ⟨304192329705958177186709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3244718183530220556658229 304192329705958177186709)
                ·
                  refine ⟨14259015454966789555627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304192329705958177186709 14259015454966789555627)
                  ·
                    rfl

theorem cell21_62481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_62481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62481 prefixEnd_62481 := by exact prefixLift 62481
  have htrace : WordTrace (prefixWord ++ tailWord_62481) baseStart_62481 baseEnd_62481 := by
    simpa [prefixWord, tailWord_62481, baseEnd_62481] using wordTrace_append hprefix tailTrace_62481
  have hstable : (prefixWord ++ tailWord_62481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62481).length < 2 ^ (prefixWord ++ tailWord_62481).sum := by decide
  have hdescent : baseEnd_62481 < baseStart_62481 := by decide
  rcases family_descends (prefixWord ++ tailWord_62481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62518 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_62518 : Nat := 118140960795 + 62518 * 2 ^ 59
def prefixEnd_62518 : Nat := 4983230072969 + 3 ^ 40 * 62518 * 2
def baseEnd_62518 : Nat := 14267459359062947438885

theorem tailTrace_62518 : CollatzResearch.WordTrace tailWord_62518 prefixEnd_62518 14267459359062947438885 := by
  unfold tailWord_62518
  simp only [CollatzResearch.WordTrace]
  refine ⟨142513674219714879340763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1520145858343625379634805 142513674219714879340763)
  ·
    refine ⟨213770511329572319011145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142513674219714879340763 213770511329572319011145)
    ·
      refine ⟨160327883497179239258359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213770511329572319011145 160327883497179239258359)
      ·
        refine ⟨240491825245768858887539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160327883497179239258359 240491825245768858887539)
        ·
          refine ⟨360737737868653288331309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240491825245768858887539 360737737868653288331309)
          ·
            refine ⟨135276651700744983124241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360737737868653288331309 135276651700744983124241)
            ·
              refine ⟨101457488775558737343181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135276651700744983124241 101457488775558737343181)
              ·
                refine ⟨38046558290834526503693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101457488775558737343181 38046558290834526503693)
                ·
                  refine ⟨14267459359062947438885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38046558290834526503693 14267459359062947438885)
                  ·
                    rfl

theorem cell21_62518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_62518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62518 prefixEnd_62518 := by exact prefixLift 62518
  have htrace : WordTrace (prefixWord ++ tailWord_62518) baseStart_62518 baseEnd_62518 := by
    simpa [prefixWord, tailWord_62518, baseEnd_62518] using wordTrace_append hprefix tailTrace_62518
  have hstable : (prefixWord ++ tailWord_62518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62518).length < 2 ^ (prefixWord ++ tailWord_62518).sum := by decide
  have hdescent : baseEnd_62518 < baseStart_62518 := by decide
  rcases family_descends (prefixWord ++ tailWord_62518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62529 : List Nat := [1, 2, 5, 1, 3, 1, 8]
def baseStart_62529 : Nat := 118140960795 + 62529 * 2 ^ 59
def prefixEnd_62529 : Nat := 4983230072969 + 3 ^ 40 * 62529 * 2
def baseEnd_62529 : Nat := 1585552189881041417281

theorem tailTrace_62529 : CollatzResearch.WordTrace tailWord_62529 prefixEnd_62529 1585552189881041417281 := by
  unfold tailWord_62529
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280619990475586948102641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1520413326983724632068427 2280619990475586948102641)
  ·
    refine ⟨1710464992856690211076981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2280619990475586948102641 1710464992856690211076981)
    ·
      refine ⟨160356093080314707288467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1710464992856690211076981 160356093080314707288467)
      ·
        refine ⟨240534139620472060932701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160356093080314707288467 240534139620472060932701)
        ·
          refine ⟨90200302357677022849763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240534139620472060932701 90200302357677022849763)
          ·
            refine ⟨135300453536515534274645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90200302357677022849763 135300453536515534274645)
            ·
              refine ⟨1585552189881041417281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 135300453536515534274645 1585552189881041417281)
              ·
                rfl

theorem cell21_62529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 8].length) (baseStart_62529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62529 prefixEnd_62529 := by exact prefixLift 62529
  have htrace : WordTrace (prefixWord ++ tailWord_62529) baseStart_62529 baseEnd_62529 := by
    simpa [prefixWord, tailWord_62529, baseEnd_62529] using wordTrace_append hprefix tailTrace_62529
  have hstable : (prefixWord ++ tailWord_62529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62529).length < 2 ^ (prefixWord ++ tailWord_62529).sum := by decide
  have hdescent : baseEnd_62529 < baseStart_62529 := by decide
  rcases family_descends (prefixWord ++ tailWord_62529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62574 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_62574 : Nat := 118140960795 + 62574 * 2 ^ 59
def prefixEnd_62574 : Nat := 4983230072969 + 3 ^ 40 * 62574 * 2
def baseEnd_62574 : Nat := 14280239322019294505437

theorem tailTrace_62574 : CollatzResearch.WordTrace tailWord_62574 prefixEnd_62574 14280239322019294505437 := by
  unfold tailWord_62574
  simp only [CollatzResearch.WordTrace]
  refine ⟨285282659414069954186347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1521507516875039755660517 285282659414069954186347)
  ·
    refine ⟨427923989121104931279521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285282659414069954186347 427923989121104931279521)
    ·
      refine ⟨320942991840828698459641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427923989121104931279521 320942991840828698459641)
      ·
        refine ⟨240707243880621523844731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320942991840828698459641 240707243880621523844731)
        ·
          refine ⟨361060865820932285767097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240707243880621523844731 361060865820932285767097)
          ·
            refine ⟨270795649365699214325323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361060865820932285767097 270795649365699214325323)
            ·
              refine ⟨406193474048548821487985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270795649365699214325323 406193474048548821487985)
              ·
                refine ⟨304645105536411616115989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406193474048548821487985 304645105536411616115989)
                ·
                  refine ⟨14280239322019294505437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304645105536411616115989 14280239322019294505437)
                  ·
                    rfl

theorem cell21_62574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_62574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62574 prefixEnd_62574 := by exact prefixLift 62574
  have htrace : WordTrace (prefixWord ++ tailWord_62574) baseStart_62574 baseEnd_62574 := by
    simpa [prefixWord, tailWord_62574, baseEnd_62574] using wordTrace_append hprefix tailTrace_62574
  have hstable : (prefixWord ++ tailWord_62574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62574).length < 2 ^ (prefixWord ++ tailWord_62574).sum := by decide
  have hdescent : baseEnd_62574 < baseStart_62574 := by decide
  rcases family_descends (prefixWord ++ tailWord_62574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62653 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 3]
def baseStart_62653 : Nat := 118140960795 + 62653 * 2 ^ 59
def prefixEnd_62653 : Nat := 4983230072969 + 3 ^ 40 * 62653 * 2
def baseEnd_62653 : Nat := 14298268198332712688609

theorem tailTrace_62653 : CollatzResearch.WordTrace tailWord_62653 prefixEnd_62653 14298268198332712688609 := by
  unfold tailWord_62653
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285142642026356125616613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1523428428017570750411075 2285142642026356125616613)
  ·
    refine ⟨428464245379941773553115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2285142642026356125616613 428464245379941773553115)
    ·
      refine ⟨642696368069912660329673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428464245379941773553115 642696368069912660329673)
      ·
        refine ⟨482022276052434495247255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642696368069912660329673 482022276052434495247255)
        ·
          refine ⟨723033414078651742870883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482022276052434495247255 723033414078651742870883)
          ·
            refine ⟨1084550121117977614306325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723033414078651742870883 1084550121117977614306325)
            ·
              refine ⟨50838286927405200670609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1084550121117977614306325 50838286927405200670609)
              ·
                refine ⟨38128715195553900502957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50838286927405200670609 38128715195553900502957)
                ·
                  refine ⟨14298268198332712688609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38128715195553900502957 14298268198332712688609)
                  ·
                    rfl

theorem cell21_62653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_62653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62653 prefixEnd_62653 := by exact prefixLift 62653
  have htrace : WordTrace (prefixWord ++ tailWord_62653) baseStart_62653 baseEnd_62653 := by
    simpa [prefixWord, tailWord_62653, baseEnd_62653] using wordTrace_append hprefix tailTrace_62653
  have hstable : (prefixWord ++ tailWord_62653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62653).length < 2 ^ (prefixWord ++ tailWord_62653).sum := by decide
  have hdescent : baseEnd_62653 < baseStart_62653 := by decide
  rcases family_descends (prefixWord ++ tailWord_62653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62664 : List Nat := [2, 1, 3, 1, 2, 1, 5, 6]
def baseStart_62664 : Nat := 118140960795 + 62664 * 2 ^ 59
def prefixEnd_62664 : Nat := 4983230072969 + 3 ^ 40 * 62664 * 2
def baseEnd_62664 : Nat := 4766926182733046001751

theorem tailTrace_62664 : CollatzResearch.WordTrace tailWord_62664 prefixEnd_62664 4766926182733046001751 := by
  unfold tailWord_62664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142771922493252502133523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1523695896657670002844697 1142771922493252502133523)
  ·
    refine ⟨1714157883739878753200285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142771922493252502133523 1714157883739878753200285)
    ·
      refine ⟨642809206402454532450107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1714157883739878753200285 642809206402454532450107)
      ·
        refine ⟨964213809603681798675161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642809206402454532450107 964213809603681798675161)
        ·
          refine ⟨723160357202761349006371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964213809603681798675161 723160357202761349006371)
          ·
            refine ⟨1084740535804142023509557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723160357202761349006371 1084740535804142023509557)
            ·
              refine ⟨101694425231638314704021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1084740535804142023509557 101694425231638314704021)
              ·
                refine ⟨4766926182733046001751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101694425231638314704021 4766926182733046001751)
                ·
                  rfl

theorem cell21_62664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_62664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62664 prefixEnd_62664 := by exact prefixLift 62664
  have htrace : WordTrace (prefixWord ++ tailWord_62664) baseStart_62664 baseEnd_62664 := by
    simpa [prefixWord, tailWord_62664, baseEnd_62664] using wordTrace_append hprefix tailTrace_62664
  have hstable : (prefixWord ++ tailWord_62664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62664).length < 2 ^ (prefixWord ++ tailWord_62664).sum := by decide
  have hdescent : baseEnd_62664 < baseStart_62664 := by decide
  rcases family_descends (prefixWord ++ tailWord_62664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62771 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_62771 : Nat := 118140960795 + 62771 * 2 ^ 59
def prefixEnd_62771 : Nat := 4983230072969 + 3 ^ 40 * 62771 * 2
def baseEnd_62771 : Nat := 14325197405990729721701

theorem tailTrace_62771 : CollatzResearch.WordTrace tailWord_62771 prefixEnd_62771 14325197405990729721701 := by
  unfold tailWord_62771
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289446455598862278412167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1526297637065908185608111 2289446455598862278412167)
  ·
    refine ⟨3434169683398293417618251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2289446455598862278412167 3434169683398293417618251)
    ·
      refine ⟨5151254525097440126427377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434169683398293417618251 5151254525097440126427377)
      ·
        refine ⟨3863440893823080094820533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5151254525097440126427377 3863440893823080094820533)
        ·
          refine ⟨362197583795913758889425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3863440893823080094820533 362197583795913758889425)
          ·
            refine ⟨271648187846935319167069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362197583795913758889425 271648187846935319167069)
            ·
              refine ⟨101868070442600744687651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271648187846935319167069 101868070442600744687651)
              ·
                refine ⟨152802105663901117031477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101868070442600744687651 152802105663901117031477)
                ·
                  refine ⟨14325197405990729721701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152802105663901117031477 14325197405990729721701)
                  ·
                    rfl

theorem cell21_62771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_62771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62771 prefixEnd_62771 := by exact prefixLift 62771
  have htrace : WordTrace (prefixWord ++ tailWord_62771) baseStart_62771 baseEnd_62771 := by
    simpa [prefixWord, tailWord_62771, baseEnd_62771] using wordTrace_append hprefix tailTrace_62771
  have hstable : (prefixWord ++ tailWord_62771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62771).length < 2 ^ (prefixWord ++ tailWord_62771).sum := by decide
  have hdescent : baseEnd_62771 < baseStart_62771 := by decide
  rcases family_descends (prefixWord ++ tailWord_62771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62777 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 4]
def baseStart_62777 : Nat := 118140960795 + 62777 * 2 ^ 59
def prefixEnd_62777 : Nat := 4983230072969 + 3 ^ 40 * 62777 * 2
def baseEnd_62777 : Nat := 14326566687736052621689

theorem tailTrace_62777 : CollatzResearch.WordTrace tailWord_62777 prefixEnd_62777 14326566687736052621689 := by
  unfold tailWord_62777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289665293577125303130585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1526443529051416868753723 2289665293577125303130585)
  ·
    refine ⟨1717248970182843977347939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2289665293577125303130585 1717248970182843977347939)
    ·
      refine ⟨2575873455274265966021909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717248970182843977347939 2575873455274265966021909)
      ·
        refine ⟨120744068215981217157277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2575873455274265966021909 120744068215981217157277)
        ·
          refine ⟨45279025580992956433979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120744068215981217157277 45279025580992956433979)
          ·
            refine ⟨67918538371489434650969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45279025580992956433979 67918538371489434650969)
            ·
              refine ⟨50938903778617075988227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67918538371489434650969 50938903778617075988227)
              ·
                refine ⟨76408355667925613982341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50938903778617075988227 76408355667925613982341)
                ·
                  refine ⟨14326566687736052621689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76408355667925613982341 14326566687736052621689)
                  ·
                    rfl

theorem cell21_62777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_62777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62777 prefixEnd_62777 := by exact prefixLift 62777
  have htrace : WordTrace (prefixWord ++ tailWord_62777) baseStart_62777 baseEnd_62777 := by
    simpa [prefixWord, tailWord_62777, baseEnd_62777] using wordTrace_append hprefix tailTrace_62777
  have hstable : (prefixWord ++ tailWord_62777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62777).length < 2 ^ (prefixWord ++ tailWord_62777).sum := by decide
  have hdescent : baseEnd_62777 < baseStart_62777 := by decide
  rcases family_descends (prefixWord ++ tailWord_62777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62937 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_62937 : Nat := 118140960795 + 62937 * 2 ^ 59
def prefixEnd_62937 : Nat := 4983230072969 + 3 ^ 40 * 62937 * 2
def baseEnd_62937 : Nat := 14363080867611329954695

theorem tailTrace_62937 : CollatzResearch.WordTrace tailWord_62937 prefixEnd_62937 14363080867611329954695 := by
  unfold tailWord_62937
  simp only [CollatzResearch.WordTrace]
  refine ⟨2295500972997472628955065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1530333981998315085970043 2295500972997472628955065)
  ·
    refine ⟨1721625729748104471716299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2295500972997472628955065 1721625729748104471716299)
    ·
      refine ⟨2582438594622156707574449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721625729748104471716299 2582438594622156707574449)
      ·
        refine ⟨1936828945966617530680837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2582438594622156707574449 1936828945966617530680837)
        ·
          refine ⟨363155427368740787002657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1936828945966617530680837 363155427368740787002657)
          ·
            refine ⟨272366570526555590251993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363155427368740787002657 272366570526555590251993)
            ·
              refine ⟨204274927894916692688995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272366570526555590251993 204274927894916692688995)
              ·
                refine ⟨306412391842375039033493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204274927894916692688995 306412391842375039033493)
                ·
                  refine ⟨14363080867611329954695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 306412391842375039033493 14363080867611329954695)
                  ·
                    rfl

theorem cell21_62937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_62937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_62937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_62937 prefixEnd_62937 := by exact prefixLift 62937
  have htrace : WordTrace (prefixWord ++ tailWord_62937) baseStart_62937 baseEnd_62937 := by
    simpa [prefixWord, tailWord_62937, baseEnd_62937] using wordTrace_append hprefix tailTrace_62937
  have hstable : (prefixWord ++ tailWord_62937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62937).length < 2 ^ (prefixWord ++ tailWord_62937).sum := by decide
  have hdescent : baseEnd_62937 < baseStart_62937 := by decide
  rcases family_descends (prefixWord ++ tailWord_62937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63016 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_63016 : Nat := 118140960795 + 63016 * 2 ^ 59
def prefixEnd_63016 : Nat := 4983230072969 + 3 ^ 40 * 63016 * 2
def baseEnd_63016 : Nat := 14381109743924748137867

theorem tailTrace_63016 : CollatzResearch.WordTrace tailWord_63016 prefixEnd_63016 14381109743924748137867 := by
  unfold tailWord_63016
  simp only [CollatzResearch.WordTrace]
  refine ⟨1149191169855634560540451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1532254893140846080720601 1149191169855634560540451)
  ·
    refine ⟨1723786754783451840810677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1149191169855634560540451 1723786754783451840810677)
    ·
      refine ⟨161605008260948610076001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1723786754783451840810677 161605008260948610076001)
      ·
        refine ⟨121203756195711457557001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161605008260948610076001 121203756195711457557001)
        ·
          refine ⟨90902817146783593167751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121203756195711457557001 90902817146783593167751)
          ·
            refine ⟨136354225720175389751627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90902817146783593167751 136354225720175389751627)
            ·
              refine ⟨204531338580263084627441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136354225720175389751627 204531338580263084627441)
              ·
                refine ⟨153398503935197313470581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204531338580263084627441 153398503935197313470581)
                ·
                  refine ⟨14381109743924748137867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 153398503935197313470581 14381109743924748137867)
                  ·
                    rfl

theorem cell21_63016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_63016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63016 prefixEnd_63016 := by exact prefixLift 63016
  have htrace : WordTrace (prefixWord ++ tailWord_63016) baseStart_63016 baseEnd_63016 := by
    simpa [prefixWord, tailWord_63016, baseEnd_63016] using wordTrace_append hprefix tailTrace_63016
  have hstable : (prefixWord ++ tailWord_63016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63016).length < 2 ^ (prefixWord ++ tailWord_63016).sum := by decide
  have hdescent : baseEnd_63016 < baseStart_63016 := by decide
  rcases family_descends (prefixWord ++ tailWord_63016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63047 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 4]
def baseStart_63047 : Nat := 118140960795 + 63047 * 2 ^ 59
def prefixEnd_63047 : Nat := 4983230072969 + 3 ^ 40 * 63047 * 2
def baseEnd_63047 : Nat := 14388184366275583121137

theorem tailTrace_63047 : CollatzResearch.WordTrace tailWord_63047 prefixEnd_63047 14388184366275583121137 := by
  unfold tailWord_63047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299513002598961415459395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1533008668399307610306263 2299513002598961415459395)
  ·
    refine ⟨3449269503898442123189093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299513002598961415459395 3449269503898442123189093)
    ·
      refine ⟨646738031980957898097955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3449269503898442123189093 646738031980957898097955)
      ·
        refine ⟨970107047971436847146933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646738031980957898097955 970107047971436847146933)
        ·
          refine ⟨90947535747322204420025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 970107047971436847146933 90947535747322204420025)
          ·
            refine ⟨68210651810491653315019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90947535747322204420025 68210651810491653315019)
            ·
              refine ⟨102315977715737479972529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68210651810491653315019 102315977715737479972529)
              ·
                refine ⟨76736983286803109979397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102315977715737479972529 76736983286803109979397)
                ·
                  refine ⟨14388184366275583121137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76736983286803109979397 14388184366275583121137)
                  ·
                    rfl

theorem cell21_63047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_63047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63047 prefixEnd_63047 := by exact prefixLift 63047
  have htrace : WordTrace (prefixWord ++ tailWord_63047) baseStart_63047 baseEnd_63047 := by
    simpa [prefixWord, tailWord_63047, baseEnd_63047] using wordTrace_append hprefix tailTrace_63047
  have hstable : (prefixWord ++ tailWord_63047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63047).length < 2 ^ (prefixWord ++ tailWord_63047).sum := by decide
  have hdescent : baseEnd_63047 < baseStart_63047 := by decide
  rcases family_descends (prefixWord ++ tailWord_63047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63151 : List Nat := [1, 1, 2, 1, 2, 4, 2, 5, 3]
def baseStart_63151 : Nat := 118140960795 + 63151 * 2 ^ 59
def prefixEnd_63151 : Nat := 4983230072969 + 3 ^ 40 * 63151 * 2
def baseEnd_63151 : Nat := 14411918583194513387591

theorem tailTrace_63151 : CollatzResearch.WordTrace tailWord_63151 prefixEnd_63151 14411918583194513387591 := by
  unfold tailWord_63151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303306194222187177245307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1535537462814791451496871 2303306194222187177245307)
  ·
    refine ⟨3454959291333280765867961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303306194222187177245307 3454959291333280765867961)
    ·
      refine ⟨2591219468499960574400971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3454959291333280765867961 2591219468499960574400971)
      ·
        refine ⟨3886829202749940861601457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2591219468499960574400971 3886829202749940861601457)
        ·
          refine ⟨2915121902062455646201093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886829202749940861601457 2915121902062455646201093)
          ·
            refine ⟨546585356636710433662705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2915121902062455646201093 546585356636710433662705)
            ·
              refine ⟨409939017477532825247029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546585356636710433662705 409939017477532825247029)
              ·
                refine ⟨38431782888518702366909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 409939017477532825247029 38431782888518702366909)
                ·
                  refine ⟨14411918583194513387591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38431782888518702366909 14411918583194513387591)
                  ·
                    rfl

theorem cell21_63151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 5, 3].length) (baseStart_63151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63151 prefixEnd_63151 := by exact prefixLift 63151
  have htrace : WordTrace (prefixWord ++ tailWord_63151) baseStart_63151 baseEnd_63151 := by
    simpa [prefixWord, tailWord_63151, baseEnd_63151] using wordTrace_append hprefix tailTrace_63151
  have hstable : (prefixWord ++ tailWord_63151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63151).length < 2 ^ (prefixWord ++ tailWord_63151).sum := by decide
  have hdescent : baseEnd_63151 < baseStart_63151 := by decide
  rcases family_descends (prefixWord ++ tailWord_63151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63272 : List Nat := [2, 1, 5, 1, 1, 4, 7]
def baseStart_63272 : Nat := 118140960795 + 63272 * 2 ^ 59
def prefixEnd_63272 : Nat := 4983230072969 + 3 ^ 40 * 63272 * 2
def baseEnd_63272 : Nat := 1604392492413910207853

theorem tailTrace_63272 : CollatzResearch.WordTrace tailWord_63272 prefixEnd_63272 1604392492413910207853 := by
  unfold tailWord_63272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1153859713391912421200035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1538479617855883228266713 1153859713391912421200035)
  ·
    refine ⟨1730789570087868631800053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1153859713391912421200035 1730789570087868631800053)
    ·
      refine ⟨162261522195737684231255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1730789570087868631800053 162261522195737684231255)
      ·
        refine ⟨243392283293606526346883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162261522195737684231255 243392283293606526346883)
        ·
          refine ⟨365088424940409789520325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243392283293606526346883 365088424940409789520325)
          ·
            refine ⟨68454079676326835535061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 365088424940409789520325 68454079676326835535061)
            ·
              refine ⟨1604392492413910207853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68454079676326835535061 1604392492413910207853)
              ·
                rfl

theorem cell21_63272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 7].length) (baseStart_63272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63272 prefixEnd_63272 := by exact prefixLift 63272
  have htrace : WordTrace (prefixWord ++ tailWord_63272) baseStart_63272 baseEnd_63272 := by
    simpa [prefixWord, tailWord_63272, baseEnd_63272] using wordTrace_append hprefix tailTrace_63272
  have hstable : (prefixWord ++ tailWord_63272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63272).length < 2 ^ (prefixWord ++ tailWord_63272).sum := by decide
  have hdescent : baseEnd_63272 < baseStart_63272 := by decide
  rcases family_descends (prefixWord ++ tailWord_63272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63278 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_63278 : Nat := 118140960795 + 63278 * 2 ^ 59
def prefixEnd_63278 : Nat := 4983230072969 + 3 ^ 40 * 63278 * 2
def baseEnd_63278 : Nat := 14440901713470514770665

theorem tailTrace_63278 : CollatzResearch.WordTrace tailWord_63278 prefixEnd_63278 14440901713470514770665 := by
  unfold tailWord_63278
  simp only [CollatzResearch.WordTrace]
  refine ⟨288492283095260983389811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1538625509841391911412325 288492283095260983389811)
  ·
    refine ⟨432738424642891475084717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288492283095260983389811 432738424642891475084717)
    ·
      refine ⟨162276909241084303156769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 432738424642891475084717 162276909241084303156769)
      ·
        refine ⟨121707681930813227367577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162276909241084303156769 121707681930813227367577)
        ·
          refine ⟨91280761448109920525683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121707681930813227367577 91280761448109920525683)
          ·
            refine ⟨136921142172164880788525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91280761448109920525683 136921142172164880788525)
            ·
              refine ⟨51345428314561830295697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136921142172164880788525 51345428314561830295697)
              ·
                refine ⟨38509071235921372721773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51345428314561830295697 38509071235921372721773)
                ·
                  refine ⟨14440901713470514770665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38509071235921372721773 14440901713470514770665)
                  ·
                    rfl

theorem cell21_63278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_63278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63278 prefixEnd_63278 := by exact prefixLift 63278
  have htrace : WordTrace (prefixWord ++ tailWord_63278) baseStart_63278 baseEnd_63278 := by
    simpa [prefixWord, tailWord_63278, baseEnd_63278] using wordTrace_append hprefix tailTrace_63278
  have hstable : (prefixWord ++ tailWord_63278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63278).length < 2 ^ (prefixWord ++ tailWord_63278).sum := by decide
  have hdescent : baseEnd_63278 < baseStart_63278 := by decide
  rcases family_descends (prefixWord ++ tailWord_63278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63289 : List Nat := [1, 2, 1, 7, 1, 1, 2, 6]
def baseStart_63289 : Nat := 118140960795 + 63289 * 2 ^ 59
def prefixEnd_63289 : Nat := 4983230072969 + 3 ^ 40 * 63289 * 2
def baseEnd_63289 : Nat := 4814470687778980029103

theorem tailTrace_63289 : CollatzResearch.WordTrace tailWord_63289 prefixEnd_63289 4814470687778980029103 := by
  unfold tailWord_63289
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308339467722236745768921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1538892978481491163845947 2308339467722236745768921)
  ·
    refine ⟨1731254600791677559326691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2308339467722236745768921 1731254600791677559326691)
    ·
      refine ⟨2596881901187516338990037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731254600791677559326691 2596881901187516338990037)
      ·
        refine ⟨60864419559082414195079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2596881901187516338990037 60864419559082414195079)
        ·
          refine ⟨91296629338623621292619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60864419559082414195079 91296629338623621292619)
          ·
            refine ⟨136944944007935431938929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91296629338623621292619 136944944007935431938929)
            ·
              refine ⟨102708708005951573954197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136944944007935431938929 102708708005951573954197)
              ·
                refine ⟨4814470687778980029103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102708708005951573954197 4814470687778980029103)
                ·
                  rfl

theorem cell21_63289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 6].length) (baseStart_63289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63289 prefixEnd_63289 := by exact prefixLift 63289
  have htrace : WordTrace (prefixWord ++ tailWord_63289) baseStart_63289 baseEnd_63289 := by
    simpa [prefixWord, tailWord_63289, baseEnd_63289] using wordTrace_append hprefix tailTrace_63289
  have hstable : (prefixWord ++ tailWord_63289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63289).length < 2 ^ (prefixWord ++ tailWord_63289).sum := by decide
  have hdescent : baseEnd_63289 < baseStart_63289 := by decide
  rcases family_descends (prefixWord ++ tailWord_63289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63331 : List Nat := [1, 1, 1, 5, 4, 9]
def baseStart_63331 : Nat := 118140960795 + 63331 * 2 ^ 59
def prefixEnd_63331 : Nat := 4983230072969 + 3 ^ 40 * 63331 * 2
def baseEnd_63331 : Nat := 535296186502007421749

theorem tailTrace_63331 : CollatzResearch.WordTrace tailWord_63331 prefixEnd_63331 535296186502007421749 := by
  unfold tailWord_63331
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309871333570077918797847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1539914222380051945865231 2309871333570077918797847)
  ·
    refine ⟨3464807000355116878196771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2309871333570077918797847 3464807000355116878196771)
    ·
      refine ⟨5197210500532675317295157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464807000355116878196771 5197210500532675317295157)
      ·
        refine ⟨487238484424938310996421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5197210500532675317295157 487238484424938310996421)
        ·
          refine ⟨91357215829675933311829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 487238484424938310996421 91357215829675933311829)
          ·
            refine ⟨535296186502007421749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 91357215829675933311829 535296186502007421749)
            ·
              rfl

theorem cell21_63331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 9].length) (baseStart_63331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63331 prefixEnd_63331 := by exact prefixLift 63331
  have htrace : WordTrace (prefixWord ++ tailWord_63331) baseStart_63331 baseEnd_63331 := by
    simpa [prefixWord, tailWord_63331, baseEnd_63331] using wordTrace_append hprefix tailTrace_63331
  have hstable : (prefixWord ++ tailWord_63331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63331).length < 2 ^ (prefixWord ++ tailWord_63331).sum := by decide
  have hdescent : baseEnd_63331 < baseStart_63331 := by decide
  rcases family_descends (prefixWord ++ tailWord_63331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63382 : List Nat := [5, 3, 1, 1, 2, 1, 8]
def baseStart_63382 : Nat := 118140960795 + 63382 * 2 ^ 59
def prefixEnd_63382 : Nat := 4983230072969 + 3 ^ 40 * 63382 * 2
def baseEnd_63382 : Nat := 1607181770043271670791

theorem tailTrace_63382 : CollatzResearch.WordTrace tailWord_63382 prefixEnd_63382 1607181770043271670791 := by
  unfold tailWord_63382
  simp only [CollatzResearch.WordTrace]
  refine ⟨144483216024082101806525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1541154304256875752602933 144483216024082101806525)
  ·
    refine ⟨54181206009030788177447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144483216024082101806525 54181206009030788177447)
    ·
      refine ⟨81271809013546182266171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54181206009030788177447 81271809013546182266171)
      ·
        refine ⟨121907713520319273399257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81271809013546182266171 121907713520319273399257)
        ·
          refine ⟨91430785140239455049443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121907713520319273399257 91430785140239455049443)
          ·
            refine ⟨137146177710359182574165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91430785140239455049443 137146177710359182574165)
            ·
              refine ⟨1607181770043271670791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 137146177710359182574165 1607181770043271670791)
              ·
                rfl

theorem cell21_63382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 8].length) (baseStart_63382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63382 prefixEnd_63382 := by exact prefixLift 63382
  have htrace : WordTrace (prefixWord ++ tailWord_63382) baseStart_63382 baseEnd_63382 := by
    simpa [prefixWord, tailWord_63382, baseEnd_63382] using wordTrace_append hprefix tailTrace_63382
  have hstable : (prefixWord ++ tailWord_63382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63382).length < 2 ^ (prefixWord ++ tailWord_63382).sum := by decide
  have hdescent : baseEnd_63382 < baseStart_63382 := by decide
  rcases family_descends (prefixWord ++ tailWord_63382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63455 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 5]
def baseStart_63455 : Nat := 118140960795 + 63455 * 2 ^ 59
def prefixEnd_63455 : Nat := 4983230072969 + 3 ^ 40 * 63455 * 2
def baseEnd_63455 : Nat := 14481295524957540320303

theorem tailTrace_63455 : CollatzResearch.WordTrace tailWord_63455 prefixEnd_63455 14481295524957540320303 := by
  unfold tailWord_63455
  simp only [CollatzResearch.WordTrace]
  refine ⟨2314393985120847096311819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1542929323413898064207879 2314393985120847096311819)
  ·
    refine ⟨3471590977681270644467729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2314393985120847096311819 3471590977681270644467729)
    ·
      refine ⟨2603693233260952983350797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3471590977681270644467729 2603693233260952983350797)
      ·
        refine ⟨976384962472857368756549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2603693233260952983350797 976384962472857368756549)
        ·
          refine ⟨183072180463660756641853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 976384962472857368756549 183072180463660756641853)
          ·
            refine ⟨68652067673872783740695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183072180463660756641853 68652067673872783740695)
            ·
              refine ⟨102978101510809175611043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68652067673872783740695 102978101510809175611043)
              ·
                refine ⟨154467152266213763416565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102978101510809175611043 154467152266213763416565)
                ·
                  refine ⟨14481295524957540320303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154467152266213763416565 14481295524957540320303)
                  ·
                    rfl

theorem cell21_63455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_63455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63455 prefixEnd_63455 := by exact prefixLift 63455
  have htrace : WordTrace (prefixWord ++ tailWord_63455) baseStart_63455 baseEnd_63455 := by
    simpa [prefixWord, tailWord_63455, baseEnd_63455] using wordTrace_append hprefix tailTrace_63455
  have hstable : (prefixWord ++ tailWord_63455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63455).length < 2 ^ (prefixWord ++ tailWord_63455).sum := by decide
  have hdescent : baseEnd_63455 < baseStart_63455 := by decide
  rcases family_descends (prefixWord ++ tailWord_63455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63607 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 3]
def baseStart_63607 : Nat := 118140960795 + 63607 * 2 ^ 59
def prefixEnd_63607 : Nat := 4983230072969 + 3 ^ 40 * 63607 * 2
def baseEnd_63607 : Nat := 14515983995839053786659

theorem tailTrace_63607 : CollatzResearch.WordTrace tailWord_63607 prefixEnd_63607 14515983995839053786659 := by
  unfold tailWord_63607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319937880570177055845075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1546625253713451370563383 2319937880570177055845075)
  ·
    refine ⟨3479906820855265583767613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319937880570177055845075 3479906820855265583767613)
    ·
      refine ⟨1304965057820724593912855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3479906820855265583767613 1304965057820724593912855)
      ·
        refine ⟨1957447586731086890869283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304965057820724593912855 1957447586731086890869283)
        ·
          refine ⟨2936171380096630336303925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957447586731086890869283 2936171380096630336303925)
          ·
            refine ⟨275266066884059094028493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2936171380096630336303925 275266066884059094028493)
            ·
              refine ⟨103224775081522160260685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275266066884059094028493 103224775081522160260685)
              ·
                refine ⟨38709290655570810097757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103224775081522160260685 38709290655570810097757)
                ·
                  refine ⟨14515983995839053786659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38709290655570810097757 14515983995839053786659)
                  ·
                    rfl

theorem cell21_63607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 3].length) (baseStart_63607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63607 prefixEnd_63607 := by exact prefixLift 63607
  have htrace : WordTrace (prefixWord ++ tailWord_63607) baseStart_63607 baseEnd_63607 := by
    simpa [prefixWord, tailWord_63607, baseEnd_63607] using wordTrace_append hprefix tailTrace_63607
  have hstable : (prefixWord ++ tailWord_63607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63607).length < 2 ^ (prefixWord ++ tailWord_63607).sum := by decide
  have hdescent : baseEnd_63607 < baseStart_63607 := by decide
  rcases family_descends (prefixWord ++ tailWord_63607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63776 : List Nat := [2, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_63776 : Nat := 118140960795 + 63776 * 2 ^ 59
def prefixEnd_63776 : Nat := 4983230072969 + 3 ^ 40 * 63776 * 2
def baseEnd_63776 : Nat := 14554552098332315469647

theorem tailTrace_63776 : CollatzResearch.WordTrace tailWord_63776 prefixEnd_63776 14554552098332315469647 := by
  unfold tailWord_63776
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163050908478959459373591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1550734544638612612498121 1163050908478959459373591)
  ·
    refine ⟨1744576362718439189060387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163050908478959459373591 1744576362718439189060387)
    ·
      refine ⟨2616864544077658783590581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744576362718439189060387 2616864544077658783590581)
      ·
        refine ⟨245331051007280510961617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2616864544077658783590581 245331051007280510961617)
        ·
          refine ⟨183998288255460383221213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245331051007280510961617 183998288255460383221213)
          ·
            refine ⟨68999358095797643707955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183998288255460383221213 68999358095797643707955)
            ·
              refine ⟨103499037143696465561933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68999358095797643707955 103499037143696465561933)
              ·
                refine ⟨38812138928886174585725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103499037143696465561933 38812138928886174585725)
                ·
                  refine ⟨14554552098332315469647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38812138928886174585725 14554552098332315469647)
                  ·
                    rfl

theorem cell21_63776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_63776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63776 prefixEnd_63776 := by exact prefixLift 63776
  have htrace : WordTrace (prefixWord ++ tailWord_63776) baseStart_63776 baseEnd_63776 := by
    simpa [prefixWord, tailWord_63776, baseEnd_63776] using wordTrace_append hprefix tailTrace_63776
  have hstable : (prefixWord ++ tailWord_63776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63776).length < 2 ^ (prefixWord ++ tailWord_63776).sum := by decide
  have hdescent : baseEnd_63776 < baseStart_63776 := by decide
  rcases family_descends (prefixWord ++ tailWord_63776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63838 : List Nat := [4, 4, 2, 1, 1, 9]
def baseStart_63838 : Nat := 118140960795 + 63838 * 2 ^ 59
def prefixEnd_63838 : Nat := 4983230072969 + 3 ^ 40 * 63838 * 2
def baseEnd_63838 : Nat := 539581531223480942081

theorem tailTrace_63838 : CollatzResearch.WordTrace tailWord_63838 prefixEnd_63838 539581531223480942081 := by
  unfold tailWord_63838
  simp only [CollatzResearch.WordTrace]
  refine ⟨291045392841662938438021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1552242095155535671669445 291045392841662938438021)
  ·
    refine ⟨54571011157811800957129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 291045392841662938438021 54571011157811800957129)
    ·
      refine ⟨40928258368358850717847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54571011157811800957129 40928258368358850717847)
      ·
        refine ⟨61392387552538276076771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40928258368358850717847 61392387552538276076771)
        ·
          refine ⟨92088581328807414115157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61392387552538276076771 92088581328807414115157)
          ·
            refine ⟨539581531223480942081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 92088581328807414115157 539581531223480942081)
            ·
              rfl

theorem cell21_63838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 9].length) (baseStart_63838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63838 prefixEnd_63838 := by exact prefixLift 63838
  have htrace : WordTrace (prefixWord ++ tailWord_63838) baseStart_63838 baseEnd_63838 := by
    simpa [prefixWord, tailWord_63838, baseEnd_63838] using wordTrace_append hprefix tailTrace_63838
  have hstable : (prefixWord ++ tailWord_63838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63838).length < 2 ^ (prefixWord ++ tailWord_63838).sum := by decide
  have hdescent : baseEnd_63838 < baseStart_63838 := by decide
  rcases family_descends (prefixWord ++ tailWord_63838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63911 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 3]
def baseStart_63911 : Nat := 118140960795 + 63911 * 2 ^ 59
def prefixEnd_63911 : Nat := 4983230072969 + 3 ^ 40 * 63911 * 2
def baseEnd_63911 : Nat := 14585360937602080719371

theorem tailTrace_63911 : CollatzResearch.WordTrace tailWord_63911 prefixEnd_63911 14585360937602080719371 := by
  unfold tailWord_63911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2331025671468836974911587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1554017114312557983274391 2331025671468836974911587)
  ·
    refine ⟨3496538507203255462367381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2331025671468836974911587 3496538507203255462367381)
    ·
      refine ⟨163900242525152599798471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3496538507203255462367381 163900242525152599798471)
      ·
        refine ⟨245850363787728899697707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163900242525152599798471 245850363787728899697707)
        ·
          refine ⟨368775545681593349546561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245850363787728899697707 368775545681593349546561)
          ·
            refine ⟨276581659261195012159921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368775545681593349546561 276581659261195012159921)
            ·
              refine ⟨207436244445896259119941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276581659261195012159921 207436244445896259119941)
              ·
                refine ⟨38894295833605548584989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207436244445896259119941 38894295833605548584989)
                ·
                  refine ⟨14585360937602080719371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38894295833605548584989 14585360937602080719371)
                  ·
                    rfl

theorem cell21_63911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 3].length) (baseStart_63911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63911 prefixEnd_63911 := by exact prefixLift 63911
  have htrace : WordTrace (prefixWord ++ tailWord_63911) baseStart_63911 baseEnd_63911 := by
    simpa [prefixWord, tailWord_63911, baseEnd_63911] using wordTrace_append hprefix tailTrace_63911
  have hstable : (prefixWord ++ tailWord_63911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63911).length < 2 ^ (prefixWord ++ tailWord_63911).sum := by decide
  have hdescent : baseEnd_63911 < baseStart_63911 := by decide
  rcases family_descends (prefixWord ++ tailWord_63911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63922 : List Nat := [3, 2, 1, 1, 1, 1, 4, 8]
def baseStart_63922 : Nat := 118140960795 + 63922 * 2 ^ 59
def prefixEnd_63922 : Nat := 4983230072969 + 3 ^ 40 * 63922 * 2
def baseEnd_63922 : Nat := 4862623762489502012005

theorem tailTrace_63922 : CollatzResearch.WordTrace tailWord_63922 prefixEnd_63922 4862623762489502012005 := by
  unfold tailWord_63922
  simp only [CollatzResearch.WordTrace]
  refine ⟨582856718607246463390505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1554284582952657235708013 582856718607246463390505)
  ·
    refine ⟨437142538955434847542879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 582856718607246463390505 437142538955434847542879)
    ·
      refine ⟨655713808433152271314319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437142538955434847542879 655713808433152271314319)
      ·
        refine ⟨983570712649728406971479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655713808433152271314319 983570712649728406971479)
        ·
          refine ⟨1475356068974592610457219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 983570712649728406971479 1475356068974592610457219)
          ·
            refine ⟨2213034103461888915685829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475356068974592610457219 2213034103461888915685829)
            ·
              refine ⟨414943894399104171691093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2213034103461888915685829 414943894399104171691093)
              ·
                refine ⟨4862623762489502012005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 414943894399104171691093 4862623762489502012005)
                ·
                  rfl

theorem cell21_63922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_63922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63922 prefixEnd_63922 := by exact prefixLift 63922
  have htrace : WordTrace (prefixWord ++ tailWord_63922) baseStart_63922 baseEnd_63922 := by
    simpa [prefixWord, tailWord_63922, baseEnd_63922] using wordTrace_append hprefix tailTrace_63922
  have hstable : (prefixWord ++ tailWord_63922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63922).length < 2 ^ (prefixWord ++ tailWord_63922).sum := by decide
  have hdescent : baseEnd_63922 < baseStart_63922 := by decide
  rcases family_descends (prefixWord ++ tailWord_63922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63984 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_63984 : Nat := 118140960795 + 63984 * 2 ^ 59
def prefixEnd_63984 : Nat := 4983230072969 + 3 ^ 40 * 63984 * 2
def baseEnd_63984 : Nat := 14602020532170176002555

theorem tailTrace_63984 : CollatzResearch.WordTrace tailWord_63984 prefixEnd_63984 14602020532170176002555 := by
  unfold tailWord_63984
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166844100102185221159503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1555792133469580294879337 1166844100102185221159503)
  ·
    refine ⟨1750266150153277831739255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166844100102185221159503 1750266150153277831739255)
    ·
      refine ⟨2625399225229916747608883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1750266150153277831739255 2625399225229916747608883)
      ·
        refine ⟨3938098837844875121413325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2625399225229916747608883 3938098837844875121413325)
        ·
          refine ⟨1476787064191828170529997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3938098837844875121413325 1476787064191828170529997)
          ·
            refine ⟨553795149071935563948749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1476787064191828170529997 553795149071935563948749)
            ·
              refine ⟨207673180901975836480781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 553795149071935563948749 207673180901975836480781)
              ·
                refine ⟨77877442838240938680293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 207673180901975836480781 77877442838240938680293)
                ·
                  refine ⟨14602020532170176002555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77877442838240938680293 14602020532170176002555)
                  ·
                    rfl

theorem cell21_63984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_63984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_63984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_63984 prefixEnd_63984 := by exact prefixLift 63984
  have htrace : WordTrace (prefixWord ++ tailWord_63984) baseStart_63984 baseEnd_63984 := by
    simpa [prefixWord, tailWord_63984, baseEnd_63984] using wordTrace_append hprefix tailTrace_63984
  have hstable : (prefixWord ++ tailWord_63984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63984).length < 2 ^ (prefixWord ++ tailWord_63984).sum := by decide
  have hdescent : baseEnd_63984 < baseStart_63984 := by decide
  rcases family_descends (prefixWord ++ tailWord_63984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64032 : List Nat := [2, 1, 1, 6, 2, 2, 1, 6]
def baseStart_64032 : Nat := 118140960795 + 64032 * 2 ^ 59
def prefixEnd_64032 : Nat := 4983230072969 + 3 ^ 40 * 64032 * 2
def baseEnd_64032 : Nat := 4870991595377586400819

theorem tailTrace_64032 : CollatzResearch.WordTrace tailWord_64032 prefixEnd_64032 4870991595377586400819 := by
  unfold tailWord_64032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1167719452015237320033175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1556959269353649760044233 1167719452015237320033175)
  ·
    refine ⟨1751579178022855980049763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1167719452015237320033175 1751579178022855980049763)
    ·
      refine ⟨2627368767034283970074645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1751579178022855980049763 2627368767034283970074645)
      ·
        refine ⟨123157910954732061097249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2627368767034283970074645 123157910954732061097249)
        ·
          refine ⟨92368433216049045822937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123157910954732061097249 92368433216049045822937)
          ·
            refine ⟨69276324912036784367203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92368433216049045822937 69276324912036784367203)
            ·
              refine ⟨103914487368055176550805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69276324912036784367203 103914487368055176550805)
              ·
                refine ⟨4870991595377586400819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103914487368055176550805 4870991595377586400819)
                ·
                  rfl

theorem cell21_64032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_64032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64032 prefixEnd_64032 := by exact prefixLift 64032
  have htrace : WordTrace (prefixWord ++ tailWord_64032) baseStart_64032 baseEnd_64032 := by
    simpa [prefixWord, tailWord_64032, baseEnd_64032] using wordTrace_append hprefix tailTrace_64032
  have hstable : (prefixWord ++ tailWord_64032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64032).length < 2 ^ (prefixWord ++ tailWord_64032).sum := by decide
  have hdescent : baseEnd_64032 < baseStart_64032 := by decide
  rcases family_descends (prefixWord ++ tailWord_64032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64074 : List Nat := [3, 1, 2, 1, 1, 5, 8]
def baseStart_64074 : Nat := 118140960795 + 64074 * 2 ^ 59
def prefixEnd_64074 : Nat := 4983230072969 + 3 ^ 40 * 64074 * 2
def baseEnd_64074 : Nat := 1624728862038891055819

theorem tailTrace_64074 : CollatzResearch.WordTrace tailWord_64074 prefixEnd_64074 1624728862038891055819 := by
  unfold tailWord_64074
  simp only [CollatzResearch.WordTrace]
  refine ⟨584242692469578953273819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1557980513252210542063517 584242692469578953273819)
  ·
    refine ⟨876364038704368429910729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 584242692469578953273819 876364038704368429910729)
    ·
      refine ⟨657273029028276322433047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 876364038704368429910729 657273029028276322433047)
      ·
        refine ⟨985909543542414483649571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657273029028276322433047 985909543542414483649571)
        ·
          refine ⟨1478864315313621725474357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985909543542414483649571 1478864315313621725474357)
          ·
            refine ⟨138643529560652036763221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1478864315313621725474357 138643529560652036763221)
            ·
              refine ⟨1624728862038891055819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 138643529560652036763221 1624728862038891055819)
              ·
                rfl

theorem cell21_64074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 8].length) (baseStart_64074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64074 prefixEnd_64074 := by exact prefixLift 64074
  have htrace : WordTrace (prefixWord ++ tailWord_64074) baseStart_64074 baseEnd_64074 := by
    simpa [prefixWord, tailWord_64074, baseEnd_64074] using wordTrace_append hprefix tailTrace_64074
  have hstable : (prefixWord ++ tailWord_64074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64074).length < 2 ^ (prefixWord ++ tailWord_64074).sum := by decide
  have hdescent : baseEnd_64074 < baseStart_64074 := by decide
  rcases family_descends (prefixWord ++ tailWord_64074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64077 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_64077 : Nat := 118140960795 + 64077 * 2 ^ 59
def prefixEnd_64077 : Nat := 4983230072969 + 3 ^ 40 * 64077 * 2
def baseEnd_64077 : Nat := 14623244399222680952365

theorem tailTrace_64077 : CollatzResearch.WordTrace tailWord_64077 prefixEnd_64077 14623244399222680952365 := by
  unfold tailWord_64077
  simp only [CollatzResearch.WordTrace]
  refine ⟨2337080188867447325454485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1558053459244964883636323 2337080188867447325454485)
  ·
    refine ⟨109550633853161593380679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2337080188867447325454485 109550633853161593380679)
    ·
      refine ⟨164325950779742390071019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109550633853161593380679 164325950779742390071019)
      ·
        refine ⟨246488926169613585106529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164325950779742390071019 246488926169613585106529)
        ·
          refine ⟨184866694627210188829897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246488926169613585106529 184866694627210188829897)
          ·
            refine ⟨138650020970407641622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184866694627210188829897 138650020970407641622423)
            ·
              refine ⟨207975031455611462433635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138650020970407641622423 207975031455611462433635)
              ·
                refine ⟨311962547183417193650453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207975031455611462433635 311962547183417193650453)
                ·
                  refine ⟨14623244399222680952365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311962547183417193650453 14623244399222680952365)
                  ·
                    rfl

theorem cell21_64077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_64077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64077 prefixEnd_64077 := by exact prefixLift 64077
  have htrace : WordTrace (prefixWord ++ tailWord_64077) baseStart_64077 baseEnd_64077 := by
    simpa [prefixWord, tailWord_64077, baseEnd_64077] using wordTrace_append hprefix tailTrace_64077
  have hstable : (prefixWord ++ tailWord_64077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64077).length < 2 ^ (prefixWord ++ tailWord_64077).sum := by decide
  have hdescent : baseEnd_64077 < baseStart_64077 := by decide
  rcases family_descends (prefixWord ++ tailWord_64077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64119 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_64119 : Nat := 118140960795 + 64119 * 2 ^ 59
def prefixEnd_64119 : Nat := 4983230072969 + 3 ^ 40 * 64119 * 2
def baseEnd_64119 : Nat := 14632829371439941252279

theorem tailTrace_64119 : CollatzResearch.WordTrace tailWord_64119 prefixEnd_64119 14632829371439941252279 := by
  unfold tailWord_64119
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338612054715288498483411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1559074703143525665655607 2338612054715288498483411)
  ·
    refine ⟨3507918082072932747725117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338612054715288498483411 3507918082072932747725117)
    ·
      refine ⟨1315469280777349780396919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3507918082072932747725117 1315469280777349780396919)
      ·
        refine ⟨1973203921166024670595379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1315469280777349780396919 1973203921166024670595379)
        ·
          refine ⟨2959805881749037005893069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973203921166024670595379 2959805881749037005893069)
          ·
            refine ⟨1109927205655888877209901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2959805881749037005893069 1109927205655888877209901)
            ·
              refine ⟨416222702120958328953713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109927205655888877209901 416222702120958328953713)
              ·
                refine ⟨312167026590718746715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 416222702120958328953713 312167026590718746715285)
                ·
                  refine ⟨14632829371439941252279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 312167026590718746715285 14632829371439941252279)
                  ·
                    rfl

theorem cell21_64119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_64119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64119 prefixEnd_64119 := by exact prefixLift 64119
  have htrace : WordTrace (prefixWord ++ tailWord_64119) baseStart_64119 baseEnd_64119 := by
    simpa [prefixWord, tailWord_64119, baseEnd_64119] using wordTrace_append hprefix tailTrace_64119
  have hstable : (prefixWord ++ tailWord_64119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64119).length < 2 ^ (prefixWord ++ tailWord_64119).sum := by decide
  have hdescent : baseEnd_64119 < baseStart_64119 := by decide
  rcases family_descends (prefixWord ++ tailWord_64119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64240 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_64240 : Nat := 118140960795 + 64240 * 2 ^ 59
def prefixEnd_64240 : Nat := 4983230072969 + 3 ^ 40 * 64240 * 2
def baseEnd_64240 : Nat := 14660443219970619735365

theorem tailTrace_64240 : CollatzResearch.WordTrace tailWord_64240 prefixEnd_64240 14660443219970619735365 := by
  unfold tailWord_64240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171512643638463081819087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1562016858184617442425449 1171512643638463081819087)
  ·
    refine ⟨1757268965457694622728631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1171512643638463081819087 1757268965457694622728631)
    ·
      refine ⟨2635903448186541934092947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1757268965457694622728631 2635903448186541934092947)
      ·
        refine ⟨3953855172279812901139421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635903448186541934092947 3953855172279812901139421)
        ·
          refine ⟨1482695689604929837927283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3953855172279812901139421 1482695689604929837927283)
          ·
            refine ⟨2224043534407394756890925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482695689604929837927283 2224043534407394756890925)
            ·
              refine ⟨834016325402773033834097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2224043534407394756890925 834016325402773033834097)
              ·
                refine ⟨625512244052079775375573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 834016325402773033834097 625512244052079775375573)
                ·
                  refine ⟨14660443219970619735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 625512244052079775375573 14660443219970619735365)
                  ·
                    rfl

theorem cell21_64240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_64240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64240 prefixEnd_64240 := by exact prefixLift 64240
  have htrace : WordTrace (prefixWord ++ tailWord_64240) baseStart_64240 baseEnd_64240 := by
    simpa [prefixWord, tailWord_64240, baseEnd_64240] using wordTrace_append hprefix tailTrace_64240
  have hstable : (prefixWord ++ tailWord_64240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64240).length < 2 ^ (prefixWord ++ tailWord_64240).sum := by decide
  have hdescent : baseEnd_64240 < baseStart_64240 := by decide
  rcases family_descends (prefixWord ++ tailWord_64240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64308 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_64308 : Nat := 118140960795 + 64308 * 2 ^ 59
def prefixEnd_64308 : Nat := 4983230072969 + 3 ^ 40 * 64308 * 2
def baseEnd_64308 : Nat := 14675961746417612601893

theorem tailTrace_64308 : CollatzResearch.WordTrace tailWord_64308 prefixEnd_64308 14675961746417612601893 := by
  unfold tailWord_64308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172752725515286888556789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1563670300687049184742385 1172752725515286888556789)
  ·
    refine ⟨109945568017058145802199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1172752725515286888556789 109945568017058145802199)
    ·
      refine ⟨164918352025587218703299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109945568017058145802199 164918352025587218703299)
      ·
        refine ⟨247377528038380828054949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164918352025587218703299 247377528038380828054949)
        ·
          refine ⟨46383286507196405260303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247377528038380828054949 46383286507196405260303)
          ·
            refine ⟨69574929760794607890455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46383286507196405260303 69574929760794607890455)
            ·
              refine ⟨104362394641191911835683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69574929760794607890455 104362394641191911835683)
              ·
                refine ⟨156543591961787867753525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104362394641191911835683 156543591961787867753525)
                ·
                  refine ⟨14675961746417612601893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156543591961787867753525 14675961746417612601893)
                  ·
                    rfl

theorem cell21_64308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_64308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64308 prefixEnd_64308 := by exact prefixLift 64308
  have htrace : WordTrace (prefixWord ++ tailWord_64308) baseStart_64308 baseEnd_64308 := by
    simpa [prefixWord, tailWord_64308, baseEnd_64308] using wordTrace_append hprefix tailTrace_64308
  have hstable : (prefixWord ++ tailWord_64308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64308).length < 2 ^ (prefixWord ++ tailWord_64308).sum := by decide
  have hdescent : baseEnd_64308 < baseStart_64308 := by decide
  rcases family_descends (prefixWord ++ tailWord_64308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64364 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_64364 : Nat := 118140960795 + 64364 * 2 ^ 59
def prefixEnd_64364 : Nat := 4983230072969 + 3 ^ 40 * 64364 * 2
def baseEnd_64364 : Nat := 14688741709373959668445

theorem tailTrace_64364 : CollatzResearch.WordTrace tailWord_64364 prefixEnd_64364 14688741709373959668445 := by
  unfold tailWord_64364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173773969413847670576073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1565031959218463560768097 1173773969413847670576073)
  ·
    refine ⟨880330477060385752932055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1173773969413847670576073 880330477060385752932055)
    ·
      refine ⟨1320495715590578629398083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 880330477060385752932055 1320495715590578629398083)
      ·
        refine ⟨1980743573385867944097125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320495715590578629398083 1980743573385867944097125)
        ·
          refine ⟨371389420009850239518211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1980743573385867944097125 371389420009850239518211)
          ·
            refine ⟨557084130014775359277317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371389420009850239518211 557084130014775359277317)
            ·
              refine ⟨104453274377770379864497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557084130014775359277317 104453274377770379864497)
              ·
                refine ⟨78339955783327784898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104453274377770379864497 78339955783327784898373)
                ·
                  refine ⟨14688741709373959668445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78339955783327784898373 14688741709373959668445)
                  ·
                    rfl

theorem cell21_64364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_64364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64364 prefixEnd_64364 := by exact prefixLift 64364
  have htrace : WordTrace (prefixWord ++ tailWord_64364) baseStart_64364 baseEnd_64364 := by
    simpa [prefixWord, tailWord_64364, baseEnd_64364] using wordTrace_append hprefix tailTrace_64364
  have hstable : (prefixWord ++ tailWord_64364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64364).length < 2 ^ (prefixWord ++ tailWord_64364).sum := by decide
  have hdescent : baseEnd_64364 < baseStart_64364 := by decide
  rcases family_descends (prefixWord ++ tailWord_64364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64564 : List Nat := [2, 5, 1, 2, 1, 2, 3, 5]
def baseStart_64564 : Nat := 118140960795 + 64564 * 2 ^ 59
def prefixEnd_64564 : Nat := 4983230072969 + 3 ^ 40 * 64564 * 2
def baseEnd_64564 : Nat := 4911461478072685444901

theorem tailTrace_64564 : CollatzResearch.WordTrace tailWord_64564 prefixEnd_64564 4911461478072685444901 := by
  unfold tailWord_64564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177421269051564749216373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1569895025402086332288497 1177421269051564749216373)
  ·
    refine ⟨110383243973584195239035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1177421269051564749216373 110383243973584195239035)
    ·
      refine ⟨165574865960376292858553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110383243973584195239035 165574865960376292858553)
      ·
        refine ⟨124181149470282219643915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165574865960376292858553 124181149470282219643915)
        ·
          refine ⟨186271724205423329465873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124181149470282219643915 186271724205423329465873)
          ·
            refine ⟨139703793154067497099405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186271724205423329465873 139703793154067497099405)
            ·
              refine ⟨52388922432775311412277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139703793154067497099405 52388922432775311412277)
              ·
                refine ⟨4911461478072685444901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52388922432775311412277 4911461478072685444901)
                ·
                  rfl

theorem cell21_64564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_64564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64564 prefixEnd_64564 := by exact prefixLift 64564
  have htrace : WordTrace (prefixWord ++ tailWord_64564) baseStart_64564 baseEnd_64564 := by
    simpa [prefixWord, tailWord_64564, baseEnd_64564] using wordTrace_append hprefix tailTrace_64564
  have hstable : (prefixWord ++ tailWord_64564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64564).length < 2 ^ (prefixWord ++ tailWord_64564).sum := by decide
  have hdescent : baseEnd_64564 < baseStart_64564 := by decide
  rcases family_descends (prefixWord ++ tailWord_64564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64620 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_64620 : Nat := 118140960795 + 64620 * 2 ^ 59
def prefixEnd_64620 : Nat := 4983230072969 + 3 ^ 40 * 64620 * 2
def baseEnd_64620 : Nat := 14747164397174403401255

theorem tailTrace_64620 : CollatzResearch.WordTrace tailWord_64620 prefixEnd_64620 14747164397174403401255 := by
  unfold tailWord_64620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1178442512950125531235657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1571256683933500708314209 1178442512950125531235657)
  ·
    refine ⟨883831884712594148426743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1178442512950125531235657 883831884712594148426743)
    ·
      refine ⟨1325747827068891222640115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883831884712594148426743 1325747827068891222640115)
      ·
        refine ⟨1988621740603336833960173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325747827068891222640115 1988621740603336833960173)
        ·
          refine ⟨745733152726251312735065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1988621740603336833960173 745733152726251312735065)
          ·
            refine ⟨559299864544688484551299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745733152726251312735065 559299864544688484551299)
            ·
              refine ⟨838949796817032726826949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559299864544688484551299 838949796817032726826949)
              ·
                refine ⟨157303086903193636280053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838949796817032726826949 157303086903193636280053)
                ·
                  refine ⟨14747164397174403401255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157303086903193636280053 14747164397174403401255)
                  ·
                    rfl

theorem cell21_64620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_64620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64620 prefixEnd_64620 := by exact prefixLift 64620
  have htrace : WordTrace (prefixWord ++ tailWord_64620) baseStart_64620 baseEnd_64620 := by
    simpa [prefixWord, tailWord_64620, baseEnd_64620] using wordTrace_append hprefix tailTrace_64620
  have hstable : (prefixWord ++ tailWord_64620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64620).length < 2 ^ (prefixWord ++ tailWord_64620).sum := by decide
  have hdescent : baseEnd_64620 < baseStart_64620 := by decide
  rcases family_descends (prefixWord ++ tailWord_64620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64629 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 3]
def baseStart_64629 : Nat := 118140960795 + 64629 * 2 ^ 59
def prefixEnd_64629 : Nat := 4983230072969 + 3 ^ 40 * 64629 * 2
def baseEnd_64629 : Nat := 14749218319792387751237

theorem tailTrace_64629 : CollatzResearch.WordTrace tailWord_64629 prefixEnd_64629 14749218319792387751237 := by
  unfold tailWord_64629
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357213282867645599548941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1571475521911763733032627 2357213282867645599548941)
  ·
    refine ⟨883954981075367099830853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2357213282867645599548941 883954981075367099830853)
    ·
      refine ⟨165741558951631331218285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 883954981075367099830853 165741558951631331218285)
      ·
        refine ⟨62153084606861749206857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165741558951631331218285 62153084606861749206857)
        ·
          refine ⟨46614813455146311905143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62153084606861749206857 46614813455146311905143)
          ·
            refine ⟨69922220182719467857715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46614813455146311905143 69922220182719467857715)
            ·
              refine ⟨104883330274079201786573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69922220182719467857715 104883330274079201786573)
              ·
                refine ⟨39331248852779700669965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104883330274079201786573 39331248852779700669965)
                ·
                  refine ⟨14749218319792387751237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39331248852779700669965 14749218319792387751237)
                  ·
                    rfl

theorem cell21_64629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_64629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64629 prefixEnd_64629 := by exact prefixLift 64629
  have htrace : WordTrace (prefixWord ++ tailWord_64629) baseStart_64629 baseEnd_64629 := by
    simpa [prefixWord, tailWord_64629, baseEnd_64629] using wordTrace_append hprefix tailTrace_64629
  have hstable : (prefixWord ++ tailWord_64629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64629).length < 2 ^ (prefixWord ++ tailWord_64629).sum := by decide
  have hdescent : baseEnd_64629 < baseStart_64629 := by decide
  rcases family_descends (prefixWord ++ tailWord_64629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64654 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_64654 : Nat := 118140960795 + 64654 * 2 ^ 59
def prefixEnd_64654 : Nat := 4983230072969 + 3 ^ 40 * 64654 * 2
def baseEnd_64654 : Nat := 14754923660397899834519

theorem tailTrace_64654 : CollatzResearch.WordTrace tailWord_64654 prefixEnd_64654 14754923660397899834519 := by
  unfold tailWord_64654
  simp only [CollatzResearch.WordTrace]
  refine ⟨294765638472134358651127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1572083405184716579472677 294765638472134358651127)
  ·
    refine ⟨442148457708201537976691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294765638472134358651127 442148457708201537976691)
    ·
      refine ⟨663222686562302306965037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442148457708201537976691 663222686562302306965037)
      ·
        refine ⟨248708507460863365111889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 663222686562302306965037 248708507460863365111889)
        ·
          refine ⟨186531380595647523833917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248708507460863365111889 186531380595647523833917)
          ·
            refine ⟨69949267723367821437719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186531380595647523833917 69949267723367821437719)
            ·
              refine ⟨104923901585051732156579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69949267723367821437719 104923901585051732156579)
              ·
                refine ⟨157385852377577598234869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104923901585051732156579 157385852377577598234869)
                ·
                  refine ⟨14754923660397899834519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157385852377577598234869 14754923660397899834519)
                  ·
                    rfl

theorem cell21_64654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_64654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64654 prefixEnd_64654 := by exact prefixLift 64654
  have htrace : WordTrace (prefixWord ++ tailWord_64654) baseStart_64654 baseEnd_64654 := by
    simpa [prefixWord, tailWord_64654, baseEnd_64654] using wordTrace_append hprefix tailTrace_64654
  have hstable : (prefixWord ++ tailWord_64654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64654).length < 2 ^ (prefixWord ++ tailWord_64654).sum := by decide
  have hdescent : baseEnd_64654 < baseStart_64654 := by decide
  rcases family_descends (prefixWord ++ tailWord_64654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64668 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_64668 : Nat := 118140960795 + 64668 * 2 ^ 59
def prefixEnd_64668 : Nat := 4983230072969 + 3 ^ 40 * 64668 * 2
def baseEnd_64668 : Nat := 14758118651136986601157

theorem tailTrace_64668 : CollatzResearch.WordTrace tailWord_64668 prefixEnd_64668 14758118651136986601157 := by
  unfold tailWord_64668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179317864863177630109329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1572423819817570173479105 1179317864863177630109329)
  ·
    refine ⟨884488398647383222581997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1179317864863177630109329 884488398647383222581997)
    ·
      refine ⟨331683149492768708468249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 884488398647383222581997 331683149492768708468249)
      ·
        refine ⟨248762362119576531351187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331683149492768708468249 248762362119576531351187)
        ·
          refine ⟨373143543179364797026781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248762362119576531351187 373143543179364797026781)
          ·
            refine ⟨139928828692261798885043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373143543179364797026781 139928828692261798885043)
            ·
              refine ⟨209893243038392698327565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139928828692261798885043 209893243038392698327565)
              ·
                refine ⟨78709966139397261872837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209893243038392698327565 78709966139397261872837)
                ·
                  refine ⟨14758118651136986601157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78709966139397261872837 14758118651136986601157)
                  ·
                    rfl

theorem cell21_64668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_64668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64668 prefixEnd_64668 := by exact prefixLift 64668
  have htrace : WordTrace (prefixWord ++ tailWord_64668) baseStart_64668 baseEnd_64668 := by
    simpa [prefixWord, tailWord_64668, baseEnd_64668] using wordTrace_append hprefix tailTrace_64668
  have hstable : (prefixWord ++ tailWord_64668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64668).length < 2 ^ (prefixWord ++ tailWord_64668).sum := by decide
  have hdescent : baseEnd_64668 < baseStart_64668 := by decide
  rcases family_descends (prefixWord ++ tailWord_64668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64727 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 4]
def baseStart_64727 : Nat := 118140960795 + 64727 * 2 ^ 59
def prefixEnd_64727 : Nat := 4983230072969 + 3 ^ 40 * 64727 * 2
def baseEnd_64727 : Nat := 14771583254965995117703

theorem tailTrace_64727 : CollatzResearch.WordTrace tailWord_64727 prefixEnd_64727 14771583254965995117703 := by
  unfold tailWord_64727
  simp only [CollatzResearch.WordTrace]
  refine ⟨2360787636512608336616435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1573858424341738891077623 2360787636512608336616435)
  ·
    refine ⟨3541181454768912504924653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2360787636512608336616435 3541181454768912504924653)
    ·
      refine ⟨1327943045538342189346745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3541181454768912504924653 1327943045538342189346745)
      ·
        refine ⟨995957284153756642010059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1327943045538342189346745 995957284153756642010059)
        ·
          refine ⟨1493935926230634963015089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995957284153756642010059 1493935926230634963015089)
          ·
            refine ⟨1120451944672976222261317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493935926230634963015089 1120451944672976222261317)
            ·
              refine ⟨210084739626183041673997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1120451944672976222261317 210084739626183041673997)
              ·
                refine ⟨78781777359818640627749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210084739626183041673997 78781777359818640627749)
                ·
                  refine ⟨14771583254965995117703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78781777359818640627749 14771583254965995117703)
                  ·
                    rfl

theorem cell21_64727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 4].length) (baseStart_64727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64727 prefixEnd_64727 := by exact prefixLift 64727
  have htrace : WordTrace (prefixWord ++ tailWord_64727) baseStart_64727 baseEnd_64727 := by
    simpa [prefixWord, tailWord_64727, baseEnd_64727] using wordTrace_append hprefix tailTrace_64727
  have hstable : (prefixWord ++ tailWord_64727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64727).length < 2 ^ (prefixWord ++ tailWord_64727).sum := by decide
  have hdescent : baseEnd_64727 < baseStart_64727 := by decide
  rcases family_descends (prefixWord ++ tailWord_64727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64817 : List Nat := [1, 2, 2, 3, 3, 1, 9]
def baseStart_64817 : Nat := 118140960795 + 64817 * 2 ^ 59
def prefixEnd_64817 : Nat := 4983230072969 + 3 ^ 40 * 64817 * 2
def baseEnd_64817 : Nat := 1643569164571759846391

theorem tailTrace_64817 : CollatzResearch.WordTrace tailWord_64817 prefixEnd_64817 1643569164571759846391 := by
  unfold tailWord_64817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364070206186553707392705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576046804124369138261803 2364070206186553707392705)
  ·
    refine ⟨1773052654639915280544529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2364070206186553707392705 1773052654639915280544529)
    ·
      refine ⟨1329789490979936460408397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1773052654639915280544529 1329789490979936460408397)
      ·
        refine ⟨498671059117476172653149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1329789490979936460408397 498671059117476172653149)
        ·
          refine ⟨187001647169053564744931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498671059117476172653149 187001647169053564744931)
          ·
            refine ⟨280502470753580347117397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187001647169053564744931 280502470753580347117397)
            ·
              refine ⟨1643569164571759846391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 280502470753580347117397 1643569164571759846391)
              ·
                rfl

theorem cell21_64817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 9].length) (baseStart_64817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64817 prefixEnd_64817 := by exact prefixLift 64817
  have htrace : WordTrace (prefixWord ++ tailWord_64817) baseStart_64817 baseEnd_64817 := by
    simpa [prefixWord, tailWord_64817, baseEnd_64817] using wordTrace_append hprefix tailTrace_64817
  have hstable : (prefixWord ++ tailWord_64817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64817).length < 2 ^ (prefixWord ++ tailWord_64817).sum := by decide
  have hdescent : baseEnd_64817 < baseStart_64817 := by decide
  rcases family_descends (prefixWord ++ tailWord_64817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64820 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_64820 : Nat := 118140960795 + 64820 * 2 ^ 59
def prefixEnd_64820 : Nat := 4983230072969 + 3 ^ 40 * 64820 * 2
def baseEnd_64820 : Nat := 14792807122018500067513

theorem tailTrace_64820 : CollatzResearch.WordTrace tailWord_64820 prefixEnd_64820 14792807122018500067513 := by
  unfold tailWord_64820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182089812587842609875957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1576119750117123479834609 1182089812587842609875957)
  ·
    refine ⟨110820919930110244675871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1182089812587842609875957 110820919930110244675871)
    ·
      refine ⟨166231379895165367013807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110820919930110244675871 166231379895165367013807)
      ·
        refine ⟨249347069842748050520711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166231379895165367013807 249347069842748050520711)
        ·
          refine ⟨374020604764122075781067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249347069842748050520711 374020604764122075781067)
          ·
            refine ⟨561030907146183113671601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374020604764122075781067 561030907146183113671601)
            ·
              refine ⟨420773180359637335253701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561030907146183113671601 420773180359637335253701)
              ·
                refine ⟨78894971317432000360069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420773180359637335253701 78894971317432000360069)
                ·
                  refine ⟨14792807122018500067513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78894971317432000360069 14792807122018500067513)
                  ·
                    rfl

theorem cell21_64820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_64820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64820 prefixEnd_64820 := by exact prefixLift 64820
  have htrace : WordTrace (prefixWord ++ tailWord_64820) baseStart_64820 baseEnd_64820 := by
    simpa [prefixWord, tailWord_64820, baseEnd_64820] using wordTrace_append hprefix tailTrace_64820
  have hstable : (prefixWord ++ tailWord_64820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64820).length < 2 ^ (prefixWord ++ tailWord_64820).sum := by decide
  have hdescent : baseEnd_64820 < baseStart_64820 := by decide
  rcases family_descends (prefixWord ++ tailWord_64820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64879 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 4]
def baseStart_64879 : Nat := 118140960795 + 64879 * 2 ^ 59
def prefixEnd_64879 : Nat := 4983230072969 + 3 ^ 40 * 64879 * 2
def baseEnd_64879 : Nat := 14806271725847508584059

theorem tailTrace_64879 : CollatzResearch.WordTrace tailWord_64879 prefixEnd_64879 14806271725847508584059 := by
  unfold tailWord_64879
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366331531961938296149691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1577554354641292197433127 2366331531961938296149691)
  ·
    refine ⟨3549497297942907444224537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366331531961938296149691 3549497297942907444224537)
    ·
      refine ⟨2662122973457180583168403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549497297942907444224537 2662122973457180583168403)
      ·
        refine ⟨3993184460185770874752605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662122973457180583168403 3993184460185770874752605)
        ·
          refine ⟨1497444172569664078032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3993184460185770874752605 1497444172569664078032227)
          ·
            refine ⟨2246166258854496117048341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497444172569664078032227 2246166258854496117048341)
            ·
              refine ⟨105289043383804505486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2246166258854496117048341 105289043383804505486641)
              ·
                refine ⟨78966782537853379114981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105289043383804505486641 78966782537853379114981)
                ·
                  refine ⟨14806271725847508584059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78966782537853379114981 14806271725847508584059)
                  ·
                    rfl

theorem cell21_64879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 4].length) (baseStart_64879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64879 prefixEnd_64879 := by exact prefixLift 64879
  have htrace : WordTrace (prefixWord ++ tailWord_64879) baseStart_64879 baseEnd_64879 := by
    simpa [prefixWord, tailWord_64879, baseEnd_64879] using wordTrace_append hprefix tailTrace_64879
  have hstable : (prefixWord ++ tailWord_64879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64879).length < 2 ^ (prefixWord ++ tailWord_64879).sum := by decide
  have hdescent : baseEnd_64879 < baseStart_64879 := by decide
  rcases family_descends (prefixWord ++ tailWord_64879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64941 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_64941 : Nat := 118140960795 + 64941 * 2 ^ 59
def prefixEnd_64941 : Nat := 4983230072969 + 3 ^ 40 * 64941 * 2
def baseEnd_64941 : Nat := 14820420970549178550599

theorem tailTrace_64941 : CollatzResearch.WordTrace tailWord_64941 prefixEnd_64941 14820420970549178550599 := by
  unfold tailWord_64941
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368592857737322884906677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1579061905158215256604451 2368592857737322884906677)
  ·
    refine ⟨222055580412874020460001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2368592857737322884906677 222055580412874020460001)
    ·
      refine ⟨166541685309655515345001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222055580412874020460001 166541685309655515345001)
      ·
        refine ⟨124906263982241636508751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166541685309655515345001 124906263982241636508751)
        ·
          refine ⟨187359395973362454763127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124906263982241636508751 187359395973362454763127)
          ·
            refine ⟨281039093960043682144691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187359395973362454763127 281039093960043682144691)
            ·
              refine ⟨421558640940065523217037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281039093960043682144691 421558640940065523217037)
              ·
                refine ⟨158084490352524571206389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421558640940065523217037 158084490352524571206389)
                ·
                  refine ⟨14820420970549178550599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158084490352524571206389 14820420970549178550599)
                  ·
                    rfl

theorem cell21_64941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_64941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64941 prefixEnd_64941 := by exact prefixLift 64941
  have htrace : WordTrace (prefixWord ++ tailWord_64941) baseStart_64941 baseEnd_64941 := by
    simpa [prefixWord, tailWord_64941, baseEnd_64941] using wordTrace_append hprefix tailTrace_64941
  have hstable : (prefixWord ++ tailWord_64941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64941).length < 2 ^ (prefixWord ++ tailWord_64941).sum := by decide
  have hdescent : baseEnd_64941 < baseStart_64941 := by decide
  rcases family_descends (prefixWord ++ tailWord_64941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64983 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_64983 : Nat := 118140960795 + 64983 * 2 ^ 59
def prefixEnd_64983 : Nat := 4983230072969 + 3 ^ 40 * 64983 * 2
def baseEnd_64983 : Nat := 14830005942766438850513

theorem tailTrace_64983 : CollatzResearch.WordTrace tailWord_64983 prefixEnd_64983 14830005942766438850513 := by
  unfold tailWord_64983
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370124723585164057935603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1580083149056776038623735 2370124723585164057935603)
  ·
    refine ⟨3555187085377746086903405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370124723585164057935603 3555187085377746086903405)
    ·
      refine ⟨1333195157016654782588777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3555187085377746086903405 1333195157016654782588777)
      ·
        refine ⟨999896367762491086941583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333195157016654782588777 999896367762491086941583)
        ·
          refine ⟨1499844551643736630412375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999896367762491086941583 1499844551643736630412375)
          ·
            refine ⟨2249766827465604945618563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499844551643736630412375 2249766827465604945618563)
            ·
              refine ⟨3374650241198407418427845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2249766827465604945618563 3374650241198407418427845)
              ·
                refine ⟨632746920224701390955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3374650241198407418427845 632746920224701390955221)
                ·
                  refine ⟨14830005942766438850513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 632746920224701390955221 14830005942766438850513)
                  ·
                    rfl

theorem cell21_64983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_64983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_64983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_64983 prefixEnd_64983 := by exact prefixLift 64983
  have htrace : WordTrace (prefixWord ++ tailWord_64983) baseStart_64983 baseEnd_64983 := by
    simpa [prefixWord, tailWord_64983, baseEnd_64983] using wordTrace_append hprefix tailTrace_64983
  have hstable : (prefixWord ++ tailWord_64983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64983).length < 2 ^ (prefixWord ++ tailWord_64983).sum := by decide
  have hdescent : baseEnd_64983 < baseStart_64983 := by decide
  rcases family_descends (prefixWord ++ tailWord_64983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65048 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_65048 : Nat := 118140960795 + 65048 * 2 ^ 59
def prefixEnd_65048 : Nat := 4983230072969 + 3 ^ 40 * 65048 * 2
def baseEnd_65048 : Nat := 14844839828340770267047

theorem tailTrace_65048 : CollatzResearch.WordTrace tailWord_65048 prefixEnd_65048 14844839828340770267047 := by
  unfold tailWord_65048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186247734174840079525899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1581663645566453439367865 1186247734174840079525899)
  ·
    refine ⟨1779371601262260119288849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1186247734174840079525899 1779371601262260119288849)
    ·
      refine ⟨1334528700946695089466637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1779371601262260119288849 1334528700946695089466637)
      ·
        refine ⟨500448262855010658549989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1334528700946695089466637 500448262855010658549989)
        ·
          refine ⟨93834049285314498478123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 500448262855010658549989 93834049285314498478123)
          ·
            refine ⟨140751073927971747717185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93834049285314498478123 140751073927971747717185)
            ·
              refine ⟨105563305445978810787889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140751073927971747717185 105563305445978810787889)
              ·
                refine ⟨79172479084484108090917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105563305445978810787889 79172479084484108090917)
                ·
                  refine ⟨14844839828340770267047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79172479084484108090917 14844839828340770267047)
                  ·
                    rfl

theorem cell21_65048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_65048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65048 prefixEnd_65048 := by exact prefixLift 65048
  have htrace : WordTrace (prefixWord ++ tailWord_65048) baseStart_65048 baseEnd_65048 := by
    simpa [prefixWord, tailWord_65048, baseEnd_65048] using wordTrace_append hprefix tailTrace_65048
  have hstable : (prefixWord ++ tailWord_65048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65048).length < 2 ^ (prefixWord ++ tailWord_65048).sum := by decide
  have hdescent : baseEnd_65048 < baseStart_65048 := by decide
  rcases family_descends (prefixWord ++ tailWord_65048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65054 : List Nat := [4, 3, 3, 1, 2, 1, 1, 6]
def baseStart_65054 : Nat := 118140960795 + 65054 * 2 ^ 59
def prefixEnd_65054 : Nat := 4983230072969 + 3 ^ 40 * 65054 * 2
def baseEnd_65054 : Nat := 4948736370028697722345

theorem tailTrace_65054 : CollatzResearch.WordTrace tailWord_65054 prefixEnd_65054 4948736370028697722345 := by
  unfold tailWord_65054
  simp only [CollatzResearch.WordTrace]
  refine ⟨296589288290992897971277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1581809537551962122513477 296589288290992897971277)
  ·
    refine ⟨111220983109122336739229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 296589288290992897971277 111220983109122336739229)
    ·
      refine ⟨41707868665920876277211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111220983109122336739229 41707868665920876277211)
      ·
        refine ⟨62561802998881314415817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41707868665920876277211 62561802998881314415817)
        ·
          refine ⟨46921352249160985811863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62561802998881314415817 46921352249160985811863)
          ·
            refine ⟨70382028373741478717795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46921352249160985811863 70382028373741478717795)
            ·
              refine ⟨105573042560612218076693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70382028373741478717795 105573042560612218076693)
              ·
                refine ⟨4948736370028697722345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105573042560612218076693 4948736370028697722345)
                ·
                  rfl

theorem cell21_65054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_65054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65054 prefixEnd_65054 := by exact prefixLift 65054
  have htrace : WordTrace (prefixWord ++ tailWord_65054) baseStart_65054 baseEnd_65054 := by
    simpa [prefixWord, tailWord_65054, baseEnd_65054] using wordTrace_append hprefix tailTrace_65054
  have hstable : (prefixWord ++ tailWord_65054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65054).length < 2 ^ (prefixWord ++ tailWord_65054).sum := by decide
  have hdescent : baseEnd_65054 < baseStart_65054 := by decide
  rcases family_descends (prefixWord ++ tailWord_65054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65093 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 3]
def baseStart_65093 : Nat := 118140960795 + 65093 * 2 ^ 59
def prefixEnd_65093 : Nat := 4983230072969 + 3 ^ 40 * 65093 * 2
def baseEnd_65093 : Nat := 14855109441430692016955

theorem tailTrace_65093 : CollatzResearch.WordTrace tailWord_65093 prefixEnd_65093 14855109441430692016955 := by
  unfold tailWord_65093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374136753186652844439933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1582757835457768562959955 2374136753186652844439933)
  ·
    refine ⟨890301282444994816664975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2374136753186652844439933 890301282444994816664975)
    ·
      refine ⟨1335451923667492224997463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890301282444994816664975 1335451923667492224997463)
      ·
        refine ⟨2003177885501238337496195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335451923667492224997463 2003177885501238337496195)
        ·
          refine ⟨3004766828251857506244293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003177885501238337496195 3004766828251857506244293)
          ·
            refine ⟨563393780297223282420805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3004766828251857506244293 563393780297223282420805)
            ·
              refine ⟨105636333805729365453901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 563393780297223282420805 105636333805729365453901)
              ·
                refine ⟨39613625177148512045213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105636333805729365453901 39613625177148512045213)
                ·
                  refine ⟨14855109441430692016955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39613625177148512045213 14855109441430692016955)
                  ·
                    rfl

theorem cell21_65093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_65093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65093 prefixEnd_65093 := by exact prefixLift 65093
  have htrace : WordTrace (prefixWord ++ tailWord_65093) baseStart_65093 baseEnd_65093 := by
    simpa [prefixWord, tailWord_65093, baseEnd_65093] using wordTrace_append hprefix tailTrace_65093
  have hstable : (prefixWord ++ tailWord_65093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65093).length < 2 ^ (prefixWord ++ tailWord_65093).sum := by decide
  have hdescent : baseEnd_65093 < baseStart_65093 := by decide
  rcases family_descends (prefixWord ++ tailWord_65093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65104 : List Nat := [2, 1, 1, 1, 1, 3, 12]
def baseStart_65104 : Nat := 118140960795 + 65104 * 2 ^ 59
def prefixEnd_65104 : Nat := 4983230072969 + 3 ^ 40 * 65104 * 2
def baseEnd_65104 : Nat := 1650846643477457481511

theorem tailTrace_65104 : CollatzResearch.WordTrace tailWord_65104 prefixEnd_65104 1650846643477457481511 := by
  unfold tailWord_65104
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187268978073400861545183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1583025304097867815393577 1187268978073400861545183)
  ·
    refine ⟨1780903467110101292317775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1187268978073400861545183 1780903467110101292317775)
    ·
      refine ⟨2671355200665151938476663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780903467110101292317775 2671355200665151938476663)
      ·
        refine ⟨4007032800997727907714995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2671355200665151938476663 4007032800997727907714995)
        ·
          refine ⟨6010549201496591861572493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4007032800997727907714995 6010549201496591861572493)
          ·
            refine ⟨2253955950561221948089685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6010549201496591861572493 2253955950561221948089685)
            ·
              refine ⟨1650846643477457481511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 2253955950561221948089685 1650846643477457481511)
              ·
                rfl

theorem cell21_65104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 12].length) (baseStart_65104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65104 prefixEnd_65104 := by exact prefixLift 65104
  have htrace : WordTrace (prefixWord ++ tailWord_65104) baseStart_65104 baseEnd_65104 := by
    simpa [prefixWord, tailWord_65104, baseEnd_65104] using wordTrace_append hprefix tailTrace_65104
  have hstable : (prefixWord ++ tailWord_65104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65104).length < 2 ^ (prefixWord ++ tailWord_65104).sum := by decide
  have hdescent : baseEnd_65104 < baseStart_65104 := by decide
  rcases family_descends (prefixWord ++ tailWord_65104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65124 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_65124 : Nat := 118140960795 + 65124 * 2 ^ 59
def prefixEnd_65124 : Nat := 4983230072969 + 3 ^ 40 * 65124 * 2
def baseEnd_65124 : Nat := 14862184063781527000225

theorem tailTrace_65124 : CollatzResearch.WordTrace tailWord_65124 prefixEnd_65124 14862184063781527000225 := by
  unfold tailWord_65124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1187633708037172569409213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1583511610716230092545617 1187633708037172569409213)
  ·
    refine ⟨445362640513939713528455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1187633708037172569409213 445362640513939713528455)
    ·
      refine ⟨668043960770909570292683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445362640513939713528455 668043960770909570292683)
      ·
        refine ⟨1002065941156364355439025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668043960770909570292683 1002065941156364355439025)
        ·
          refine ⟨751549455867273266579269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002065941156364355439025 751549455867273266579269)
          ·
            refine ⟨140915522975113737483613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 751549455867273266579269 140915522975113737483613)
            ·
              refine ⟨52843321115667651556355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140915522975113737483613 52843321115667651556355)
              ·
                refine ⟨79264981673501477334533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52843321115667651556355 79264981673501477334533)
                ·
                  refine ⟨14862184063781527000225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79264981673501477334533 14862184063781527000225)
                  ·
                    rfl

theorem cell21_65124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_65124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65124 prefixEnd_65124 := by exact prefixLift 65124
  have htrace : WordTrace (prefixWord ++ tailWord_65124) baseStart_65124 baseEnd_65124 := by
    simpa [prefixWord, tailWord_65124, baseEnd_65124] using wordTrace_append hprefix tailTrace_65124
  have hstable : (prefixWord ++ tailWord_65124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65124).length < 2 ^ (prefixWord ++ tailWord_65124).sum := by decide
  have hdescent : baseEnd_65124 < baseStart_65124 := by decide
  rcases family_descends (prefixWord ++ tailWord_65124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65138 : List Nat := [3, 2, 1, 2, 3, 1, 4, 5]
def baseStart_65138 : Nat := 118140960795 + 65138 * 2 ^ 59
def prefixEnd_65138 : Nat := 4983230072969 + 3 ^ 40 * 65138 * 2
def baseEnd_65138 : Nat := 4955126351506871255621

theorem tailTrace_65138 : CollatzResearch.WordTrace tailWord_65138 prefixEnd_65138 4955126351506871255621 := by
  unfold tailWord_65138
  simp only [CollatzResearch.WordTrace]
  refine ⟨593944509505906382457017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1583852025349083686552045 593944509505906382457017)
  ·
    refine ⟨445458382129429786842763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 593944509505906382457017 445458382129429786842763)
    ·
      refine ⟨668187573194144680264145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445458382129429786842763 668187573194144680264145)
      ·
        refine ⟨501140679895608510198109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668187573194144680264145 501140679895608510198109)
        ·
          refine ⟨187927754960853191324291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501140679895608510198109 187927754960853191324291)
          ·
            refine ⟨281891632441279786986437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187927754960853191324291 281891632441279786986437)
            ·
              refine ⟨52854681082739960059957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281891632441279786986437 52854681082739960059957)
              ·
                refine ⟨4955126351506871255621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52854681082739960059957 4955126351506871255621)
                ·
                  rfl

theorem cell21_65138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_65138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65138 prefixEnd_65138 := by exact prefixLift 65138
  have htrace : WordTrace (prefixWord ++ tailWord_65138) baseStart_65138 baseEnd_65138 := by
    simpa [prefixWord, tailWord_65138, baseEnd_65138] using wordTrace_append hprefix tailTrace_65138
  have hstable : (prefixWord ++ tailWord_65138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65138).length < 2 ^ (prefixWord ++ tailWord_65138).sum := by decide
  have hdescent : baseEnd_65138 < baseStart_65138 := by decide
  rcases family_descends (prefixWord ++ tailWord_65138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65197 : List Nat := [1, 5, 2, 1, 1, 1, 1, 9]
def baseStart_65197 : Nat := 118140960795 + 65197 * 2 ^ 59
def prefixEnd_65197 : Nat := 4983230072969 + 3 ^ 40 * 65197 * 2
def baseEnd_65197 : Nat := 4959614552783207427803

theorem tailTrace_65197 : CollatzResearch.WordTrace tailWord_65197 prefixEnd_65197 4959614552783207427803 := by
  unfold tailWord_65197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377929944809878606225845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1585286629873252404150563 2377929944809878606225845)
  ·
    refine ⟨222930932325926119333673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2377929944809878606225845 222930932325926119333673)
    ·
      refine ⟨167198199244444589500255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222930932325926119333673 167198199244444589500255)
      ·
        refine ⟨250797298866666884250383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167198199244444589500255 250797298866666884250383)
        ·
          refine ⟨376195948300000326375575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250797298866666884250383 376195948300000326375575)
          ·
            refine ⟨564293922450000489563363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376195948300000326375575 564293922450000489563363)
            ·
              refine ⟨846440883675000734345045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564293922450000489563363 846440883675000734345045)
              ·
                refine ⟨4959614552783207427803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 846440883675000734345045 4959614552783207427803)
                ·
                  rfl

theorem cell21_65197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_65197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65197 prefixEnd_65197 := by exact prefixLift 65197
  have htrace : WordTrace (prefixWord ++ tailWord_65197) baseStart_65197 baseEnd_65197 := by
    simpa [prefixWord, tailWord_65197, baseEnd_65197] using wordTrace_append hprefix tailTrace_65197
  have hstable : (prefixWord ++ tailWord_65197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65197).length < 2 ^ (prefixWord ++ tailWord_65197).sum := by decide
  have hdescent : baseEnd_65197 < baseStart_65197 := by decide
  rcases family_descends (prefixWord ++ tailWord_65197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65338 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_65338 : Nat := 118140960795 + 65338 * 2 ^ 59
def prefixEnd_65338 : Nat := 4983230072969 + 3 ^ 40 * 65338 * 2
def baseEnd_65338 : Nat := 14911021779364710433121

theorem tailTrace_65338 : CollatzResearch.WordTrace tailWord_65338 prefixEnd_65338 14911021779364710433121 := by
  unfold tailWord_65338
  simp only [CollatzResearch.WordTrace]
  refine ⟨595768159324764921777167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1588715091532706458072445 595768159324764921777167)
  ·
    refine ⟨893652238987147382665751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 595768159324764921777167 893652238987147382665751)
    ·
      refine ⟨1340478358480721073998627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893652238987147382665751 1340478358480721073998627)
      ·
        refine ⟨2010717537721081610997941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340478358480721073998627 2010717537721081610997941)
        ·
          refine ⟨188504769161351401031057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2010717537721081610997941 188504769161351401031057)
          ·
            refine ⟨141378576871013550773293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188504769161351401031057 141378576871013550773293)
            ·
              refine ⟨53016966326630081539985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141378576871013550773293 53016966326630081539985)
              ·
                refine ⟨39762724744972561154989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53016966326630081539985 39762724744972561154989)
                ·
                  refine ⟨14911021779364710433121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39762724744972561154989 14911021779364710433121)
                  ·
                    rfl

theorem cell21_65338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_65338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65338 prefixEnd_65338 := by exact prefixLift 65338
  have htrace : WordTrace (prefixWord ++ tailWord_65338) baseStart_65338 baseEnd_65338 := by
    simpa [prefixWord, tailWord_65338, baseEnd_65338] using wordTrace_append hprefix tailTrace_65338
  have hstable : (prefixWord ++ tailWord_65338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65338).length < 2 ^ (prefixWord ++ tailWord_65338).sum := by decide
  have hdescent : baseEnd_65338 < baseStart_65338 := by decide
  rcases family_descends (prefixWord ++ tailWord_65338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65352 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_65352 : Nat := 118140960795 + 65352 * 2 ^ 59
def prefixEnd_65352 : Nat := 4983230072969 + 3 ^ 40 * 65352 * 2
def baseEnd_65352 : Nat := 14914216770103797199759

theorem tailTrace_65352 : CollatzResearch.WordTrace tailWord_65352 prefixEnd_65352 14914216770103797199759 := by
  unfold tailWord_65352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191791629624170039059155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1589055506165560052078873 1191791629624170039059155)
  ·
    refine ⟨1787687444436255058588733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191791629624170039059155 1787687444436255058588733)
    ·
      refine ⟨670382791663595646970775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1787687444436255058588733 670382791663595646970775)
      ·
        refine ⟨1005574187495393470456163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670382791663595646970775 1005574187495393470456163)
        ·
          refine ⟨1508361281243090205684245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005574187495393470456163 1508361281243090205684245)
          ·
            refine ⟨70704435058269853391449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1508361281243090205684245 70704435058269853391449)
            ·
              refine ⟨53028326293702390043587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70704435058269853391449 53028326293702390043587)
              ·
                refine ⟨79542489440553585065381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53028326293702390043587 79542489440553585065381)
                ·
                  refine ⟨14914216770103797199759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79542489440553585065381 14914216770103797199759)
                  ·
                    rfl

theorem cell21_65352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_65352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65352 prefixEnd_65352 := by exact prefixLift 65352
  have htrace : WordTrace (prefixWord ++ tailWord_65352) baseStart_65352 baseEnd_65352 := by
    simpa [prefixWord, tailWord_65352, baseEnd_65352] using wordTrace_append hprefix tailTrace_65352
  have hstable : (prefixWord ++ tailWord_65352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65352).length < 2 ^ (prefixWord ++ tailWord_65352).sum := by decide
  have hdescent : baseEnd_65352 < baseStart_65352 := by decide
  rcases family_descends (prefixWord ++ tailWord_65352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65397 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 3]
def baseStart_65397 : Nat := 118140960795 + 65397 * 2 ^ 59
def prefixEnd_65397 : Nat := 4983230072969 + 3 ^ 40 * 65397 * 2
def baseEnd_65397 : Nat := 14924486383193718949667

theorem tailTrace_65397 : CollatzResearch.WordTrace tailWord_65397 prefixEnd_65397 14924486383193718949667 := by
  unfold tailWord_65397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385224544085312763506445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1590149696056875175670963 2385224544085312763506445)
  ·
    refine ⟨894459204031992286314917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2385224544085312763506445 894459204031992286314917)
    ·
      refine ⟨167711100755998553684047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 894459204031992286314917 167711100755998553684047)
      ·
        refine ⟨251566651133997830526071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167711100755998553684047 251566651133997830526071)
        ·
          refine ⟨377349976700996745789107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251566651133997830526071 377349976700996745789107)
          ·
            refine ⟨566024965051495118683661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377349976700996745789107 566024965051495118683661)
            ·
              refine ⟨212259361894310669506373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566024965051495118683661 212259361894310669506373)
              ·
                refine ⟨39798630355183250532445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212259361894310669506373 39798630355183250532445)
                ·
                  refine ⟨14924486383193718949667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39798630355183250532445 14924486383193718949667)
                  ·
                    rfl

theorem cell21_65397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_65397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65397 prefixEnd_65397 := by exact prefixLift 65397
  have htrace : WordTrace (prefixWord ++ tailWord_65397) baseStart_65397 baseEnd_65397 := by
    simpa [prefixWord, tailWord_65397, baseEnd_65397] using wordTrace_append hprefix tailTrace_65397
  have hstable : (prefixWord ++ tailWord_65397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65397).length < 2 ^ (prefixWord ++ tailWord_65397).sum := by decide
  have hdescent : baseEnd_65397 < baseStart_65397 := by decide
  rcases family_descends (prefixWord ++ tailWord_65397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65521 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 4]
def baseStart_65521 : Nat := 118140960795 + 65521 * 2 ^ 59
def prefixEnd_65521 : Nat := 4983230072969 + 3 ^ 40 * 65521 * 2
def baseEnd_65521 : Nat := 14952784872597058882747

theorem tailTrace_65521 : CollatzResearch.WordTrace tailWord_65521 prefixEnd_65521 14952784872597058882747 := by
  unfold tailWord_65521
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389747195636081941020417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1593164797090721294013611 2389747195636081941020417)
  ·
    refine ⟨1792310396727061455765313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2389747195636081941020417 1792310396727061455765313)
    ·
      refine ⟨1344232797545296091823985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792310396727061455765313 1344232797545296091823985)
      ·
        refine ⟨1008174598158972068867989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344232797545296091823985 1008174598158972068867989)
        ·
          refine ⟨47258184288701815728187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1008174598158972068867989 47258184288701815728187)
          ·
            refine ⟨70887276433052723592281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47258184288701815728187 70887276433052723592281)
            ·
              refine ⟨53165457324789542694211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70887276433052723592281 53165457324789542694211)
              ·
                refine ⟨79748185987184314041317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53165457324789542694211 79748185987184314041317)
                ·
                  refine ⟨14952784872597058882747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79748185987184314041317 14952784872597058882747)
                  ·
                    rfl

theorem cell21_65521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 4].length) (baseStart_65521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65521 prefixEnd_65521 := by exact prefixLift 65521
  have htrace : WordTrace (prefixWord ++ tailWord_65521) baseStart_65521 baseEnd_65521 := by
    simpa [prefixWord, tailWord_65521, baseEnd_65521] using wordTrace_append hprefix tailTrace_65521
  have hstable : (prefixWord ++ tailWord_65521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65521).length < 2 ^ (prefixWord ++ tailWord_65521).sum := by decide
  have hdescent : baseEnd_65521 < baseStart_65521 := by decide
  rcases family_descends (prefixWord ++ tailWord_65521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65605 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 6]
def baseStart_65605 : Nat := 118140960795 + 65605 * 2 ^ 59
def prefixEnd_65605 : Nat := 4983230072969 + 3 ^ 40 * 65605 * 2
def baseEnd_65605 : Nat := 14971954817031579482575

theorem tailTrace_65605 : CollatzResearch.WordTrace tailWord_65605 prefixEnd_65605 14971954817031579482575 := by
  unfold tailWord_65605
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392810927331764287078269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1595207284887842858052179 2392810927331764287078269)
  ·
    refine ⟨897304097749411607654351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2392810927331764287078269 897304097749411607654351)
    ·
      refine ⟨1345956146624117411481527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897304097749411607654351 1345956146624117411481527)
      ·
        refine ⟨2018934219936176117222291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345956146624117411481527 2018934219936176117222291)
        ·
          refine ⟨3028401329904264175833437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018934219936176117222291 3028401329904264175833437)
          ·
            refine ⟨1135650498714099065937539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3028401329904264175833437 1135650498714099065937539)
            ·
              refine ⟨1703475748071148598906309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135650498714099065937539 1703475748071148598906309)
              ·
                refine ⟨319401702763340362294933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1703475748071148598906309 319401702763340362294933)
                ·
                  refine ⟨14971954817031579482575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319401702763340362294933 14971954817031579482575)
                  ·
                    rfl

theorem cell21_65605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_65605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65605 prefixEnd_65605 := by exact prefixLift 65605
  have htrace : WordTrace (prefixWord ++ tailWord_65605) baseStart_65605 baseEnd_65605 := by
    simpa [prefixWord, tailWord_65605, baseEnd_65605] using wordTrace_append hprefix tailTrace_65605
  have hstable : (prefixWord ++ tailWord_65605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65605).length < 2 ^ (prefixWord ++ tailWord_65605).sum := by decide
  have hdescent : baseEnd_65605 < baseStart_65605 := by decide
  rcases family_descends (prefixWord ++ tailWord_65605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65639 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 4]
def baseStart_65639 : Nat := 118140960795 + 65639 * 2 ^ 59
def prefixEnd_65639 : Nat := 4983230072969 + 3 ^ 40 * 65639 * 2
def baseEnd_65639 : Nat := 14979714080255075915839

theorem tailTrace_65639 : CollatzResearch.WordTrace tailWord_65639 prefixEnd_65639 14979714080255075915839 := by
  unfold tailWord_65639
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394051009208588093815971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1596034006139058729210647 2394051009208588093815971)
  ·
    refine ⟨3591076513812882140723957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2394051009208588093815971 3591076513812882140723957)
    ·
      refine ⟨336663423169957700692871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3591076513812882140723957 336663423169957700692871)
      ·
        refine ⟨504995134754936551039307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336663423169957700692871 504995134754936551039307)
        ·
          refine ⟨757492702132404826558961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504995134754936551039307 757492702132404826558961)
          ·
            refine ⟨568119526599303619919221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757492702132404826558961 568119526599303619919221)
            ·
              refine ⟨53261205618684714367427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 568119526599303619919221 53261205618684714367427)
              ·
                refine ⟨79891808428027071551141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53261205618684714367427 79891808428027071551141)
                ·
                  refine ⟨14979714080255075915839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79891808428027071551141 14979714080255075915839)
                  ·
                    rfl

theorem cell21_65639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 4].length) (baseStart_65639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65639 prefixEnd_65639 := by exact prefixLift 65639
  have htrace : WordTrace (prefixWord ++ tailWord_65639) baseStart_65639 baseEnd_65639 := by
    simpa [prefixWord, tailWord_65639, baseEnd_65639] using wordTrace_append hprefix tailTrace_65639
  have hstable : (prefixWord ++ tailWord_65639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65639).length < 2 ^ (prefixWord ++ tailWord_65639).sum := by decide
  have hdescent : baseEnd_65639 < baseStart_65639 := by decide
  rcases family_descends (prefixWord ++ tailWord_65639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65729 : List Nat := [1, 2, 6, 1, 2, 9]
def baseStart_65729 : Nat := 118140960795 + 65729 * 2 ^ 59
def prefixEnd_65729 : Nat := 4983230072969 + 3 ^ 40 * 65729 * 2
def baseEnd_65729 : Nat := 555564937275367385765

theorem tailTrace_65729 : CollatzResearch.WordTrace tailWord_65729 prefixEnd_65729 555564937275367385765 := by
  unfold tailWord_65729
  simp only [CollatzResearch.WordTrace]
  refine ⟨2397333578882533464592241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1598222385921688976394827 2397333578882533464592241)
  ·
    refine ⟨1798000184161900098444181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2397333578882533464592241 1798000184161900098444181)
    ·
      refine ⟨84281258632589067114571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1798000184161900098444181 84281258632589067114571)
      ·
        refine ⟨126421887948883600671857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84281258632589067114571 126421887948883600671857)
        ·
          refine ⟨94816415961662700503893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126421887948883600671857 94816415961662700503893)
          ·
            refine ⟨555564937275367385765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 94816415961662700503893 555564937275367385765)
            ·
              rfl

theorem cell21_65729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 9].length) (baseStart_65729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65729 prefixEnd_65729 := by exact prefixLift 65729
  have htrace : WordTrace (prefixWord ++ tailWord_65729) baseStart_65729 baseEnd_65729 := by
    simpa [prefixWord, tailWord_65729, baseEnd_65729] using wordTrace_append hprefix tailTrace_65729
  have hstable : (prefixWord ++ tailWord_65729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65729).length < 2 ^ (prefixWord ++ tailWord_65729).sum := by decide
  have hdescent : baseEnd_65729 < baseStart_65729 := by decide
  rcases family_descends (prefixWord ++ tailWord_65729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65788 : List Nat := [2, 2, 2, 1, 4, 2, 8]
def baseStart_65788 : Nat := 118140960795 + 65788 * 2 ^ 59
def prefixEnd_65788 : Nat := 4983230072969 + 3 ^ 40 * 65788 * 2
def baseEnd_65788 : Nat := 1668190878918214214689

theorem tailTrace_65788 : CollatzResearch.WordTrace tailWord_65788 prefixEnd_65788 1668190878918214214689 := by
  unfold tailWord_65788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1199742742834393270495009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1599656990445857693993345 1199742742834393270495009)
  ·
    refine ⟨899807057125794952871257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1199742742834393270495009 899807057125794952871257)
    ·
      refine ⟨674855292844346214653443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 899807057125794952871257 674855292844346214653443)
      ·
        refine ⟨1012282939266519321980165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674855292844346214653443 1012282939266519321980165)
        ·
          refine ⟨189803051112472372871281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1012282939266519321980165 189803051112472372871281)
          ·
            refine ⟨142352288334354279653461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189803051112472372871281 142352288334354279653461)
            ·
              refine ⟨1668190878918214214689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 142352288334354279653461 1668190878918214214689)
              ·
                rfl

theorem cell21_65788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 8].length) (baseStart_65788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65788 prefixEnd_65788 := by exact prefixLift 65788
  have htrace : WordTrace (prefixWord ++ tailWord_65788) baseStart_65788 baseEnd_65788 := by
    simpa [prefixWord, tailWord_65788, baseEnd_65788] using wordTrace_append hprefix tailTrace_65788
  have hstable : (prefixWord ++ tailWord_65788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65788).length < 2 ^ (prefixWord ++ tailWord_65788).sum := by decide
  have hdescent : baseEnd_65788 < baseStart_65788 := by decide
  rcases family_descends (prefixWord ++ tailWord_65788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65822 : List Nat := [4, 3, 2, 1, 1, 2, 1, 7]
def baseStart_65822 : Nat := 118140960795 + 65822 * 2 ^ 59
def prefixEnd_65822 : Nat := 4983230072969 + 3 ^ 40 * 65822 * 2
def baseEnd_65822 : Nat := 5007159057829141455155

theorem tailTrace_65822 : CollatzResearch.WordTrace tailWord_65822 prefixEnd_65822 5007159057829141455155 := by
  unfold tailWord_65822
  simp only [CollatzResearch.WordTrace]
  refine ⟨300090695943201293465965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1600483711697073565151813 300090695943201293465965)
  ·
    refine ⟨112534010978700485049737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 300090695943201293465965 112534010978700485049737)
    ·
      refine ⟨84400508234025363787303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112534010978700485049737 84400508234025363787303)
      ·
        refine ⟨126600762351038045680955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84400508234025363787303 126600762351038045680955)
        ·
          refine ⟨189901143526557068521433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126600762351038045680955 189901143526557068521433)
          ·
            refine ⟨142425857644917801391075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189901143526557068521433 142425857644917801391075)
            ·
              refine ⟨213638786467376702086613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142425857644917801391075 213638786467376702086613)
              ·
                refine ⟨5007159057829141455155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213638786467376702086613 5007159057829141455155)
                ·
                  rfl

theorem cell21_65822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_65822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65822 prefixEnd_65822 := by exact prefixLift 65822
  have htrace : WordTrace (prefixWord ++ tailWord_65822) baseStart_65822 baseEnd_65822 := by
    simpa [prefixWord, tailWord_65822, baseEnd_65822] using wordTrace_append hprefix tailTrace_65822
  have hstable : (prefixWord ++ tailWord_65822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65822).length < 2 ^ (prefixWord ++ tailWord_65822).sum := by decide
  have hdescent : baseEnd_65822 < baseStart_65822 := by decide
  rcases family_descends (prefixWord ++ tailWord_65822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65836 : List Nat := [2, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_65836 : Nat := 118140960795 + 65836 * 2 ^ 59
def prefixEnd_65836 : Nat := 4983230072969 + 3 ^ 40 * 65836 * 2
def baseEnd_65836 : Nat := 15024672164226511132103

theorem tailTrace_65836 : CollatzResearch.WordTrace tailWord_65836 prefixEnd_65836 15024672164226511132103 := by
  unfold tailWord_65836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200618094747445369368681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1600824126329927159158241 1200618094747445369368681)
  ·
    refine ⟨900463571060584027026511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1200618094747445369368681 900463571060584027026511)
    ·
      refine ⟨1350695356590876040539767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900463571060584027026511 1350695356590876040539767)
      ·
        refine ⟨2026043034886314060809651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350695356590876040539767 2026043034886314060809651)
        ·
          refine ⟨3039064552329471091214477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026043034886314060809651 3039064552329471091214477)
          ·
            refine ⟨1139649207123551659205429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3039064552329471091214477 1139649207123551659205429)
            ·
              refine ⟨106842113167832968050509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1139649207123551659205429 106842113167832968050509)
              ·
                refine ⟨40065792437937363018941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106842113167832968050509 40065792437937363018941)
                ·
                  refine ⟨15024672164226511132103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40065792437937363018941 15024672164226511132103)
                  ·
                    rfl

theorem cell21_65836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_65836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65836 prefixEnd_65836 := by exact prefixLift 65836
  have htrace : WordTrace (prefixWord ++ tailWord_65836) baseStart_65836 baseEnd_65836 := by
    simpa [prefixWord, tailWord_65836, baseEnd_65836] using wordTrace_append hprefix tailTrace_65836
  have hstable : (prefixWord ++ tailWord_65836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65836).length < 2 ^ (prefixWord ++ tailWord_65836).sum := by decide
  have hdescent : baseEnd_65836 < baseStart_65836 := by decide
  rcases family_descends (prefixWord ++ tailWord_65836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65960 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_65960 : Nat := 118140960795 + 65960 * 2 ^ 59
def prefixEnd_65960 : Nat := 4983230072969 + 3 ^ 40 * 65960 * 2
def baseEnd_65960 : Nat := 15052970653629851065183

theorem tailTrace_65960 : CollatzResearch.WordTrace tailWord_65960 prefixEnd_65960 15052970653629851065183 := by
  unfold tailWord_65960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1202879420522829958125667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1603839227363773277500889 1202879420522829958125667)
  ·
    refine ⟨1804319130784244937188501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1202879420522829958125667 1804319130784244937188501)
    ·
      refine ⟨84577459255511481430711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1804319130784244937188501 84577459255511481430711)
      ·
        refine ⟨126866188883267222146067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84577459255511481430711 126866188883267222146067)
        ·
          refine ⟨190299283324900833219101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126866188883267222146067 190299283324900833219101)
          ·
            refine ⟨71362231246837812457163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190299283324900833219101 71362231246837812457163)
            ·
              refine ⟨107043346870256718685745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71362231246837812457163 107043346870256718685745)
              ·
                refine ⟨80282510152692539014309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107043346870256718685745 80282510152692539014309)
                ·
                  refine ⟨15052970653629851065183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80282510152692539014309 15052970653629851065183)
                  ·
                    rfl

theorem cell21_65960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_65960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_65960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_65960 prefixEnd_65960 := by exact prefixLift 65960
  have htrace : WordTrace (prefixWord ++ tailWord_65960) baseStart_65960 baseEnd_65960 := by
    simpa [prefixWord, tailWord_65960, baseEnd_65960] using wordTrace_append hprefix tailTrace_65960
  have hstable : (prefixWord ++ tailWord_65960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65960).length < 2 ^ (prefixWord ++ tailWord_65960).sum := by decide
  have hdescent : baseEnd_65960 < baseStart_65960 := by decide
  rcases family_descends (prefixWord ++ tailWord_65960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66005 : List Nat := [1, 3, 2, 3, 1, 4, 1, 3, 3]
def baseStart_66005 : Nat := 118140960795 + 66005 * 2 ^ 59
def prefixEnd_66005 : Nat := 4983230072969 + 3 ^ 40 * 66005 * 2
def baseEnd_66005 : Nat := 15063240266719772815091

theorem tailTrace_66005 : CollatzResearch.WordTrace tailWord_66005 prefixEnd_66005 15063240266719772815091 := by
  unfold tailWord_66005
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407400125882632601639469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1604933417255088401092979 2407400125882632601639469)
  ·
    refine ⟨902775047205987225614801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2407400125882632601639469 902775047205987225614801)
    ·
      refine ⟨677081285404490419211101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 902775047205987225614801 677081285404490419211101)
      ·
        refine ⟨253905482026683907204163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 677081285404490419211101 253905482026683907204163)
        ·
          refine ⟨380858223040025860806245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253905482026683907204163 380858223040025860806245)
          ·
            refine ⟨71410916820004848901171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 380858223040025860806245 71410916820004848901171)
            ·
              refine ⟨107116375230007273351757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71410916820004848901171 107116375230007273351757)
              ·
                refine ⟨40168640711252727506909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107116375230007273351757 40168640711252727506909)
                ·
                  refine ⟨15063240266719772815091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40168640711252727506909 15063240266719772815091)
                  ·
                    rfl

theorem cell21_66005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_66005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66005 prefixEnd_66005 := by exact prefixLift 66005
  have htrace : WordTrace (prefixWord ++ tailWord_66005) baseStart_66005 baseEnd_66005 := by
    simpa [prefixWord, tailWord_66005, baseEnd_66005] using wordTrace_append hprefix tailTrace_66005
  have hstable : (prefixWord ++ tailWord_66005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66005).length < 2 ^ (prefixWord ++ tailWord_66005).sum := by decide
  have hdescent : baseEnd_66005 < baseStart_66005 := by decide
  rcases family_descends (prefixWord ++ tailWord_66005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66106 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_66106 : Nat := 118140960795 + 66106 * 2 ^ 59
def prefixEnd_66106 : Nat := 4983230072969 + 3 ^ 40 * 66106 * 2
def baseEnd_66106 : Nat := 15086289842766041631551

theorem tailTrace_66106 : CollatzResearch.WordTrace tailWord_66106 prefixEnd_66106 15086289842766041631551 := by
  unfold tailWord_66106
  simp only [CollatzResearch.WordTrace]
  refine ⟨602770974629181712766543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1607389265677817900710781 602770974629181712766543)
  ·
    refine ⟨904156461943772569149815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602770974629181712766543 904156461943772569149815)
    ·
      refine ⟨1356234692915658853724723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904156461943772569149815 1356234692915658853724723)
      ·
        refine ⟨2034352039373488280587085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1356234692915658853724723 2034352039373488280587085)
        ·
          refine ⟨762882014765058105220157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2034352039373488280587085 762882014765058105220157)
          ·
            refine ⟨286080755536896789457559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762882014765058105220157 286080755536896789457559)
            ·
              refine ⟨429121133305345184186339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286080755536896789457559 429121133305345184186339)
              ·
                refine ⟨643681699958017776279509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 429121133305345184186339 643681699958017776279509)
                ·
                  refine ⟨15086289842766041631551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 643681699958017776279509 15086289842766041631551)
                  ·
                    rfl

theorem cell21_66106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_66106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66106 prefixEnd_66106 := by exact prefixLift 66106
  have htrace : WordTrace (prefixWord ++ tailWord_66106) baseStart_66106 baseEnd_66106 := by
    simpa [prefixWord, tailWord_66106, baseEnd_66106] using wordTrace_append hprefix tailTrace_66106
  have hstable : (prefixWord ++ tailWord_66106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66106).length < 2 ^ (prefixWord ++ tailWord_66106).sum := by decide
  have hdescent : baseEnd_66106 < baseStart_66106 := by decide
  rcases family_descends (prefixWord ++ tailWord_66106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66109 : List Nat := [1, 4, 1, 3, 2, 2, 3, 5]
def baseStart_66109 : Nat := 118140960795 + 66109 * 2 ^ 59
def prefixEnd_66109 : Nat := 4983230072969 + 3 ^ 40 * 66109 * 2
def baseEnd_66109 : Nat := 5028991494546234360515

theorem tailTrace_66109 : CollatzResearch.WordTrace tailWord_66109 prefixEnd_66109 5028991494546234360515 := by
  unfold tailWord_66109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411193317505858363425381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1607462211670572242283587 2411193317505858363425381)
  ·
    refine ⟨452098747032348443142259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2411193317505858363425381 452098747032348443142259)
    ·
      refine ⟨678148120548522664713389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452098747032348443142259 678148120548522664713389)
      ·
        refine ⟨254305545205695999267521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678148120548522664713389 254305545205695999267521)
        ·
          refine ⟨190729158904271999450641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254305545205695999267521 190729158904271999450641)
          ·
            refine ⟨143046869178203999587981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190729158904271999450641 143046869178203999587981)
            ·
              refine ⟨53642575941826499845493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143046869178203999587981 53642575941826499845493)
              ·
                refine ⟨5028991494546234360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53642575941826499845493 5028991494546234360515)
                ·
                  rfl

theorem cell21_66109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 5].length) (baseStart_66109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66109 prefixEnd_66109 := by exact prefixLift 66109
  have htrace : WordTrace (prefixWord ++ tailWord_66109) baseStart_66109 baseEnd_66109 := by
    simpa [prefixWord, tailWord_66109, baseEnd_66109] using wordTrace_append hprefix tailTrace_66109
  have hstable : (prefixWord ++ tailWord_66109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66109).length < 2 ^ (prefixWord ++ tailWord_66109).sum := by decide
  have hdescent : baseEnd_66109 < baseStart_66109 := by decide
  rcases family_descends (prefixWord ++ tailWord_66109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66123 : List Nat := [1, 1, 1, 1, 3, 1, 5, 5, 3]
def baseStart_66123 : Nat := 118140960795 + 66123 * 2 ^ 59
def prefixEnd_66123 : Nat := 4983230072969 + 3 ^ 40 * 66123 * 2
def baseEnd_66123 : Nat := 15090169474377789848183

theorem tailTrace_66123 : CollatzResearch.WordTrace tailWord_66123 prefixEnd_66123 15090169474377789848183 := by
  unfold tailWord_66123
  simp only [CollatzResearch.WordTrace]
  refine ⟨2411703939455138754435023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1607802626303425836290015 2411703939455138754435023)
  ·
    refine ⟨3617555909182708131652535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2411703939455138754435023 3617555909182708131652535)
    ·
      refine ⟨5426333863774062197478803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3617555909182708131652535 5426333863774062197478803)
      ·
        refine ⟨8139500795661093296218205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5426333863774062197478803 8139500795661093296218205)
        ·
          refine ⟨3052312798372909986081827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8139500795661093296218205 3052312798372909986081827)
          ·
            refine ⟨4578469197559364979122741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052312798372909986081827 4578469197559364979122741)
            ·
              refine ⟨429231487271190466792757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4578469197559364979122741 429231487271190466792757)
              ·
                refine ⟨40240451931674106261821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429231487271190466792757 40240451931674106261821)
                ·
                  refine ⟨15090169474377789848183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40240451931674106261821 15090169474377789848183)
                  ·
                    rfl

theorem cell21_66123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 5, 3].length) (baseStart_66123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66123 prefixEnd_66123 := by exact prefixLift 66123
  have htrace : WordTrace (prefixWord ++ tailWord_66123) baseStart_66123 baseEnd_66123 := by
    simpa [prefixWord, tailWord_66123, baseEnd_66123] using wordTrace_append hprefix tailTrace_66123
  have hstable : (prefixWord ++ tailWord_66123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66123).length < 2 ^ (prefixWord ++ tailWord_66123).sum := by decide
  have hdescent : baseEnd_66123 < baseStart_66123 := by decide
  rcases family_descends (prefixWord ++ tailWord_66123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66140 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_66140 : Nat := 118140960795 + 66140 * 2 ^ 59
def prefixEnd_66140 : Nat := 4983230072969 + 3 ^ 40 * 66140 * 2
def baseEnd_66140 : Nat := 15094049105989538064815

theorem tailTrace_66140 : CollatzResearch.WordTrace tailWord_66140 prefixEnd_66140 15094049105989538064815 := by
  unfold tailWord_66140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206161990196775328901937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1608215986929033771869249 1206161990196775328901937)
  ·
    refine ⟨904621492647581496676453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1206161990196775328901937 904621492647581496676453)
    ·
      refine ⟨169616529871421530626835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 904621492647581496676453 169616529871421530626835)
      ·
        refine ⟨254424794807132295940253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169616529871421530626835 254424794807132295940253)
        ·
          refine ⟨95409298052674610977595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254424794807132295940253 95409298052674610977595)
          ·
            refine ⟨143113947079011916466393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95409298052674610977595 143113947079011916466393)
            ·
              refine ⟨107335460309258937349795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143113947079011916466393 107335460309258937349795)
              ·
                refine ⟨161003190463888406024693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107335460309258937349795 161003190463888406024693)
                ·
                  refine ⟨15094049105989538064815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161003190463888406024693 15094049105989538064815)
                  ·
                    rfl

theorem cell21_66140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_66140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66140 prefixEnd_66140 := by exact prefixLift 66140
  have htrace : WordTrace (prefixWord ++ tailWord_66140) baseStart_66140 baseEnd_66140 := by
    simpa [prefixWord, tailWord_66140, baseEnd_66140] using wordTrace_append hprefix tailTrace_66140
  have hstable : (prefixWord ++ tailWord_66140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66140).length < 2 ^ (prefixWord ++ tailWord_66140).sum := by decide
  have hdescent : baseEnd_66140 < baseStart_66140 := by decide
  rcases family_descends (prefixWord ++ tailWord_66140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66151 : List Nat := [1, 1, 5, 1, 1, 1, 1, 10]
def baseStart_66151 : Nat := 118140960795 + 66151 * 2 ^ 59
def prefixEnd_66151 : Nat := 4983230072969 + 3 ^ 40 * 66151 * 2
def baseEnd_66151 : Nat := 5032186485285321127153

theorem tailTrace_66151 : CollatzResearch.WordTrace tailWord_66151 prefixEnd_66151 5032186485285321127153 := by
  unfold tailWord_66151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412725183353699536454307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1608483455569133024302871 2412725183353699536454307)
  ·
    refine ⟨3619087775030549304681461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2412725183353699536454307 3619087775030549304681461)
    ·
      refine ⟨339289478909113997313887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3619087775030549304681461 339289478909113997313887)
      ·
        refine ⟨508934218363670995970831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339289478909113997313887 508934218363670995970831)
        ·
          refine ⟨763401327545506493956247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508934218363670995970831 763401327545506493956247)
          ·
            refine ⟨1145101991318259740934371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763401327545506493956247 1145101991318259740934371)
            ·
              refine ⟨1717652986977389611401557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145101991318259740934371 1717652986977389611401557)
              ·
                refine ⟨5032186485285321127153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1717652986977389611401557 5032186485285321127153)
                ·
                  rfl

theorem cell21_66151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_66151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66151 prefixEnd_66151 := by exact prefixLift 66151
  have htrace : WordTrace (prefixWord ++ tailWord_66151) baseStart_66151 baseEnd_66151 := by
    simpa [prefixWord, tailWord_66151, baseEnd_66151] using wordTrace_append hprefix tailTrace_66151
  have hstable : (prefixWord ++ tailWord_66151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66151).length < 2 ^ (prefixWord ++ tailWord_66151).sum := by decide
  have hdescent : baseEnd_66151 < baseStart_66151 := by decide
  rcases family_descends (prefixWord ++ tailWord_66151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66227 : List Nat := [1, 1, 1, 2, 3, 4, 2, 7]
def baseStart_66227 : Nat := 118140960795 + 66227 * 2 ^ 59
def prefixEnd_66227 : Nat := 4983230072969 + 3 ^ 40 * 66227 * 2
def baseEnd_66227 : Nat := 5037967897098906704879

theorem tailTrace_66227 : CollatzResearch.WordTrace tailWord_66227 prefixEnd_66227 5037967897098906704879 := by
  unfold tailWord_66227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415497131078364516220935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1610331420718909677480623 2415497131078364516220935)
  ·
    refine ⟨3623245696617546774331403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2415497131078364516220935 3623245696617546774331403)
    ·
      refine ⟨5434868544926320161497105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3623245696617546774331403 5434868544926320161497105)
      ·
        refine ⟨4076151408694740121122829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5434868544926320161497105 4076151408694740121122829)
        ·
          refine ⟨1528556778260527545421061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4076151408694740121122829 1528556778260527545421061)
          ·
            refine ⟨286604395923848914766449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1528556778260527545421061 286604395923848914766449)
            ·
              refine ⟨214953296942886686074837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286604395923848914766449 214953296942886686074837)
              ·
                refine ⟨5037967897098906704879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 214953296942886686074837 5037967897098906704879)
                ·
                  rfl

theorem cell21_66227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_66227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66227 prefixEnd_66227 := by exact prefixLift 66227
  have htrace : WordTrace (prefixWord ++ tailWord_66227) baseStart_66227 baseEnd_66227 := by
    simpa [prefixWord, tailWord_66227, baseEnd_66227] using wordTrace_append hprefix tailTrace_66227
  have hstable : (prefixWord ++ tailWord_66227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66227).length < 2 ^ (prefixWord ++ tailWord_66227).sum := by decide
  have hdescent : baseEnd_66227 < baseStart_66227 := by decide
  rcases family_descends (prefixWord ++ tailWord_66227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66272 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_66272 : Nat := 118140960795 + 66272 * 2 ^ 59
def prefixEnd_66272 : Nat := 4983230072969 + 3 ^ 40 * 66272 * 2
def baseEnd_66272 : Nat := 15124173304386641864545

theorem tailTrace_66272 : CollatzResearch.WordTrace tailWord_66272 prefixEnd_66272 15124173304386641864545 := by
  unfold tailWord_66272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208569207957668600804535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1611425610610224801072713 1208569207957668600804535)
  ·
    refine ⟨1812853811936502901206803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208569207957668600804535 1812853811936502901206803)
    ·
      refine ⟨2719280717904754351810205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1812853811936502901206803 2719280717904754351810205)
      ·
        refine ⟨1019730269214282881928827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2719280717904754351810205 1019730269214282881928827)
        ·
          refine ⟨1529595403821424322893241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019730269214282881928827 1529595403821424322893241)
          ·
            refine ⟨1147196552866068242169931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1529595403821424322893241 1147196552866068242169931)
            ·
              refine ⟨1720794829299102363254897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147196552866068242169931 1720794829299102363254897)
              ·
                refine ⟨1290596121974326772441173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1720794829299102363254897 1290596121974326772441173)
                ·
                  refine ⟨15124173304386641864545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1290596121974326772441173 15124173304386641864545)
                  ·
                    rfl

theorem cell21_66272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_66272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66272 prefixEnd_66272 := by exact prefixLift 66272
  have htrace : WordTrace (prefixWord ++ tailWord_66272) baseStart_66272 baseEnd_66272 := by
    simpa [prefixWord, tailWord_66272, baseEnd_66272] using wordTrace_append hprefix tailTrace_66272
  have hstable : (prefixWord ++ tailWord_66272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66272).length < 2 ^ (prefixWord ++ tailWord_66272).sum := by decide
  have hdescent : baseEnd_66272 < baseStart_66272 := by decide
  rcases family_descends (prefixWord ++ tailWord_66272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66275 : List Nat := [1, 1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_66275 : Nat := 118140960795 + 66275 * 2 ^ 59
def prefixEnd_66275 : Nat := 4983230072969 + 3 ^ 40 * 66275 * 2
def baseEnd_66275 : Nat := 15124857945259303314539

theorem tailTrace_66275 : CollatzResearch.WordTrace tailWord_66275 prefixEnd_66275 15124857945259303314539 := by
  unfold tailWord_66275
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417247834904468713968279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1611498556602979142645519 2417247834904468713968279)
  ·
    refine ⟨3625871752356703070952419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2417247834904468713968279 3625871752356703070952419)
    ·
      refine ⟨5438807628535054606428629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625871752356703070952419 5438807628535054606428629)
      ·
        refine ⟨127472053793790342338171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5438807628535054606428629 127472053793790342338171)
        ·
          refine ⟨191208080690685513507257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127472053793790342338171 191208080690685513507257)
          ·
            refine ⟨143406060518014135130443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191208080690685513507257 143406060518014135130443)
            ·
              refine ⟨215109090777021202695665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143406060518014135130443 215109090777021202695665)
              ·
                refine ⟨161331818082765902021749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215109090777021202695665 161331818082765902021749)
                ·
                  refine ⟨15124857945259303314539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161331818082765902021749 15124857945259303314539)
                  ·
                    rfl

theorem cell21_66275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_66275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66275 prefixEnd_66275 := by exact prefixLift 66275
  have htrace : WordTrace (prefixWord ++ tailWord_66275) baseStart_66275 baseEnd_66275 := by
    simpa [prefixWord, tailWord_66275, baseEnd_66275] using wordTrace_append hprefix tailTrace_66275
  have hstable : (prefixWord ++ tailWord_66275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66275).length < 2 ^ (prefixWord ++ tailWord_66275).sum := by decide
  have hdescent : baseEnd_66275 < baseStart_66275 := by decide
  rcases family_descends (prefixWord ++ tailWord_66275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66306 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_66306 : Nat := 118140960795 + 66306 * 2 ^ 59
def prefixEnd_66306 : Nat := 4983230072969 + 3 ^ 40 * 66306 * 2
def baseEnd_66306 : Nat := 15131932567610138297809

theorem tailTrace_66306 : CollatzResearch.WordTrace tailWord_66306 prefixEnd_66306 15131932567610138297809 := by
  unfold tailWord_66306
  simp only [CollatzResearch.WordTrace]
  refine ⟨604594624448040252086693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1612252331861440672231181 604594624448040252086693)
  ·
    refine ⟨113361492084007547266255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 604594624448040252086693 113361492084007547266255)
    ·
      refine ⟨170042238126011320899383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113361492084007547266255 170042238126011320899383)
      ·
        refine ⟨255063357189016981349075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170042238126011320899383 255063357189016981349075)
        ·
          refine ⟨382595035783525472023613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255063357189016981349075 382595035783525472023613)
          ·
            refine ⟨143473138418822052008855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382595035783525472023613 143473138418822052008855)
            ·
              refine ⟨215209707628233078013283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143473138418822052008855 215209707628233078013283)
              ·
                refine ⟨322814561442349617019925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215209707628233078013283 322814561442349617019925)
                ·
                  refine ⟨15131932567610138297809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322814561442349617019925 15131932567610138297809)
                  ·
                    rfl

theorem cell21_66306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_66306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66306 prefixEnd_66306 := by exact prefixLift 66306
  have htrace : WordTrace (prefixWord ++ tailWord_66306) baseStart_66306 baseEnd_66306 := by
    simpa [prefixWord, tailWord_66306, baseEnd_66306] using wordTrace_append hprefix tailTrace_66306
  have hstable : (prefixWord ++ tailWord_66306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66306).length < 2 ^ (prefixWord ++ tailWord_66306).sum := by decide
  have hdescent : baseEnd_66306 < baseStart_66306 := by decide
  rcases family_descends (prefixWord ++ tailWord_66306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66348 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_66348 : Nat := 118140960795 + 66348 * 2 ^ 59
def prefixEnd_66348 : Nat := 4983230072969 + 3 ^ 40 * 66348 * 2
def baseEnd_66348 : Nat := 15141517539827398597723

theorem tailTrace_66348 : CollatzResearch.WordTrace tailWord_66348 prefixEnd_66348 15141517539827398597723 := by
  unfold tailWord_66348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209955181820001090687849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1613273575760001454250465 1209955181820001090687849)
  ·
    refine ⟨907466386365000818015887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1209955181820001090687849 907466386365000818015887)
    ·
      refine ⟨1361199579547501227023831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 907466386365000818015887 1361199579547501227023831)
      ·
        refine ⟨2041799369321251840535747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1361199579547501227023831 2041799369321251840535747)
        ·
          refine ⟨3062699053981877760803621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2041799369321251840535747 3062699053981877760803621)
          ·
            refine ⟨574256072621602080150679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3062699053981877760803621 574256072621602080150679)
            ·
              refine ⟨861384108932403120226019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574256072621602080150679 861384108932403120226019)
              ·
                refine ⟨1292076163398604680339029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861384108932403120226019 1292076163398604680339029)
                ·
                  refine ⟨15141517539827398597723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1292076163398604680339029 15141517539827398597723)
                  ·
                    rfl

theorem cell21_66348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_66348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66348 prefixEnd_66348 := by exact prefixLift 66348
  have htrace : WordTrace (prefixWord ++ tailWord_66348) baseStart_66348 baseEnd_66348 := by
    simpa [prefixWord, tailWord_66348, baseEnd_66348] using wordTrace_append hprefix tailTrace_66348
  have hstable : (prefixWord ++ tailWord_66348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66348).length < 2 ^ (prefixWord ++ tailWord_66348).sum := by decide
  have hdescent : baseEnd_66348 < baseStart_66348 := by decide
  rcases family_descends (prefixWord ++ tailWord_66348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66374 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_66374 : Nat := 118140960795 + 66374 * 2 ^ 59
def prefixEnd_66374 : Nat := 4983230072969 + 3 ^ 40 * 66374 * 2
def baseEnd_66374 : Nat := 15147451094057131164337

theorem tailTrace_66374 : CollatzResearch.WordTrace tailWord_66374 prefixEnd_66374 15147451094057131164337 := by
  unfold tailWord_66374
  simp only [CollatzResearch.WordTrace]
  refine ⟨75651833173306519431943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1613905774363872414548117 75651833173306519431943)
  ·
    refine ⟨113477749759959779147915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75651833173306519431943 113477749759959779147915)
    ·
      refine ⟨170216624639939668721873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113477749759959779147915 170216624639939668721873)
      ·
        refine ⟨127662468479954751541405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170216624639939668721873 127662468479954751541405)
        ·
          refine ⟨47873425679983031828027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127662468479954751541405 47873425679983031828027)
          ·
            refine ⟨71810138519974547742041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47873425679983031828027 71810138519974547742041)
            ·
              refine ⟨53857603889980910806531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71810138519974547742041 53857603889980910806531)
              ·
                refine ⟨80786405834971366209797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53857603889980910806531 80786405834971366209797)
                ·
                  refine ⟨15147451094057131164337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80786405834971366209797 15147451094057131164337)
                  ·
                    rfl

theorem cell21_66374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_66374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66374 prefixEnd_66374 := by exact prefixLift 66374
  have htrace : WordTrace (prefixWord ++ tailWord_66374) baseStart_66374 baseEnd_66374 := by
    simpa [prefixWord, tailWord_66374, baseEnd_66374] using wordTrace_append hprefix tailTrace_66374
  have hstable : (prefixWord ++ tailWord_66374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66374).length < 2 ^ (prefixWord ++ tailWord_66374).sum := by decide
  have hdescent : baseEnd_66374 < baseStart_66374 := by decide
  rcases family_descends (prefixWord ++ tailWord_66374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66396 : List Nat := [2, 2, 4, 2, 1, 1, 2, 7]
def baseStart_66396 : Nat := 118140960795 + 66396 * 2 ^ 59
def prefixEnd_66396 : Nat := 4983230072969 + 3 ^ 40 * 66396 * 2
def baseEnd_66396 : Nat := 5050823931263327265875

theorem tailTrace_66396 : CollatzResearch.WordTrace tailWord_66396 prefixEnd_66396 5050823931263327265875 := by
  unfold tailWord_66396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210830533733053189561521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1614440711644070919415361 1210830533733053189561521)
  ·
    refine ⟨908122900299789892171141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1210830533733053189561521 908122900299789892171141)
    ·
      refine ⟨170273043806210604782089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 908122900299789892171141 170273043806210604782089)
      ·
        refine ⟨127704782854657953586567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170273043806210604782089 127704782854657953586567)
        ·
          refine ⟨191557174281986930379851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127704782854657953586567 191557174281986930379851)
          ·
            refine ⟨287335761422980395569777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191557174281986930379851 287335761422980395569777)
            ·
              refine ⟨215501821067235296677333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287335761422980395569777 215501821067235296677333)
              ·
                refine ⟨5050823931263327265875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215501821067235296677333 5050823931263327265875)
                ·
                  rfl

theorem cell21_66396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_66396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66396 prefixEnd_66396 := by exact prefixLift 66396
  have htrace : WordTrace (prefixWord ++ tailWord_66396) baseStart_66396 baseEnd_66396 := by
    simpa [prefixWord, tailWord_66396, baseEnd_66396] using wordTrace_append hprefix tailTrace_66396
  have hstable : (prefixWord ++ tailWord_66396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66396).length < 2 ^ (prefixWord ++ tailWord_66396).sum := by decide
  have hdescent : baseEnd_66396 < baseStart_66396 := by decide
  rcases family_descends (prefixWord ++ tailWord_66396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66430 : List Nat := [4, 2, 3, 1, 2, 2, 1, 6]
def baseStart_66430 : Nat := 118140960795 + 66430 * 2 ^ 59
def prefixEnd_66430 : Nat := 4983230072969 + 3 ^ 40 * 66430 * 2
def baseEnd_66430 : Nat := 5053410352337826076963

theorem tailTrace_66430 : CollatzResearch.WordTrace tailWord_66430 prefixEnd_66430 5053410352337826076963 := by
  unfold tailWord_66430
  simp only [CollatzResearch.WordTrace]
  refine ⟨302862643667866273232593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1615267432895286790573829 302862643667866273232593)
  ·
    refine ⟨227146982750899704924445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302862643667866273232593 227146982750899704924445)
    ·
      refine ⟨85180118531587389346667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227146982750899704924445 85180118531587389346667)
      ·
        refine ⟨127770177797381084020001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85180118531587389346667 127770177797381084020001)
        ·
          refine ⟨95827633348035813015001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127770177797381084020001 95827633348035813015001)
          ·
            refine ⟨71870725011026859761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95827633348035813015001 71870725011026859761251)
            ·
              refine ⟨107806087516540289641877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71870725011026859761251 107806087516540289641877)
              ·
                refine ⟨5053410352337826076963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107806087516540289641877 5053410352337826076963)
                ·
                  rfl

theorem cell21_66430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_66430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66430 prefixEnd_66430 := by exact prefixLift 66430
  have htrace : WordTrace (prefixWord ++ tailWord_66430) baseStart_66430 baseEnd_66430 := by
    simpa [prefixWord, tailWord_66430, baseEnd_66430] using wordTrace_append hprefix tailTrace_66430
  have hstable : (prefixWord ++ tailWord_66430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66430).length < 2 ^ (prefixWord ++ tailWord_66430).sum := by decide
  have hdescent : baseEnd_66430 < baseStart_66430 := by decide
  rcases family_descends (prefixWord ++ tailWord_66430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66441 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_66441 : Nat := 118140960795 + 66441 * 2 ^ 59
def prefixEnd_66441 : Nat := 4983230072969 + 3 ^ 40 * 66441 * 2
def baseEnd_66441 : Nat := 15162741406879903547533

theorem tailTrace_66441 : CollatzResearch.WordTrace tailWord_66441 prefixEnd_66441 15162741406879903547533 := by
  unfold tailWord_66441
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423302352303079064511177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1615534901535386043007451 2423302352303079064511177)
  ·
    refine ⟨1817476764227309298383383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2423302352303079064511177 1817476764227309298383383)
    ·
      refine ⟨2726215146340963947575075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1817476764227309298383383 2726215146340963947575075)
      ·
        refine ⟨4089322719511445921362613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726215146340963947575075 4089322719511445921362613)
        ·
          refine ⟨383374004954198055127745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4089322719511445921362613 383374004954198055127745)
          ·
            refine ⟨287530503715648541345809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383374004954198055127745 287530503715648541345809)
            ·
              refine ⟨215647877786736406009357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287530503715648541345809 215647877786736406009357)
              ·
                refine ⟨80867954170026152253509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215647877786736406009357 80867954170026152253509)
                ·
                  refine ⟨15162741406879903547533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80867954170026152253509 15162741406879903547533)
                  ·
                    rfl

theorem cell21_66441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_66441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66441 prefixEnd_66441 := by exact prefixLift 66441
  have htrace : WordTrace (prefixWord ++ tailWord_66441) baseStart_66441 baseEnd_66441 := by
    simpa [prefixWord, tailWord_66441, baseEnd_66441] using wordTrace_append hprefix tailTrace_66441
  have hstable : (prefixWord ++ tailWord_66441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66441).length < 2 ^ (prefixWord ++ tailWord_66441).sum := by decide
  have hdescent : baseEnd_66441 < baseStart_66441 := by decide
  rcases family_descends (prefixWord ++ tailWord_66441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66520 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_66520 : Nat := 118140960795 + 66520 * 2 ^ 59
def prefixEnd_66520 : Nat := 4983230072969 + 3 ^ 40 * 66520 * 2
def baseEnd_66520 : Nat := 15180770283193321730705

theorem tailTrace_66520 : CollatzResearch.WordTrace tailWord_66520 prefixEnd_66520 15180770283193321730705 := by
  unfold tailWord_66520
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213091859508437778318507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1617455812677917037758009 1213091859508437778318507)
  ·
    refine ⟨1819637789262656667477761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1213091859508437778318507 1819637789262656667477761)
    ·
      refine ⟨1364728341946992500608321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819637789262656667477761 1364728341946992500608321)
      ·
        refine ⟨1023546256460244375456241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1364728341946992500608321 1023546256460244375456241)
        ·
          refine ⟨767659692345183281592181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1023546256460244375456241 767659692345183281592181)
          ·
            refine ⟨71968096157360932649267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 767659692345183281592181 71968096157360932649267)
            ·
              refine ⟨107952144236041398973901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71968096157360932649267 107952144236041398973901)
              ·
                refine ⟨40482054088515524615213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107952144236041398973901 40482054088515524615213)
                ·
                  refine ⟨15180770283193321730705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40482054088515524615213 15180770283193321730705)
                  ·
                    rfl

theorem cell21_66520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_66520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66520 prefixEnd_66520 := by exact prefixLift 66520
  have htrace : WordTrace (prefixWord ++ tailWord_66520) baseStart_66520 baseEnd_66520 := by
    simpa [prefixWord, tailWord_66520, baseEnd_66520] using wordTrace_append hprefix tailTrace_66520
  have hstable : (prefixWord ++ tailWord_66520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66520).length < 2 ^ (prefixWord ++ tailWord_66520).sum := by decide
  have hdescent : baseEnd_66520 < baseStart_66520 := by decide
  rcases family_descends (prefixWord ++ tailWord_66520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66593 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_66593 : Nat := 118140960795 + 66593 * 2 ^ 59
def prefixEnd_66593 : Nat := 4983230072969 + 3 ^ 40 * 66593 * 2
def baseEnd_66593 : Nat := 15197429877761417013889

theorem tailTrace_66593 : CollatzResearch.WordTrace tailWord_66593 prefixEnd_66593 15197429877761417013889 := by
  unfold tailWord_66593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428846247752409024044433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1619230831834939349362955 2428846247752409024044433)
  ·
    refine ⟨1821634685814306768033325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2428846247752409024044433 1821634685814306768033325)
    ·
      refine ⟨683113007180365038012497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1821634685814306768033325 683113007180365038012497)
      ·
        refine ⟨512334755385273778509373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683113007180365038012497 512334755385273778509373)
        ·
          refine ⟨192125533269477666941015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512334755385273778509373 192125533269477666941015)
          ·
            refine ⟨288188299904216500411523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192125533269477666941015 288188299904216500411523)
            ·
              refine ⟨432282449856324750617285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288188299904216500411523 432282449856324750617285)
              ·
                refine ⟨81052959348060890740741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432282449856324750617285 81052959348060890740741)
                ·
                  refine ⟨15197429877761417013889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81052959348060890740741 15197429877761417013889)
                  ·
                    rfl

theorem cell21_66593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_66593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66593 prefixEnd_66593 := by exact prefixLift 66593
  have htrace : WordTrace (prefixWord ++ tailWord_66593) baseStart_66593 baseEnd_66593 := by
    simpa [prefixWord, tailWord_66593, baseEnd_66593] using wordTrace_append hprefix tailTrace_66593
  have hstable : (prefixWord ++ tailWord_66593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66593).length < 2 ^ (prefixWord ++ tailWord_66593).sum := by decide
  have hdescent : baseEnd_66593 < baseStart_66593 := by decide
  rcases family_descends (prefixWord ++ tailWord_66593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66596 : List Nat := [2, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_66596 : Nat := 118140960795 + 66596 * 2 ^ 59
def prefixEnd_66596 : Nat := 4983230072969 + 3 ^ 40 * 66596 * 2
def baseEnd_66596 : Nat := 15198114518634078463883

theorem tailTrace_66596 : CollatzResearch.WordTrace tailWord_66596 prefixEnd_66596 15198114518634078463883 := by
  unfold tailWord_66596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1214477833370770268201821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1619303777827693690935761 1214477833370770268201821)
  ·
    refine ⟨455429187514038850575683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1214477833370770268201821 455429187514038850575683)
    ·
      refine ⟨683143781271058275863525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455429187514038850575683 683143781271058275863525)
      ·
        refine ⟨128089458988323426724411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 683143781271058275863525 128089458988323426724411)
        ·
          refine ⟨192134188482485140086617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128089458988323426724411 192134188482485140086617)
          ·
            refine ⟨144100641361863855064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192134188482485140086617 144100641361863855064963)
            ·
              refine ⟨216150962042795782597445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144100641361863855064963 216150962042795782597445)
              ·
                refine ⟨40528305383024209237021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216150962042795782597445 40528305383024209237021)
                ·
                  refine ⟨15198114518634078463883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40528305383024209237021 15198114518634078463883)
                  ·
                    rfl

theorem cell21_66596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_66596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66596 prefixEnd_66596 := by exact prefixLift 66596
  have htrace : WordTrace (prefixWord ++ tailWord_66596) baseStart_66596 baseEnd_66596 := by
    simpa [prefixWord, tailWord_66596, baseEnd_66596] using wordTrace_append hprefix tailTrace_66596
  have hstable : (prefixWord ++ tailWord_66596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66596).length < 2 ^ (prefixWord ++ tailWord_66596).sum := by decide
  have hdescent : baseEnd_66596 < baseStart_66596 := by decide
  rcases family_descends (prefixWord ++ tailWord_66596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66776 : List Nat := [2, 1, 2, 2, 5, 2, 1, 6]
def baseStart_66776 : Nat := 118140960795 + 66776 * 2 ^ 59
def prefixEnd_66776 : Nat := 4983230072969 + 3 ^ 40 * 66776 * 2
def baseEnd_66776 : Nat := 5079730990331255154505

theorem tailTrace_66776 : CollatzResearch.WordTrace tailWord_66776 prefixEnd_66776 5079730990331255154505 := by
  unfold tailWord_66776
  simp only [CollatzResearch.WordTrace]
  refine ⟨1217760403044715638978091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1623680537392954185304121 1217760403044715638978091)
  ·
    refine ⟨1826640604567073458467137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1217760403044715638978091 1826640604567073458467137)
    ·
      refine ⟨1369980453425305093850353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1826640604567073458467137 1369980453425305093850353)
      ·
        refine ⟨1027485340068978820387765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1369980453425305093850353 1027485340068978820387765)
        ·
          refine ⟨96326750631466764411353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1027485340068978820387765 96326750631466764411353)
          ·
            refine ⟨72245062973600073308515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96326750631466764411353 72245062973600073308515)
            ·
              refine ⟨108367594460400109962773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72245062973600073308515 108367594460400109962773)
              ·
                refine ⟨5079730990331255154505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108367594460400109962773 5079730990331255154505)
                ·
                  rfl

theorem cell21_66776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_66776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66776 prefixEnd_66776 := by exact prefixLift 66776
  have htrace : WordTrace (prefixWord ++ tailWord_66776) baseStart_66776 baseEnd_66776 := by
    simpa [prefixWord, tailWord_66776, baseEnd_66776] using wordTrace_append hprefix tailTrace_66776
  have hstable : (prefixWord ++ tailWord_66776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66776).length < 2 ^ (prefixWord ++ tailWord_66776).sum := by decide
  have hdescent : baseEnd_66776 < baseStart_66776 := by decide
  rcases family_descends (prefixWord ++ tailWord_66776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66880 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_66880 : Nat := 118140960795 + 66880 * 2 ^ 59
def prefixEnd_66880 : Nat := 4983230072969 + 3 ^ 40 * 66880 * 2
def baseEnd_66880 : Nat := 15262927187912695729969

theorem tailTrace_66880 : CollatzResearch.WordTrace tailWord_66880 prefixEnd_66880 15262927187912695729969 := by
  unfold tailWord_66880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1219656998856328519871047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1626209331808438026494729 1219656998856328519871047)
  ·
    refine ⟨1829485498284492779806571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1219656998856328519871047 1829485498284492779806571)
    ·
      refine ⟨2744228247426739169709857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1829485498284492779806571 2744228247426739169709857)
      ·
        refine ⟨2058171185570054377282393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2744228247426739169709857 2058171185570054377282393)
        ·
          refine ⟨1543628389177540782961795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2058171185570054377282393 1543628389177540782961795)
          ·
            refine ⟨2315442583766311174442693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543628389177540782961795 2315442583766311174442693)
            ·
              refine ⟨434145484456183345208005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2315442583766311174442693 434145484456183345208005)
              ·
                refine ⟨81402278335534377226501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434145484456183345208005 81402278335534377226501)
                ·
                  refine ⟨15262927187912695729969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81402278335534377226501 15262927187912695729969)
                  ·
                    rfl

theorem cell21_66880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_66880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66880 prefixEnd_66880 := by exact prefixLift 66880
  have htrace : WordTrace (prefixWord ++ tailWord_66880) baseStart_66880 baseEnd_66880 := by
    simpa [prefixWord, tailWord_66880, baseEnd_66880] using wordTrace_append hprefix tailTrace_66880
  have hstable : (prefixWord ++ tailWord_66880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66880).length < 2 ^ (prefixWord ++ tailWord_66880).sum := by decide
  have hdescent : baseEnd_66880 < baseStart_66880 := by decide
  rcases family_descends (prefixWord ++ tailWord_66880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66886 : List Nat := [6, 1, 1, 3, 1, 1, 2, 6]
def baseStart_66886 : Nat := 118140960795 + 66886 * 2 ^ 59
def prefixEnd_66886 : Nat := 4983230072969 + 3 ^ 40 * 66886 * 2
def baseEnd_66886 : Nat := 5088098823219339543319

theorem tailTrace_66886 : CollatzResearch.WordTrace tailWord_66886 prefixEnd_66886 5088098823219339543319 := by
  unfold tailWord_66886
  simp only [CollatzResearch.WordTrace]
  refine ⟨76235401115341252014391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1626355223793946709640341 76235401115341252014391)
  ·
    refine ⟨114353101673011878021587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76235401115341252014391 114353101673011878021587)
    ·
      refine ⟨171529652509517817032381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114353101673011878021587 171529652509517817032381)
      ·
        refine ⟨64323619691069181387143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171529652509517817032381 64323619691069181387143)
        ·
          refine ⟨96485429536603772080715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64323619691069181387143 96485429536603772080715)
          ·
            refine ⟨144728144304905658121073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96485429536603772080715 144728144304905658121073)
            ·
              refine ⟨108546108228679243590805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144728144304905658121073 108546108228679243590805)
              ·
                refine ⟨5088098823219339543319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108546108228679243590805 5088098823219339543319)
                ·
                  rfl

theorem cell21_66886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_66886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66886 prefixEnd_66886 := by exact prefixLift 66886
  have htrace : WordTrace (prefixWord ++ tailWord_66886) baseStart_66886 baseEnd_66886 := by
    simpa [prefixWord, tailWord_66886, baseEnd_66886] using wordTrace_append hprefix tailTrace_66886
  have hstable : (prefixWord ++ tailWord_66886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66886).length < 2 ^ (prefixWord ++ tailWord_66886).sum := by decide
  have hdescent : baseEnd_66886 < baseStart_66886 := by decide
  rcases family_descends (prefixWord ++ tailWord_66886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66945 : List Nat := [1, 2, 4, 3, 3, 1, 1, 6]
def baseStart_66945 : Nat := 118140960795 + 66945 * 2 ^ 59
def prefixEnd_66945 : Nat := 4983230072969 + 3 ^ 40 * 66945 * 2
def baseEnd_66945 : Nat := 5092587024495675715501

theorem tailTrace_66945 : CollatzResearch.WordTrace tailWord_66945 prefixEnd_66945 5092587024495675715501 := by
  unfold tailWord_66945
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441684742477173140858289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1627789828318115427238859 2441684742477173140858289)
  ·
    refine ⟨1831263556857879855643717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2441684742477173140858289 1831263556857879855643717)
    ·
      refine ⟨343361916910852472933197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1831263556857879855643717 343361916910852472933197)
      ·
        refine ⟨128760718841569677349949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343361916910852472933197 128760718841569677349949)
        ·
          refine ⟨48285269565588629006231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128760718841569677349949 48285269565588629006231)
          ·
            refine ⟨72427904348382943509347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48285269565588629006231 72427904348382943509347)
            ·
              refine ⟨108641856522574415264021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72427904348382943509347 108641856522574415264021)
              ·
                refine ⟨5092587024495675715501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108641856522574415264021 5092587024495675715501)
                ·
                  rfl

theorem cell21_66945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 6].length) (baseStart_66945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66945 prefixEnd_66945 := by exact prefixLift 66945
  have htrace : WordTrace (prefixWord ++ tailWord_66945) baseStart_66945 baseEnd_66945 := by
    simpa [prefixWord, tailWord_66945, baseEnd_66945] using wordTrace_append hprefix tailTrace_66945
  have hstable : (prefixWord ++ tailWord_66945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66945).length < 2 ^ (prefixWord ++ tailWord_66945).sum := by decide
  have hdescent : baseEnd_66945 < baseStart_66945 := by decide
  rcases family_descends (prefixWord ++ tailWord_66945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66956 : List Nat := [2, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_66956 : Nat := 118140960795 + 66956 * 2 ^ 59
def prefixEnd_66956 : Nat := 4983230072969 + 3 ^ 40 * 66956 * 2
def baseEnd_66956 : Nat := 15280271423353452463147

theorem tailTrace_66956 : CollatzResearch.WordTrace tailWord_66956 prefixEnd_66956 15280271423353452463147 := by
  unfold tailWord_66956
  simp only [CollatzResearch.WordTrace]
  refine ⟨1221042972718661009754361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1628057296958214679672481 1221042972718661009754361)
  ·
    refine ⟨915782229538995757315771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1221042972718661009754361 915782229538995757315771)
    ·
      refine ⟨1373673344308493635973657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915782229538995757315771 1373673344308493635973657)
      ·
        refine ⟨1030255008231370226980243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1373673344308493635973657 1030255008231370226980243)
        ·
          refine ⟨1545382512347055340470365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030255008231370226980243 1545382512347055340470365)
          ·
            refine ⟨579518442130145752676387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1545382512347055340470365 579518442130145752676387)
            ·
              refine ⟨869277663195218629014581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579518442130145752676387 869277663195218629014581)
              ·
                refine ⟨81494780924551746470117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869277663195218629014581 81494780924551746470117)
                ·
                  refine ⟨15280271423353452463147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81494780924551746470117 15280271423353452463147)
                  ·
                    rfl

theorem cell21_66956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_66956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_66956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_66956 prefixEnd_66956 := by exact prefixLift 66956
  have htrace : WordTrace (prefixWord ++ tailWord_66956) baseStart_66956 baseEnd_66956 := by
    simpa [prefixWord, tailWord_66956, baseEnd_66956] using wordTrace_append hprefix tailTrace_66956
  have hstable : (prefixWord ++ tailWord_66956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66956).length < 2 ^ (prefixWord ++ tailWord_66956).sum := by decide
  have hdescent : baseEnd_66956 < baseStart_66956 := by decide
  rcases family_descends (prefixWord ++ tailWord_66956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67204 : List Nat := [2, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_67204 : Nat := 118140960795 + 67204 * 2 ^ 59
def prefixEnd_67204 : Nat := 4983230072969 + 3 ^ 40 * 67204 * 2
def baseEnd_67204 : Nat := 15336868402160132329307

theorem tailTrace_67204 : CollatzResearch.WordTrace tailWord_67204 prefixEnd_67204 15336868402160132329307 := by
  unfold tailWord_67204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225565624269430187268333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1634087499025906916357777 1225565624269430187268333)
  ·
    refine ⟨459587109101036320225625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1225565624269430187268333 459587109101036320225625)
    ·
      refine ⟨344690331825777240169219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459587109101036320225625 344690331825777240169219)
      ·
        refine ⟨517035497738665860253829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344690331825777240169219 517035497738665860253829)
        ·
          refine ⟨96944155825999848797593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 517035497738665860253829 96944155825999848797593)
          ·
            refine ⟨72708116869499886598195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96944155825999848797593 72708116869499886598195)
            ·
              refine ⟨109062175304249829897293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72708116869499886598195 109062175304249829897293)
              ·
                refine ⟨40898315739093686211485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109062175304249829897293 40898315739093686211485)
                ·
                  refine ⟨15336868402160132329307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40898315739093686211485 15336868402160132329307)
                  ·
                    rfl

theorem cell21_67204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_67204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67204 prefixEnd_67204 := by exact prefixLift 67204
  have htrace : WordTrace (prefixWord ++ tailWord_67204) baseStart_67204 baseEnd_67204 := by
    simpa [prefixWord, tailWord_67204, baseEnd_67204] using wordTrace_append hprefix tailTrace_67204
  have hstable : (prefixWord ++ tailWord_67204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67204).length < 2 ^ (prefixWord ++ tailWord_67204).sum := by decide
  have hdescent : baseEnd_67204 < baseStart_67204 := by decide
  rcases family_descends (prefixWord ++ tailWord_67204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67274 : List Nat := [3, 1, 2, 1, 5, 9]
def baseStart_67274 : Nat := 118140960795 + 67274 * 2 ^ 59
def prefixEnd_67274 : Nat := 4983230072969 + 3 ^ 40 * 67274 * 2
def baseEnd_67274 : Nat := 568623827994650598611

theorem tailTrace_67274 : CollatzResearch.WordTrace tailWord_67274 prefixEnd_67274 568623827994650598611 := by
  unfold tailWord_67274
  simp only [CollatzResearch.WordTrace]
  refine ⟨613421089571315582396219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1635789572190174886389917 613421089571315582396219)
  ·
    refine ⟨920131634356973373594329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613421089571315582396219 920131634356973373594329)
    ·
      refine ⟨690098725767730030195747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 920131634356973373594329 690098725767730030195747)
      ·
        refine ⟨1035148088651595045293621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690098725767730030195747 1035148088651595045293621)
        ·
          refine ⟨97045133311087035496277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1035148088651595045293621 97045133311087035496277)
          ·
            refine ⟨568623827994650598611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 97045133311087035496277 568623827994650598611)
            ·
              rfl

theorem cell21_67274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 9].length) (baseStart_67274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67274 prefixEnd_67274 := by exact prefixLift 67274
  have htrace : WordTrace (prefixWord ++ tailWord_67274) baseStart_67274 baseEnd_67274 := by
    simpa [prefixWord, tailWord_67274, baseEnd_67274] using wordTrace_append hprefix tailTrace_67274
  have hstable : (prefixWord ++ tailWord_67274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67274).length < 2 ^ (prefixWord ++ tailWord_67274).sum := by decide
  have hdescent : baseEnd_67274 < baseStart_67274 := by decide
  rcases family_descends (prefixWord ++ tailWord_67274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67395 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_67395 : Nat := 118140960795 + 67395 * 2 ^ 59
def prefixEnd_67395 : Nat := 4983230072969 + 3 ^ 40 * 67395 * 2
def baseEnd_67395 : Nat := 15380457204386244645583

theorem tailTrace_67395 : CollatzResearch.WordTrace tailWord_67395 prefixEnd_67395 15380457204386244645583 := by
  unfold tailWord_67395
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458097590846899994739639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1638731727231266663159759 2458097590846899994739639)
  ·
    refine ⟨3687146386270349992109459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2458097590846899994739639 3687146386270349992109459)
    ·
      refine ⟨5530719579405524988164189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687146386270349992109459 5530719579405524988164189)
      ·
        refine ⟨2074019842277071870561571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5530719579405524988164189 2074019842277071870561571)
        ·
          refine ⟨3111029763415607805842357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074019842277071870561571 3111029763415607805842357)
          ·
            refine ⟨291659040320213231797721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3111029763415607805842357 291659040320213231797721)
            ·
              refine ⟨218744280240159923848291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291659040320213231797721 218744280240159923848291)
              ·
                refine ⟨328116420360239885772437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218744280240159923848291 328116420360239885772437)
                ·
                  refine ⟨15380457204386244645583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 328116420360239885772437 15380457204386244645583)
                  ·
                    rfl

theorem cell21_67395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_67395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67395 prefixEnd_67395 := by exact prefixLift 67395
  have htrace : WordTrace (prefixWord ++ tailWord_67395) baseStart_67395 baseEnd_67395 := by
    simpa [prefixWord, tailWord_67395, baseEnd_67395] using wordTrace_append hprefix tailTrace_67395
  have hstable : (prefixWord ++ tailWord_67395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67395).length < 2 ^ (prefixWord ++ tailWord_67395).sum := by decide
  have hdescent : baseEnd_67395 < baseStart_67395 := by decide
  rcases family_descends (prefixWord ++ tailWord_67395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67446 : List Nat := [5, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_67446 : Nat := 118140960795 + 67446 * 2 ^ 59
def prefixEnd_67446 : Nat := 4983230072969 + 3 ^ 40 * 67446 * 2
def baseEnd_67446 : Nat := 15392096099221489295479

theorem tailTrace_67446 : CollatzResearch.WordTrace tailWord_67446 prefixEnd_67446 15392096099221489295479 := by
  unfold tailWord_67446
  simp only [CollatzResearch.WordTrace]
  refine ⟨153747357103883481552887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1639971809108090469897461 153747357103883481552887)
  ·
    refine ⟨230621035655825222329331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153747357103883481552887 230621035655825222329331)
    ·
      refine ⟨345931553483737833493997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230621035655825222329331 345931553483737833493997)
      ·
        refine ⟨129724332556401687560249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345931553483737833493997 129724332556401687560249)
        ·
          refine ⟨97293249417301265670187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129724332556401687560249 97293249417301265670187)
          ·
            refine ⟨145939874125951898505281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97293249417301265670187 145939874125951898505281)
            ·
              refine ⟨109454905594463923878961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145939874125951898505281 109454905594463923878961)
              ·
                refine ⟨82091179195847942909221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109454905594463923878961 82091179195847942909221)
                ·
                  refine ⟨15392096099221489295479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82091179195847942909221 15392096099221489295479)
                  ·
                    rfl

theorem cell21_67446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_67446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67446 prefixEnd_67446 := by exact prefixLift 67446
  have htrace : WordTrace (prefixWord ++ tailWord_67446) baseStart_67446 baseEnd_67446 := by
    simpa [prefixWord, tailWord_67446, baseEnd_67446] using wordTrace_append hprefix tailTrace_67446
  have hstable : (prefixWord ++ tailWord_67446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67446).length < 2 ^ (prefixWord ++ tailWord_67446).sum := by decide
  have hdescent : baseEnd_67446 < baseStart_67446 := by decide
  rcases family_descends (prefixWord ++ tailWord_67446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67474 : List Nat := [3, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_67474 : Nat := 118140960795 + 67474 * 2 ^ 59
def prefixEnd_67474 : Nat := 4983230072969 + 3 ^ 40 * 67474 * 2
def baseEnd_67474 : Nat := 15398486080699662828755

theorem tailTrace_67474 : CollatzResearch.WordTrace tailWord_67474 prefixEnd_67474 15398486080699662828755 := by
  unfold tailWord_67474
  simp only [CollatzResearch.WordTrace]
  refine ⟨615244739390174121716369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1640652638373797657910317 615244739390174121716369)
  ·
    refine ⟨461433554542630591287277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 615244739390174121716369 461433554542630591287277)
    ·
      refine ⟨173037582953486471732729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 461433554542630591287277 173037582953486471732729)
      ·
        refine ⟨129778187215114853799547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173037582953486471732729 129778187215114853799547)
        ·
          refine ⟨194667280822672280699321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129778187215114853799547 194667280822672280699321)
          ·
            refine ⟨146000460617004210524491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194667280822672280699321 146000460617004210524491)
            ·
              refine ⟨219000690925506315786737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146000460617004210524491 219000690925506315786737)
              ·
                refine ⟨164250518194129736840053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219000690925506315786737 164250518194129736840053)
                ·
                  refine ⟨15398486080699662828755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164250518194129736840053 15398486080699662828755)
                  ·
                    rfl

theorem cell21_67474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_67474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67474 prefixEnd_67474 := by exact prefixLift 67474
  have htrace : WordTrace (prefixWord ++ tailWord_67474) baseStart_67474 baseEnd_67474 := by
    simpa [prefixWord, tailWord_67474, baseEnd_67474] using wordTrace_append hprefix tailTrace_67474
  have hstable : (prefixWord ++ tailWord_67474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67474).length < 2 ^ (prefixWord ++ tailWord_67474).sum := by decide
  have hdescent : baseEnd_67474 < baseStart_67474 := by decide
  rcases family_descends (prefixWord ++ tailWord_67474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67505 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 4]
def baseStart_67505 : Nat := 118140960795 + 67505 * 2 ^ 59
def prefixEnd_67505 : Nat := 4983230072969 + 3 ^ 40 * 67505 * 2
def baseEnd_67505 : Nat := 15405560703050497812025

theorem tailTrace_67505 : CollatzResearch.WordTrace tailWord_67505 prefixEnd_67505 15405560703050497812025 := by
  unfold tailWord_67505
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462109620448388781243969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1641406413632259187495979 2462109620448388781243969)
  ·
    refine ⟨1846582215336291585932977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2462109620448388781243969 1846582215336291585932977)
    ·
      refine ⟨1384936661502218689449733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1846582215336291585932977 1384936661502218689449733)
      ·
        refine ⟨259675624031666004271825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1384936661502218689449733 259675624031666004271825)
        ·
          refine ⟨194756718023749503203869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259675624031666004271825 194756718023749503203869)
          ·
            refine ⟨73033769258906063701451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194756718023749503203869 73033769258906063701451)
            ·
              refine ⟨109550653888359095552177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73033769258906063701451 109550653888359095552177)
              ·
                refine ⟨82162990416269321664133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109550653888359095552177 82162990416269321664133)
                ·
                  refine ⟨15405560703050497812025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82162990416269321664133 15405560703050497812025)
                  ·
                    rfl

theorem cell21_67505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_67505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67505 prefixEnd_67505 := by exact prefixLift 67505
  have htrace : WordTrace (prefixWord ++ tailWord_67505) baseStart_67505 baseEnd_67505 := by
    simpa [prefixWord, tailWord_67505, baseEnd_67505] using wordTrace_append hprefix tailTrace_67505
  have hstable : (prefixWord ++ tailWord_67505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67505).length < 2 ^ (prefixWord ++ tailWord_67505).sum := by decide
  have hdescent : baseEnd_67505 < baseStart_67505 := by decide
  rcases family_descends (prefixWord ++ tailWord_67505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67592 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_67592 : Nat := 118140960795 + 67592 * 2 ^ 59
def prefixEnd_67592 : Nat := 4983230072969 + 3 ^ 40 * 67592 * 2
def baseEnd_67592 : Nat := 15425415288357679861847

theorem tailTrace_67592 : CollatzResearch.WordTrace tailWord_67592 prefixEnd_67592 15425415288357679861847 := by
  unfold tailWord_67592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232641385566601319830515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1643521847422135093107353 1232641385566601319830515)
  ·
    refine ⟨1848962078349901979745773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1232641385566601319830515 1848962078349901979745773)
    ·
      refine ⟨693360779381213242404665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1848962078349901979745773 693360779381213242404665)
      ·
        refine ⟨520020584535909931803499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693360779381213242404665 520020584535909931803499)
        ·
          refine ⟨780030876803864897705249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520020584535909931803499 780030876803864897705249)
          ·
            refine ⟨585023157602898673278937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780030876803864897705249 585023157602898673278937)
            ·
              refine ⟨438767368202174004959203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585023157602898673278937 438767368202174004959203)
              ·
                refine ⟨658151052303261007438805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438767368202174004959203 658151052303261007438805)
                ·
                  refine ⟨15425415288357679861847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 658151052303261007438805 15425415288357679861847)
                  ·
                    rfl

theorem cell21_67592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_67592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67592 prefixEnd_67592 := by exact prefixLift 67592
  have htrace : WordTrace (prefixWord ++ tailWord_67592) baseStart_67592 baseEnd_67592 := by
    simpa [prefixWord, tailWord_67592, baseEnd_67592] using wordTrace_append hprefix tailTrace_67592
  have hstable : (prefixWord ++ tailWord_67592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67592).length < 2 ^ (prefixWord ++ tailWord_67592).sum := by decide
  have hdescent : baseEnd_67592 < baseStart_67592 := by decide
  rcases family_descends (prefixWord ++ tailWord_67592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67609 : List Nat := [1, 2, 1, 2, 1, 1, 3, 7, 3]
def baseStart_67609 : Nat := 118140960795 + 67609 * 2 ^ 59
def prefixEnd_67609 : Nat := 4983230072969 + 3 ^ 40 * 67609 * 2
def baseEnd_67609 : Nat := 15429294919969428078479

theorem tailTrace_67609 : CollatzResearch.WordTrace tailWord_67609 prefixEnd_67609 15429294919969428078479 := by
  unfold tailWord_67609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465902812071614543029881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1643935208047743028686587 2465902812071614543029881)
  ·
    refine ⟨1849427109053710907272411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2465902812071614543029881 1849427109053710907272411)
    ·
      refine ⟨2774140663580566360908617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849427109053710907272411 2774140663580566360908617)
      ·
        refine ⟨2080605497685424770681463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774140663580566360908617 2080605497685424770681463)
        ·
          refine ⟨3120908246528137156022195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080605497685424770681463 3120908246528137156022195)
          ·
            refine ⟨4681362369792205734033293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3120908246528137156022195 4681362369792205734033293)
            ·
              refine ⟨1755510888672077150262485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4681362369792205734033293 1755510888672077150262485)
              ·
                refine ⟨41144786453251808209277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1755510888672077150262485 41144786453251808209277)
                ·
                  refine ⟨15429294919969428078479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41144786453251808209277 15429294919969428078479)
                  ·
                    rfl

theorem cell21_67609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_67609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67609 prefixEnd_67609 := by exact prefixLift 67609
  have htrace : WordTrace (prefixWord ++ tailWord_67609) baseStart_67609 baseEnd_67609 := by
    simpa [prefixWord, tailWord_67609, baseEnd_67609] using wordTrace_append hprefix tailTrace_67609
  have hstable : (prefixWord ++ tailWord_67609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67609).length < 2 ^ (prefixWord ++ tailWord_67609).sum := by decide
  have hdescent : baseEnd_67609 < baseStart_67609 := by decide
  rcases family_descends (prefixWord ++ tailWord_67609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67668 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_67668 : Nat := 118140960795 + 67668 * 2 ^ 59
def prefixEnd_67668 : Nat := 4983230072969 + 3 ^ 40 * 67668 * 2
def baseEnd_67668 : Nat := 15442759523798436595025

theorem tailTrace_67668 : CollatzResearch.WordTrace tailWord_67668 prefixEnd_67668 15442759523798436595025 := by
  unfold tailWord_67668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1234027359428933809713829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1645369812571911746285105 1234027359428933809713829)
  ·
    refine ⟨231380129892925089321343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1234027359428933809713829 231380129892925089321343)
    ·
      refine ⟨347070194839387633982015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231380129892925089321343 347070194839387633982015)
      ·
        refine ⟨520605292259081450973023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347070194839387633982015 520605292259081450973023)
        ·
          refine ⟨780907938388622176459535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520605292259081450973023 780907938388622176459535)
          ·
            refine ⟨1171361907582933264689303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780907938388622176459535 1171361907582933264689303)
            ·
              refine ⟨1757042861374399897033955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171361907582933264689303 1757042861374399897033955)
              ·
                refine ⟨2635564292061599845550933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1757042861374399897033955 2635564292061599845550933)
                ·
                  refine ⟨15442759523798436595025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2635564292061599845550933 15442759523798436595025)
                  ·
                    rfl

theorem cell21_67668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_67668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67668 prefixEnd_67668 := by exact prefixLift 67668
  have htrace : WordTrace (prefixWord ++ tailWord_67668) baseStart_67668 baseEnd_67668 := by
    simpa [prefixWord, tailWord_67668, baseEnd_67668] using wordTrace_append hprefix tailTrace_67668
  have hstable : (prefixWord ++ tailWord_67668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67668).length < 2 ^ (prefixWord ++ tailWord_67668).sum := by decide
  have hdescent : baseEnd_67668 < baseStart_67668 := by decide
  rcases family_descends (prefixWord ++ tailWord_67668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67685 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_67685 : Nat := 118140960795 + 67685 * 2 ^ 59
def prefixEnd_67685 : Nat := 4983230072969 + 3 ^ 40 * 67685 * 2
def baseEnd_67685 : Nat := 15446639155410184811657

theorem tailTrace_67685 : CollatzResearch.WordTrace tailWord_67685 prefixEnd_67685 15446639155410184811657 := by
  unfold tailWord_67685
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468674759796279522796509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1645783173197519681864339 2468674759796279522796509)
  ·
    refine ⟨925753034923604821048691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2468674759796279522796509 925753034923604821048691)
    ·
      refine ⟨1388629552385407231573037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925753034923604821048691 1388629552385407231573037)
      ·
        refine ⟨520736082144527711839889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1388629552385407231573037 520736082144527711839889)
        ·
          refine ⟨390552061608395783879917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520736082144527711839889 390552061608395783879917)
          ·
            refine ⟨146457023103148418954969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 390552061608395783879917 146457023103148418954969)
            ·
              refine ⟨109842767327361314216227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146457023103148418954969 109842767327361314216227)
              ·
                refine ⟨164764150991041971324341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109842767327361314216227 164764150991041971324341)
                ·
                  refine ⟨15446639155410184811657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164764150991041971324341 15446639155410184811657)
                  ·
                    rfl

theorem cell21_67685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_67685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67685 prefixEnd_67685 := by exact prefixLift 67685
  have htrace : WordTrace (prefixWord ++ tailWord_67685) baseStart_67685 baseEnd_67685 := by
    simpa [prefixWord, tailWord_67685, baseEnd_67685] using wordTrace_append hprefix tailTrace_67685
  have hstable : (prefixWord ++ tailWord_67685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67685).length < 2 ^ (prefixWord ++ tailWord_67685).sum := by decide
  have hdescent : baseEnd_67685 < baseStart_67685 := by decide
  rcases family_descends (prefixWord ++ tailWord_67685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67820 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_67820 : Nat := 118140960795 + 67820 * 2 ^ 59
def prefixEnd_67820 : Nat := 4983230072969 + 3 ^ 40 * 67820 * 2
def baseEnd_67820 : Nat := 15477447994679950061381

theorem tailTrace_67820 : CollatzResearch.WordTrace tailWord_67820 prefixEnd_67820 15477447994679950061381 := by
  unfold tailWord_67820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236799307153598789480457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1649065742871465052640609 1236799307153598789480457)
  ·
    refine ⟨927599480365199092110343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1236799307153598789480457 927599480365199092110343)
    ·
      refine ⟨1391399220547798638165515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927599480365199092110343 1391399220547798638165515)
      ·
        refine ⟨2087098830821697957248273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391399220547798638165515 2087098830821697957248273)
        ·
          refine ⟨1565324123116273467936205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087098830821697957248273 1565324123116273467936205)
          ·
            refine ⟨586996546168602550476077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1565324123116273467936205 586996546168602550476077)
            ·
              refine ⟨220123704813225956428529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586996546168602550476077 220123704813225956428529)
              ·
                refine ⟨165092778609919467321397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220123704813225956428529 165092778609919467321397)
                ·
                  refine ⟨15477447994679950061381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165092778609919467321397 15477447994679950061381)
                  ·
                    rfl

theorem cell21_67820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_67820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67820 prefixEnd_67820 := by exact prefixLift 67820
  have htrace : WordTrace (prefixWord ++ tailWord_67820) baseStart_67820 baseEnd_67820 := by
    simpa [prefixWord, tailWord_67820, baseEnd_67820] using wordTrace_append hprefix tailTrace_67820
  have hstable : (prefixWord ++ tailWord_67820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67820).length < 2 ^ (prefixWord ++ tailWord_67820).sum := by decide
  have hdescent : baseEnd_67820 < baseStart_67820 := by decide
  rcases family_descends (prefixWord ++ tailWord_67820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67927 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 4]
def baseStart_67927 : Nat := 118140960795 + 67927 * 2 ^ 59
def prefixEnd_67927 : Nat := 4983230072969 + 3 ^ 40 * 67927 * 2
def baseEnd_67927 : Nat := 15501866852471541777829

theorem tailTrace_67927 : CollatzResearch.WordTrace tailWord_67927 prefixEnd_67927 15501866852471541777829 := by
  unfold tailWord_67927
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477501224919554853106035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1651667483279703235404023 2477501224919554853106035)
  ·
    refine ⟨3716251837379332279659053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2477501224919554853106035 3716251837379332279659053)
    ·
      refine ⟨1393594439017249604872145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3716251837379332279659053 1393594439017249604872145)
      ·
        refine ⟨1045195829262937203654109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1393594439017249604872145 1045195829262937203654109)
        ·
          refine ⟨391948435973601451370291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1045195829262937203654109 391948435973601451370291)
          ·
            refine ⟨587922653960402177055437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391948435973601451370291 587922653960402177055437)
            ·
              refine ⟨220470995235150816395789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587922653960402177055437 220470995235150816395789)
              ·
                refine ⟨82676623213181556148421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220470995235150816395789 82676623213181556148421)
                ·
                  refine ⟨15501866852471541777829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82676623213181556148421 15501866852471541777829)
                  ·
                    rfl

theorem cell21_67927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 4].length) (baseStart_67927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67927 prefixEnd_67927 := by exact prefixLift 67927
  have htrace : WordTrace (prefixWord ++ tailWord_67927) baseStart_67927 baseEnd_67927 := by
    simpa [prefixWord, tailWord_67927, baseEnd_67927] using wordTrace_append hprefix tailTrace_67927
  have hstable : (prefixWord ++ tailWord_67927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67927).length < 2 ^ (prefixWord ++ tailWord_67927).sum := by decide
  have hdescent : baseEnd_67927 < baseStart_67927 := by decide
  rcases family_descends (prefixWord ++ tailWord_67927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67941 : List Nat := [1, 3, 1, 3, 1, 3, 2, 7]
def baseStart_67941 : Nat := 118140960795 + 67941 * 2 ^ 59
def prefixEnd_67941 : Nat := 4983230072969 + 3 ^ 40 * 67941 * 2
def baseEnd_67941 : Nat := 5168353947736876181489

theorem tailTrace_67941 : CollatzResearch.WordTrace tailWord_67941 prefixEnd_67941 5168353947736876181489 := by
  unfold tailWord_67941
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478011846868835244115677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1652007897912556829410451 2478011846868835244115677)
  ·
    refine ⟨929254442575813216543379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2478011846868835244115677 929254442575813216543379)
    ·
      refine ⟨1393881663863719824815069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929254442575813216543379 1393881663863719824815069)
      ·
        refine ⟨522705623948894934305651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1393881663863719824815069 522705623948894934305651)
        ·
          refine ⟨784058435923342401458477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522705623948894934305651 784058435923342401458477)
          ·
            refine ⟨294021913471253400546929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 784058435923342401458477 294021913471253400546929)
            ·
              refine ⟨220516435103440050410197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294021913471253400546929 220516435103440050410197)
              ·
                refine ⟨5168353947736876181489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 220516435103440050410197 5168353947736876181489)
                ·
                  rfl

theorem cell21_67941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_67941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67941 prefixEnd_67941 := by exact prefixLift 67941
  have htrace : WordTrace (prefixWord ++ tailWord_67941) baseStart_67941 baseEnd_67941 := by
    simpa [prefixWord, tailWord_67941, baseEnd_67941] using wordTrace_append hprefix tailTrace_67941
  have hstable : (prefixWord ++ tailWord_67941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67941).length < 2 ^ (prefixWord ++ tailWord_67941).sum := by decide
  have hdescent : baseEnd_67941 < baseStart_67941 := by decide
  rcases family_descends (prefixWord ++ tailWord_67941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67955 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_67955 : Nat := 118140960795 + 67955 * 2 ^ 59
def prefixEnd_67955 : Nat := 4983230072969 + 3 ^ 40 * 67955 * 2
def baseEnd_67955 : Nat := 15508256833949715311105

theorem tailTrace_67955 : CollatzResearch.WordTrace tailWord_67955 prefixEnd_67955 15508256833949715311105 := by
  unfold tailWord_67955
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478522468818115635125319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1652348312545410423416879 2478522468818115635125319)
  ·
    refine ⟨3717783703227173452687979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2478522468818115635125319 3717783703227173452687979)
    ·
      refine ⟨5576675554840760179031969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3717783703227173452687979 5576675554840760179031969)
      ·
        refine ⟨4182506666130570134273977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5576675554840760179031969 4182506666130570134273977)
        ·
          refine ⟨3136879999597927600705483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4182506666130570134273977 3136879999597927600705483)
          ·
            refine ⟨4705319999396891401058225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136879999597927600705483 4705319999396891401058225)
            ·
              refine ⟨3528989999547668550793669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705319999396891401058225 3528989999547668550793669)
              ·
                refine ⟨661685624915187853273813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3528989999547668550793669 661685624915187853273813)
                ·
                  refine ⟨15508256833949715311105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 661685624915187853273813 15508256833949715311105)
                  ·
                    rfl

theorem cell21_67955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_67955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67955 prefixEnd_67955 := by exact prefixLift 67955
  have htrace : WordTrace (prefixWord ++ tailWord_67955) baseStart_67955 baseEnd_67955 := by
    simpa [prefixWord, tailWord_67955, baseEnd_67955] using wordTrace_append hprefix tailTrace_67955
  have hstable : (prefixWord ++ tailWord_67955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67955).length < 2 ^ (prefixWord ++ tailWord_67955).sum := by decide
  have hdescent : baseEnd_67955 < baseStart_67955 := by decide
  rcases family_descends (prefixWord ++ tailWord_67955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67958 : List Nat := [5, 1, 1, 4, 10]
def baseStart_67958 : Nat := 118140960795 + 67958 * 2 ^ 59
def prefixEnd_67958 : Nat := 4983230072969 + 3 ^ 40 * 67958 * 2
def baseEnd_67958 : Nat := 191468413269412058779

theorem tailTrace_67958 : CollatzResearch.WordTrace tailWord_67958 prefixEnd_67958 191468413269412058779 := by
  unfold tailWord_67958
  simp only [CollatzResearch.WordTrace]
  refine ⟨154914492987952946717783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1652421258538164764989685 154914492987952946717783)
  ·
    refine ⟨232371739481929420076675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154914492987952946717783 232371739481929420076675)
    ·
      refine ⟨348557609222894130115013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232371739481929420076675 348557609222894130115013)
      ·
        refine ⟨65354551729292649396565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 348557609222894130115013 65354551729292649396565)
        ·
          refine ⟨191468413269412058779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 65354551729292649396565 191468413269412058779)
          ·
            rfl

theorem cell21_67958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 10].length) (baseStart_67958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67958 prefixEnd_67958 := by exact prefixLift 67958
  have htrace : WordTrace (prefixWord ++ tailWord_67958) baseStart_67958 baseEnd_67958 := by
    simpa [prefixWord, tailWord_67958, baseEnd_67958] using wordTrace_append hprefix tailTrace_67958
  have hstable : (prefixWord ++ tailWord_67958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67958).length < 2 ^ (prefixWord ++ tailWord_67958).sum := by decide
  have hdescent : baseEnd_67958 < baseStart_67958 := by decide
  rcases family_descends (prefixWord ++ tailWord_67958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67972 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_67972 : Nat := 118140960795 + 67972 * 2 ^ 59
def prefixEnd_67972 : Nat := 4983230072969 + 3 ^ 40 * 67972 * 2
def baseEnd_67972 : Nat := 15512136465561463527737

theorem tailTrace_67972 : CollatzResearch.WordTrace tailWord_67972 prefixEnd_67972 15512136465561463527737 := by
  unfold tailWord_67972
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239571254878263769247085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1652761673171018358996113 1239571254878263769247085)
  ·
    refine ⟨464839220579348913467657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1239571254878263769247085 464839220579348913467657)
    ·
      refine ⟨348629415434511685100743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464839220579348913467657 348629415434511685100743)
      ·
        refine ⟨522944123151767527651115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348629415434511685100743 522944123151767527651115)
        ·
          refine ⟨784416184727651291476673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522944123151767527651115 784416184727651291476673)
          ·
            refine ⟨588312138545738468607505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784416184727651291476673 588312138545738468607505)
            ·
              refine ⟨441234103909303851455629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588312138545738468607505 441234103909303851455629)
              ·
                refine ⟨165462788965988944295861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441234103909303851455629 165462788965988944295861)
                ·
                  refine ⟨15512136465561463527737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165462788965988944295861 15512136465561463527737)
                  ·
                    rfl

theorem cell21_67972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_67972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_67972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_67972 prefixEnd_67972 := by exact prefixLift 67972
  have htrace : WordTrace (prefixWord ++ tailWord_67972) baseStart_67972 baseEnd_67972 := by
    simpa [prefixWord, tailWord_67972, baseEnd_67972] using wordTrace_append hprefix tailTrace_67972
  have hstable : (prefixWord ++ tailWord_67972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67972).length < 2 ^ (prefixWord ++ tailWord_67972).sum := by decide
  have hdescent : baseEnd_67972 < baseStart_67972 := by decide
  rcases family_descends (prefixWord ++ tailWord_67972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68017 : List Nat := [1, 2, 2, 4, 1, 3, 8]
def baseStart_68017 : Nat := 118140960795 + 68017 * 2 ^ 59
def prefixEnd_68017 : Nat := 4983230072969 + 3 ^ 40 * 68017 * 2
def baseEnd_68017 : Nat := 1724711786516820586405

theorem tailTrace_68017 : CollatzResearch.WordTrace tailWord_68017 prefixEnd_68017 1724711786516820586405 := by
  unfold tailWord_68017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480783794593500223882305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1653855863062333482588203 2480783794593500223882305)
  ·
    refine ⟨1860587845945125167911729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2480783794593500223882305 1860587845945125167911729)
    ·
      refine ⟨1395440884458843875933797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1860587845945125167911729 1395440884458843875933797)
      ·
        refine ⟨261645165836033226737587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1395440884458843875933797 261645165836033226737587)
        ·
          refine ⟨392467748754049840106381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261645165836033226737587 392467748754049840106381)
          ·
            refine ⟨147175405782768690039893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392467748754049840106381 147175405782768690039893)
            ·
              refine ⟨1724711786516820586405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 147175405782768690039893 1724711786516820586405)
              ·
                rfl

theorem cell21_68017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 8].length) (baseStart_68017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68017 prefixEnd_68017 := by exact prefixLift 68017
  have htrace : WordTrace (prefixWord ++ tailWord_68017) baseStart_68017 baseEnd_68017 := by
    simpa [prefixWord, tailWord_68017, baseEnd_68017] using wordTrace_append hprefix tailTrace_68017
  have hstable : (prefixWord ++ tailWord_68017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68017).length < 2 ^ (prefixWord ++ tailWord_68017).sum := by decide
  have hdescent : baseEnd_68017 < baseStart_68017 := by decide
  rcases family_descends (prefixWord ++ tailWord_68017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68082 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_68082 : Nat := 118140960795 + 68082 * 2 ^ 59
def prefixEnd_68082 : Nat := 4983230072969 + 3 ^ 40 * 68082 * 2
def baseEnd_68082 : Nat := 15537239964225716694179

theorem tailTrace_68082 : CollatzResearch.WordTrace tailWord_68082 prefixEnd_68082 15537239964225716694179 := by
  unfold tailWord_68082
  simp only [CollatzResearch.WordTrace]
  refine ⟨620788634839504081249625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1655436359572010883332333 620788634839504081249625)
  ·
    refine ⟨465591476129628060937219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 620788634839504081249625 465591476129628060937219)
    ·
      refine ⟨698387214194442091405829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465591476129628060937219 698387214194442091405829)
      ·
        refine ⟨130947602661457892138593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 698387214194442091405829 130947602661457892138593)
        ·
          refine ⟨98210701996093419103945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130947602661457892138593 98210701996093419103945)
          ·
            refine ⟨73658026497070064327959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98210701996093419103945 73658026497070064327959)
            ·
              refine ⟨110487039745605096491939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73658026497070064327959 110487039745605096491939)
              ·
                refine ⟨165730559618407644737909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110487039745605096491939 165730559618407644737909)
                ·
                  refine ⟨15537239964225716694179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165730559618407644737909 15537239964225716694179)
                  ·
                    rfl

theorem cell21_68082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_68082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68082 prefixEnd_68082 := by exact prefixLift 68082
  have htrace : WordTrace (prefixWord ++ tailWord_68082) baseStart_68082 baseEnd_68082 := by
    simpa [prefixWord, tailWord_68082, baseEnd_68082] using wordTrace_append hprefix tailTrace_68082
  have hstable : (prefixWord ++ tailWord_68082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68082).length < 2 ^ (prefixWord ++ tailWord_68082).sum := by decide
  have hdescent : baseEnd_68082 < baseStart_68082 := by decide
  rcases family_descends (prefixWord ++ tailWord_68082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68093 : List Nat := [1, 4, 1, 1, 1, 3, 4, 6]
def baseStart_68093 : Nat := 118140960795 + 68093 * 2 ^ 59
def prefixEnd_68093 : Nat := 4983230072969 + 3 ^ 40 * 68093 * 2
def baseEnd_68093 : Nat := 5179916771364047336941

theorem tailTrace_68093 : CollatzResearch.WordTrace tailWord_68093 prefixEnd_68093 5179916771364047336941 := by
  unfold tailWord_68093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483555742318165203648933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1655703828212110135765955 2483555742318165203648933)
  ·
    refine ⟨465666701684655975684175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2483555742318165203648933 465666701684655975684175)
    ·
      refine ⟨698500052526983963526263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465666701684655975684175 698500052526983963526263)
      ·
        refine ⟨1047750078790475945289395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 698500052526983963526263 1047750078790475945289395)
        ·
          refine ⟨1571625118185713917934093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047750078790475945289395 1571625118185713917934093)
          ·
            refine ⟨589359419319642719225285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1571625118185713917934093 589359419319642719225285)
            ·
              refine ⟨110504891122433009854741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 589359419319642719225285 110504891122433009854741)
              ·
                refine ⟨5179916771364047336941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110504891122433009854741 5179916771364047336941)
                ·
                  rfl

theorem cell21_68093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_68093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68093 prefixEnd_68093 := by exact prefixLift 68093
  have htrace : WordTrace (prefixWord ++ tailWord_68093) baseStart_68093 baseEnd_68093 := by
    simpa [prefixWord, tailWord_68093, baseEnd_68093] using wordTrace_append hprefix tailTrace_68093
  have hstable : (prefixWord ++ tailWord_68093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68093).length < 2 ^ (prefixWord ++ tailWord_68093).sum := by decide
  have hdescent : baseEnd_68093 < baseStart_68093 := by decide
  rcases family_descends (prefixWord ++ tailWord_68093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68158 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_68158 : Nat := 118140960795 + 68158 * 2 ^ 59
def prefixEnd_68158 : Nat := 4983230072969 + 3 ^ 40 * 68158 * 2
def baseEnd_68158 : Nat := 15554584199666473427357

theorem tailTrace_68158 : CollatzResearch.WordTrace tailWord_68158 prefixEnd_68158 15554584199666473427357 := by
  unfold tailWord_68158
  simp only [CollatzResearch.WordTrace]
  refine ⟨310740810885335163095641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1657284324721787536510085 310740810885335163095641)
  ·
    refine ⟨233055608164001372321731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 310740810885335163095641 233055608164001372321731)
    ·
      refine ⟨349583412246002058482597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233055608164001372321731 349583412246002058482597)
      ·
        refine ⟨65546889796125385965487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 349583412246002058482597 65546889796125385965487)
        ·
          refine ⟨98320334694188078948231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65546889796125385965487 98320334694188078948231)
          ·
            refine ⟨147480502041282118422347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98320334694188078948231 147480502041282118422347)
            ·
              refine ⟨221220753061923177633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147480502041282118422347 221220753061923177633521)
              ·
                refine ⟨165915564796442383225141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221220753061923177633521 165915564796442383225141)
                ·
                  refine ⟨15554584199666473427357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165915564796442383225141 15554584199666473427357)
                  ·
                    rfl

theorem cell21_68158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_68158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68158 prefixEnd_68158 := by exact prefixLift 68158
  have htrace : WordTrace (prefixWord ++ tailWord_68158) baseStart_68158 baseEnd_68158 := by
    simpa [prefixWord, tailWord_68158, baseEnd_68158] using wordTrace_append hprefix tailTrace_68158
  have hstable : (prefixWord ++ tailWord_68158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68158).length < 2 ^ (prefixWord ++ tailWord_68158).sum := by decide
  have hdescent : baseEnd_68158 < baseStart_68158 := by decide
  rcases family_descends (prefixWord ++ tailWord_68158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68183 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_68183 : Nat := 118140960795 + 68183 * 2 ^ 59
def prefixEnd_68183 : Nat := 4983230072969 + 3 ^ 40 * 68183 * 2
def baseEnd_68183 : Nat := 15560289540271985510639

theorem tailTrace_68183 : CollatzResearch.WordTrace tailWord_68183 prefixEnd_68183 15560289540271985510639 := by
  unfold tailWord_68183
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486838311992110574425203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1657892207994740382950135 2486838311992110574425203)
  ·
    refine ⟨3730257467988165861637805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486838311992110574425203 3730257467988165861637805)
    ·
      refine ⟨1398846550495562198114177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3730257467988165861637805 1398846550495562198114177)
      ·
        refine ⟨1049134912871671648585633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1398846550495562198114177 1049134912871671648585633)
        ·
          refine ⟨786851184653753736439225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1049134912871671648585633 786851184653753736439225)
          ·
            refine ⟨590138388490315302329419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786851184653753736439225 590138388490315302329419)
            ·
              refine ⟨885207582735472953494129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590138388490315302329419 885207582735472953494129)
              ·
                refine ⟨663905687051604715120597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 885207582735472953494129 663905687051604715120597)
                ·
                  refine ⟨15560289540271985510639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 663905687051604715120597 15560289540271985510639)
                  ·
                    rfl

theorem cell21_68183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_68183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68183 prefixEnd_68183 := by exact prefixLift 68183
  have htrace : WordTrace (prefixWord ++ tailWord_68183) baseStart_68183 baseEnd_68183 := by
    simpa [prefixWord, tailWord_68183, baseEnd_68183] using wordTrace_append hprefix tailTrace_68183
  have hstable : (prefixWord ++ tailWord_68183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68183).length < 2 ^ (prefixWord ++ tailWord_68183).sum := by decide
  have hdescent : baseEnd_68183 < baseStart_68183 := by decide
  rcases family_descends (prefixWord ++ tailWord_68183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68226 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_68226 : Nat := 118140960795 + 68226 * 2 ^ 59
def prefixEnd_68226 : Nat := 4983230072969 + 3 ^ 40 * 68226 * 2
def baseEnd_68226 : Nat := 15570102726113466293885

theorem tailTrace_68226 : CollatzResearch.WordTrace tailWord_68226 prefixEnd_68226 15570102726113466293885 := by
  unfold tailWord_68226
  simp only [CollatzResearch.WordTrace]
  refine ⟨622101662709082229560133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1658937767224219278827021 622101662709082229560133)
  ·
    refine ⟨116644061757952918042525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 622101662709082229560133 116644061757952918042525)
    ·
      refine ⟨43741523159232344265947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116644061757952918042525 43741523159232344265947)
      ·
        refine ⟨65612284738848516398921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43741523159232344265947 65612284738848516398921)
        ·
          refine ⟨49209213554136387299191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65612284738848516398921 49209213554136387299191)
          ·
            refine ⟨73813820331204580948787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49209213554136387299191 73813820331204580948787)
            ·
              refine ⟨110720730496806871423181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73813820331204580948787 110720730496806871423181)
              ·
                refine ⟨41520273936302576783693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110720730496806871423181 41520273936302576783693)
                ·
                  refine ⟨15570102726113466293885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41520273936302576783693 15570102726113466293885)
                  ·
                    rfl

theorem cell21_68226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_68226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68226 prefixEnd_68226 := by exact prefixLift 68226
  have htrace : WordTrace (prefixWord ++ tailWord_68226) baseStart_68226 baseEnd_68226 := by
    simpa [prefixWord, tailWord_68226, baseEnd_68226] using wordTrace_append hprefix tailTrace_68226
  have hstable : (prefixWord ++ tailWord_68226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68226).length < 2 ^ (prefixWord ++ tailWord_68226).sum := by decide
  have hdescent : baseEnd_68226 < baseStart_68226 := by decide
  rcases family_descends (prefixWord ++ tailWord_68226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68259 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_68259 : Nat := 118140960795 + 68259 * 2 ^ 59
def prefixEnd_68259 : Nat := 4983230072969 + 3 ^ 40 * 68259 * 2
def baseEnd_68259 : Nat := 15577633775712742243817

theorem tailTrace_68259 : CollatzResearch.WordTrace tailWord_68259 prefixEnd_68259 15577633775712742243817 := by
  unfold tailWord_68259
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489610259716775554191831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1659740173144517036127887 2489610259716775554191831)
  ·
    refine ⟨3734415389575163331287747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2489610259716775554191831 3734415389575163331287747)
    ·
      refine ⟨5601623084362744996931621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734415389575163331287747 5601623084362744996931621)
      ·
        refine ⟨1050304328318014686924679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5601623084362744996931621 1050304328318014686924679)
        ·
          refine ⟨1575456492477022030387019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050304328318014686924679 1575456492477022030387019)
          ·
            refine ⟨2363184738715533045580529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575456492477022030387019 2363184738715533045580529)
            ·
              refine ⟨1772388554036649784185397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363184738715533045580529 1772388554036649784185397)
              ·
                refine ⟨166161426940935917267381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1772388554036649784185397 166161426940935917267381)
                ·
                  refine ⟨15577633775712742243817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166161426940935917267381 15577633775712742243817)
                  ·
                    rfl

theorem cell21_68259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_68259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68259 prefixEnd_68259 := by exact prefixLift 68259
  have htrace : WordTrace (prefixWord ++ tailWord_68259) baseStart_68259 baseEnd_68259 := by
    simpa [prefixWord, tailWord_68259, baseEnd_68259] using wordTrace_append hprefix tailTrace_68259
  have hstable : (prefixWord ++ tailWord_68259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68259).length < 2 ^ (prefixWord ++ tailWord_68259).sum := by decide
  have hdescent : baseEnd_68259 < baseStart_68259 := by decide
  rcases family_descends (prefixWord ++ tailWord_68259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68321 : List Nat := [1, 2, 3, 1, 4, 1, 3, 6]
def baseStart_68321 : Nat := 118140960795 + 68321 * 2 ^ 59
def prefixEnd_68321 : Nat := 4983230072969 + 3 ^ 40 * 68321 * 2
def baseEnd_68321 : Nat := 5197261006804804070119

theorem tailTrace_68321 : CollatzResearch.WordTrace tailWord_68321 prefixEnd_68321 5197261006804804070119 := by
  unfold tailWord_68321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2491871585492160142948817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1661247723661440095299211 2491871585492160142948817)
  ·
    refine ⟨1868903689119120107211613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2491871585492160142948817 1868903689119120107211613)
    ·
      refine ⟨700838883419670040204355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1868903689119120107211613 700838883419670040204355)
      ·
        refine ⟨1051258325129505060306533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700838883419670040204355 1051258325129505060306533)
        ·
          refine ⟨197110935961782198807475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1051258325129505060306533 197110935961782198807475)
          ·
            refine ⟨295666403942673298211213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197110935961782198807475 295666403942673298211213)
            ·
              refine ⟨110874901478502486829205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 295666403942673298211213 110874901478502486829205)
              ·
                refine ⟨5197261006804804070119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 110874901478502486829205 5197261006804804070119)
                ·
                  rfl

theorem cell21_68321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_68321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68321 prefixEnd_68321 := by exact prefixLift 68321
  have htrace : WordTrace (prefixWord ++ tailWord_68321) baseStart_68321 baseEnd_68321 := by
    simpa [prefixWord, tailWord_68321, baseEnd_68321] using wordTrace_append hprefix tailTrace_68321
  have hstable : (prefixWord ++ tailWord_68321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68321).length < 2 ^ (prefixWord ++ tailWord_68321).sum := by decide
  have hdescent : baseEnd_68321 < baseStart_68321 := by decide
  rcases family_descends (prefixWord ++ tailWord_68321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68335 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 7]
def baseStart_68335 : Nat := 118140960795 + 68335 * 2 ^ 59
def prefixEnd_68335 : Nat := 4983230072969 + 3 ^ 40 * 68335 * 2
def baseEnd_68335 : Nat := 15594978011153498976995

theorem tailTrace_68335 : CollatzResearch.WordTrace tailWord_68335 prefixEnd_68335 15594978011153498976995 := by
  unfold tailWord_68335
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492382207441440533958459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1661588138294293689305639 2492382207441440533958459)
  ·
    refine ⟨3738573311162160800937689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2492382207441440533958459 3738573311162160800937689)
    ·
      refine ⟨2803929983371620600703267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3738573311162160800937689 2803929983371620600703267)
      ·
        refine ⟨4205894975057430901054901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803929983371620600703267 4205894975057430901054901)
        ·
          refine ⟨394302653911634146973897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4205894975057430901054901 394302653911634146973897)
          ·
            refine ⟨295726990433725610230423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394302653911634146973897 295726990433725610230423)
            ·
              refine ⟨443590485650588415345635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295726990433725610230423 443590485650588415345635)
              ·
                refine ⟨665385728475882623018453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443590485650588415345635 665385728475882623018453)
                ·
                  refine ⟨15594978011153498976995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 665385728475882623018453 15594978011153498976995)
                  ·
                    rfl

theorem cell21_68335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_68335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68335 prefixEnd_68335 := by exact prefixLift 68335
  have htrace : WordTrace (prefixWord ++ tailWord_68335) baseStart_68335 baseEnd_68335 := by
    simpa [prefixWord, tailWord_68335, baseEnd_68335] using wordTrace_append hprefix tailTrace_68335
  have hstable : (prefixWord ++ tailWord_68335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68335).length < 2 ^ (prefixWord ++ tailWord_68335).sum := by decide
  have hdescent : baseEnd_68335 < baseStart_68335 := by decide
  rcases family_descends (prefixWord ++ tailWord_68335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68338 : List Nat := [3, 2, 1, 3, 1, 3, 3, 5]
def baseStart_68338 : Nat := 118140960795 + 68338 * 2 ^ 59
def prefixEnd_68338 : Nat := 4983230072969 + 3 ^ 40 * 68338 * 2
def baseEnd_68338 : Nat := 5198554217342053475663

theorem tailTrace_68338 : CollatzResearch.WordTrace tailWord_68338 prefixEnd_68338 5198554217342053475663 := by
  unfold tailWord_68338
  simp only [CollatzResearch.WordTrace]
  refine ⟨623122906607643011579417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1661661084287048030878445 623122906607643011579417)
  ·
    refine ⟨467342179955732258684563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 623122906607643011579417 467342179955732258684563)
    ·
      refine ⟨701013269933598388026845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467342179955732258684563 701013269933598388026845)
      ·
        refine ⟨262879976225099395510067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 701013269933598388026845 262879976225099395510067)
        ·
          refine ⟨394319964337649093265101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262879976225099395510067 394319964337649093265101)
          ·
            refine ⟨147869986626618409974413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394319964337649093265101 147869986626618409974413)
            ·
              refine ⟨55451244984981903740405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 147869986626618409974413 55451244984981903740405)
              ·
                refine ⟨5198554217342053475663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55451244984981903740405 5198554217342053475663)
                ·
                  rfl

theorem cell21_68338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_68338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68338 prefixEnd_68338 := by exact prefixLift 68338
  have htrace : WordTrace (prefixWord ++ tailWord_68338) baseStart_68338 baseEnd_68338 := by
    simpa [prefixWord, tailWord_68338, baseEnd_68338] using wordTrace_append hprefix tailTrace_68338
  have hstable : (prefixWord ++ tailWord_68338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68338).length < 2 ^ (prefixWord ++ tailWord_68338).sum := by decide
  have hdescent : baseEnd_68338 < baseStart_68338 := by decide
  rcases family_descends (prefixWord ++ tailWord_68338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68414 : List Nat := [4, 2, 1, 2, 3, 2, 7]
def baseStart_68414 : Nat := 118140960795 + 68414 * 2 ^ 59
def prefixEnd_68414 : Nat := 4983230072969 + 3 ^ 40 * 68414 * 2
def baseEnd_68414 : Nat := 1734778543051879684463

theorem tailTrace_68414 : CollatzResearch.WordTrace tailWord_68414 prefixEnd_68414 1734778543051879684463 := by
  unfold tailWord_68414
  simp only [CollatzResearch.WordTrace]
  refine ⟨311907946769404628260537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1663509049436824684056197 311907946769404628260537)
  ·
    refine ⟨233930960077053471195403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311907946769404628260537 233930960077053471195403)
    ·
      refine ⟨350896440115580206793105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233930960077053471195403 350896440115580206793105)
      ·
        refine ⟨263172330086685155094829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350896440115580206793105 263172330086685155094829)
        ·
          refine ⟨98689623782506933160561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263172330086685155094829 98689623782506933160561)
          ·
            refine ⟨74017217836880199870421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98689623782506933160561 74017217836880199870421)
            ·
              refine ⟨1734778543051879684463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74017217836880199870421 1734778543051879684463)
              ·
                rfl

theorem cell21_68414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 7].length) (baseStart_68414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68414 prefixEnd_68414 := by exact prefixLift 68414
  have htrace : WordTrace (prefixWord ++ tailWord_68414) baseStart_68414 baseEnd_68414 := by
    simpa [prefixWord, tailWord_68414, baseEnd_68414] using wordTrace_append hprefix tailTrace_68414
  have hstable : (prefixWord ++ tailWord_68414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68414).length < 2 ^ (prefixWord ++ tailWord_68414).sum := by decide
  have hdescent : baseEnd_68414 < baseStart_68414 := by decide
  rcases family_descends (prefixWord ++ tailWord_68414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68420 : List Nat := [2, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_68420 : Nat := 118140960795 + 68420 * 2 ^ 59
def prefixEnd_68420 : Nat := 4983230072969 + 3 ^ 40 * 68420 * 2
def baseEnd_68420 : Nat := 15614376169212240060155

theorem tailTrace_68420 : CollatzResearch.WordTrace tailWord_68420 prefixEnd_68420 15614376169212240060155 := by
  unfold tailWord_68420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247741206066750025401357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1663654941422333367201809 1247741206066750025401357)
  ·
    refine ⟨467902952275031259525509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1247741206066750025401357 467902952275031259525509)
    ·
      refine ⟨87731803551568361161033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 467902952275031259525509 87731803551568361161033)
      ·
        refine ⟨65798852663676270870775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87731803551568361161033 65798852663676270870775)
        ·
          refine ⟨98698278995514406306163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65798852663676270870775 98698278995514406306163)
          ·
            refine ⟨148047418493271609459245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98698278995514406306163 148047418493271609459245)
            ·
              refine ⟨55517781934976853547217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148047418493271609459245 55517781934976853547217)
              ·
                refine ⟨41638336451232640160413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55517781934976853547217 41638336451232640160413)
                ·
                  refine ⟨15614376169212240060155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41638336451232640160413 15614376169212240060155)
                  ·
                    rfl

theorem cell21_68420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_68420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68420 prefixEnd_68420 := by exact prefixLift 68420
  have htrace : WordTrace (prefixWord ++ tailWord_68420) baseStart_68420 baseEnd_68420 := by
    simpa [prefixWord, tailWord_68420, baseEnd_68420] using wordTrace_append hprefix tailTrace_68420
  have hstable : (prefixWord ++ tailWord_68420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68420).length < 2 ^ (prefixWord ++ tailWord_68420).sum := by decide
  have hdescent : baseEnd_68420 < baseStart_68420 := by decide
  rcases family_descends (prefixWord ++ tailWord_68420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68428 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_68428 : Nat := 118140960795 + 68428 * 2 ^ 59
def prefixEnd_68428 : Nat := 4983230072969 + 3 ^ 40 * 68428 * 2
def baseEnd_68428 : Nat := 15616201878206003926805

theorem tailTrace_68428 : CollatzResearch.WordTrace tailWord_68428 prefixEnd_68428 15616201878206003926805 := by
  unfold tailWord_68428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247887098052258708546969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1663849464069678278062625 1247887098052258708546969)
  ·
    refine ⟨935915323539194031410227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1247887098052258708546969 935915323539194031410227)
    ·
      refine ⟨1403872985308791047115341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935915323539194031410227 1403872985308791047115341)
      ·
        refine ⟨526452369490796642668253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1403872985308791047115341 526452369490796642668253)
        ·
          refine ⟨197419638559048741000595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 526452369490796642668253 197419638559048741000595)
          ·
            refine ⟨296129457838573111500893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197419638559048741000595 296129457838573111500893)
            ·
              refine ⟨111048546689464916812835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296129457838573111500893 111048546689464916812835)
              ·
                refine ⟨166572820034197375219253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111048546689464916812835 166572820034197375219253)
                ·
                  refine ⟨15616201878206003926805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 166572820034197375219253 15616201878206003926805)
                  ·
                    rfl

theorem cell21_68428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_68428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68428 prefixEnd_68428 := by exact prefixLift 68428
  have htrace : WordTrace (prefixWord ++ tailWord_68428) baseStart_68428 baseEnd_68428 := by
    simpa [prefixWord, tailWord_68428, baseEnd_68428] using wordTrace_append hprefix tailTrace_68428
  have hstable : (prefixWord ++ tailWord_68428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68428).length < 2 ^ (prefixWord ++ tailWord_68428).sum := by decide
  have hdescent : baseEnd_68428 < baseStart_68428 := by decide
  rcases family_descends (prefixWord ++ tailWord_68428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68490 : List Nat := [3, 1, 2, 4, 1, 3, 1, 6]
def baseStart_68490 : Nat := 118140960795 + 68490 * 2 ^ 59
def prefixEnd_68490 : Nat := 4983230072969 + 3 ^ 40 * 68490 * 2
def baseEnd_68490 : Nat := 5210117040969224631115

theorem tailTrace_68490 : CollatzResearch.WordTrace tailWord_68490 prefixEnd_68490 5210117040969224631115 := by
  unfold tailWord_68490
  simp only [CollatzResearch.WordTrace]
  refine ⟨624508880469975501462731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1665357014586601337233949 624508880469975501462731)
  ·
    refine ⟨936763320704963252194097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 624508880469975501462731 936763320704963252194097)
    ·
      refine ⟨702572490528722439145573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 936763320704963252194097 702572490528722439145573)
      ·
        refine ⟨131732341974135457339795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 702572490528722439145573 131732341974135457339795)
        ·
          refine ⟨197598512961203186009693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131732341974135457339795 197598512961203186009693)
          ·
            refine ⟨74099442360451194753635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 197598512961203186009693 74099442360451194753635)
            ·
              refine ⟨111149163540676792130453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74099442360451194753635 111149163540676792130453)
              ·
                refine ⟨5210117040969224631115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111149163540676792130453 5210117040969224631115)
                ·
                  rfl

theorem cell21_68490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_68490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68490 prefixEnd_68490 := by exact prefixLift 68490
  have htrace : WordTrace (prefixWord ++ tailWord_68490) baseStart_68490 baseEnd_68490 := by
    simpa [prefixWord, tailWord_68490, baseEnd_68490] using wordTrace_append hprefix tailTrace_68490
  have hstable : (prefixWord ++ tailWord_68490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68490).length < 2 ^ (prefixWord ++ tailWord_68490).sum := by decide
  have hdescent : baseEnd_68490 < baseStart_68490 := by decide
  rcases family_descends (prefixWord ++ tailWord_68490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68552 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_68552 : Nat := 118140960795 + 68552 * 2 ^ 59
def prefixEnd_68552 : Nat := 4983230072969 + 3 ^ 40 * 68552 * 2
def baseEnd_68552 : Nat := 15644500367609343859885

theorem tailTrace_68552 : CollatzResearch.WordTrace tailWord_68552 prefixEnd_68552 15644500367609343859885 := by
  unfold tailWord_68552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250148423827643297303955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1666864565103524396405273 1250148423827643297303955)
  ·
    refine ⟨1875222635741464945955933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250148423827643297303955 1875222635741464945955933)
    ·
      refine ⟨703208488403049354733475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1875222635741464945955933 703208488403049354733475)
      ·
        refine ⟨1054812732604574032100213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703208488403049354733475 1054812732604574032100213)
        ·
          refine ⟨98888693681678815509395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1054812732604574032100213 98888693681678815509395)
          ·
            refine ⟨148333040522518223264093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98888693681678815509395 148333040522518223264093)
            ·
              refine ⟨55624890195944333724035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148333040522518223264093 55624890195944333724035)
              ·
                refine ⟨83437335293916500586053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55624890195944333724035 83437335293916500586053)
                ·
                  refine ⟨15644500367609343859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83437335293916500586053 15644500367609343859885)
                  ·
                    rfl

theorem cell21_68552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_68552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68552 prefixEnd_68552 := by exact prefixLift 68552
  have htrace : WordTrace (prefixWord ++ tailWord_68552) baseStart_68552 baseEnd_68552 := by
    simpa [prefixWord, tailWord_68552, baseEnd_68552] using wordTrace_append hprefix tailTrace_68552
  have hstable : (prefixWord ++ tailWord_68552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68552).length < 2 ^ (prefixWord ++ tailWord_68552).sum := by decide
  have hdescent : baseEnd_68552 < baseStart_68552 := by decide
  rcases family_descends (prefixWord ++ tailWord_68552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68566 : List Nat := [5, 2, 1, 1, 2, 2, 1, 7]
def baseStart_68566 : Nat := 118140960795 + 68566 * 2 ^ 59
def prefixEnd_68566 : Nat := 4983230072969 + 3 ^ 40 * 68566 * 2
def baseEnd_68566 : Nat := 5215898452782810208841

theorem tailTrace_68566 : CollatzResearch.WordTrace tailWord_68566 prefixEnd_68566 5215898452782810208841 := by
  unfold tailWord_68566
  simp only [CollatzResearch.WordTrace]
  refine ⟨156300466850285436601097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1667204979736377990411701 156300466850285436601097)
  ·
    refine ⟨117225350137714077450823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156300466850285436601097 117225350137714077450823)
    ·
      refine ⟨175838025206571116176235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117225350137714077450823 175838025206571116176235)
      ·
        refine ⟨263757037809856674264353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175838025206571116176235 263757037809856674264353)
        ·
          refine ⟨197817778357392505698265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263757037809856674264353 197817778357392505698265)
          ·
            refine ⟨148363333768044379273699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197817778357392505698265 148363333768044379273699)
            ·
              refine ⟨222545000652066568910549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148363333768044379273699 222545000652066568910549)
              ·
                refine ⟨5215898452782810208841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 222545000652066568910549 5215898452782810208841)
                ·
                  rfl

theorem cell21_68566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_68566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68566 prefixEnd_68566 := by exact prefixLift 68566
  have htrace : WordTrace (prefixWord ++ tailWord_68566) baseStart_68566 baseEnd_68566 := by
    simpa [prefixWord, tailWord_68566, baseEnd_68566] using wordTrace_append hprefix tailTrace_68566
  have hstable : (prefixWord ++ tailWord_68566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68566).length < 2 ^ (prefixWord ++ tailWord_68566).sum := by decide
  have hdescent : baseEnd_68566 < baseStart_68566 := by decide
  rcases family_descends (prefixWord ++ tailWord_68566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68580 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_68580 : Nat := 118140960795 + 68580 * 2 ^ 59
def prefixEnd_68580 : Nat := 4983230072969 + 3 ^ 40 * 68580 * 2
def baseEnd_68580 : Nat := 15650890349087517393161

theorem tailTrace_68580 : CollatzResearch.WordTrace tailWord_68580 prefixEnd_68580 15650890349087517393161 := by
  unfold tailWord_68580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250659045776923688313597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1667545394369231584418129 1250659045776923688313597)
  ·
    refine ⟨468997142166346383117599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1250659045776923688313597 468997142166346383117599)
    ·
      refine ⟨703495713249519574676399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468997142166346383117599 703495713249519574676399)
      ·
        refine ⟨1055243569874279362014599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703495713249519574676399 1055243569874279362014599)
        ·
          refine ⟨1582865354811419043021899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055243569874279362014599 1582865354811419043021899)
          ·
            refine ⟨2374298032217128564532849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582865354811419043021899 2374298032217128564532849)
            ·
              refine ⟨1780723524162846423399637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374298032217128564532849 1780723524162846423399637)
              ·
                refine ⟨41735707597566713048429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1780723524162846423399637 41735707597566713048429)
                ·
                  refine ⟨15650890349087517393161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41735707597566713048429 15650890349087517393161)
                  ·
                    rfl

theorem cell21_68580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_68580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68580 prefixEnd_68580 := by exact prefixLift 68580
  have htrace : WordTrace (prefixWord ++ tailWord_68580) baseStart_68580 baseEnd_68580 := by
    simpa [prefixWord, tailWord_68580, baseEnd_68580] using wordTrace_append hprefix tailTrace_68580
  have hstable : (prefixWord ++ tailWord_68580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68580).length < 2 ^ (prefixWord ++ tailWord_68580).sum := by decide
  have hdescent : baseEnd_68580 < baseStart_68580 := by decide
  rcases family_descends (prefixWord ++ tailWord_68580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68656 : List Nat := [2, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_68656 : Nat := 118140960795 + 68656 * 2 ^ 59
def prefixEnd_68656 : Nat := 4983230072969 + 3 ^ 40 * 68656 * 2
def baseEnd_68656 : Nat := 15668234584528274126339

theorem tailTrace_68656 : CollatzResearch.WordTrace tailWord_68656 prefixEnd_68656 15668234584528274126339 := by
  unfold tailWord_68656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252045019639256178196911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1669393359519008237595881 1252045019639256178196911)
  ·
    refine ⟨1878067529458884267295367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1252045019639256178196911 1878067529458884267295367)
    ·
      refine ⟨2817101294188326400943051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878067529458884267295367 2817101294188326400943051)
      ·
        refine ⟨4225651941282489601414577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817101294188326400943051 4225651941282489601414577)
        ·
          refine ⟨3169238955961867201060933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4225651941282489601414577 3169238955961867201060933)
          ·
            refine ⟨594232304242850100198925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3169238955961867201060933 594232304242850100198925)
            ·
              refine ⟨222837114091068787574597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594232304242850100198925 222837114091068787574597)
              ·
                refine ⟨41781958892075397670237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 222837114091068787574597 41781958892075397670237)
                ·
                  refine ⟨15668234584528274126339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41781958892075397670237 15668234584528274126339)
                  ·
                    rfl

theorem cell21_68656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_68656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68656 prefixEnd_68656 := by exact prefixLift 68656
  have htrace : WordTrace (prefixWord ++ tailWord_68656) baseStart_68656 baseEnd_68656 := by
    simpa [prefixWord, tailWord_68656, baseEnd_68656] using wordTrace_append hprefix tailTrace_68656
  have hstable : (prefixWord ++ tailWord_68656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68656).length < 2 ^ (prefixWord ++ tailWord_68656).sum := by decide
  have hdescent : baseEnd_68656 < baseStart_68656 := by decide
  rcases family_descends (prefixWord ++ tailWord_68656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68760 : List Nat := [2, 1, 2, 4, 2, 1, 9]
def baseStart_68760 : Nat := 118140960795 + 68760 * 2 ^ 59
def prefixEnd_68760 : Nat := 4983230072969 + 3 ^ 40 * 68760 * 2
def baseEnd_68760 : Nat := 1743552089049689376977

theorem tailTrace_68760 : CollatzResearch.WordTrace tailWord_68760 prefixEnd_68760 1743552089049689376977 := by
  unfold tailWord_68760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253941615450869059089867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1671922153934492078786489 1253941615450869059089867)
  ·
    refine ⟨1880912423176303588634801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253941615450869059089867 1880912423176303588634801)
    ·
      refine ⟨1410684317382227691476101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1880912423176303588634801 1410684317382227691476101)
      ·
        refine ⟨264503309509167692151769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1410684317382227691476101 264503309509167692151769)
        ·
          refine ⟨198377482131875769113827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264503309509167692151769 198377482131875769113827)
          ·
            refine ⟨297566223197813653670741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198377482131875769113827 297566223197813653670741)
            ·
              refine ⟨1743552089049689376977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 297566223197813653670741 1743552089049689376977)
              ·
                rfl

theorem cell21_68760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 9].length) (baseStart_68760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68760 prefixEnd_68760 := by exact prefixLift 68760
  have htrace : WordTrace (prefixWord ++ tailWord_68760) baseStart_68760 baseEnd_68760 := by
    simpa [prefixWord, tailWord_68760, baseEnd_68760] using wordTrace_append hprefix tailTrace_68760
  have hstable : (prefixWord ++ tailWord_68760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68760).length < 2 ^ (prefixWord ++ tailWord_68760).sum := by decide
  have hdescent : baseEnd_68760 < baseStart_68760 := by decide
  rcases family_descends (prefixWord ++ tailWord_68760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68836 : List Nat := [2, 3, 1, 1, 1, 2, 5, 6]
def baseStart_68836 : Nat := 118140960795 + 68836 * 2 ^ 59
def prefixEnd_68836 : Nat := 4983230072969 + 3 ^ 40 * 68836 * 2
def baseEnd_68836 : Nat := 5236437678962653708657

theorem tailTrace_68836 : CollatzResearch.WordTrace tailWord_68836 prefixEnd_68836 5236437678962653708657 := by
  unfold tailWord_68836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255327589313201548973181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1673770119084268731964241 1255327589313201548973181)
  ·
    refine ⟨470747845992450580864943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1255327589313201548973181 470747845992450580864943)
    ·
      refine ⟨706121768988675871297415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470747845992450580864943 706121768988675871297415)
      ·
        refine ⟨1059182653483013806946123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706121768988675871297415 1059182653483013806946123)
        ·
          refine ⟨1588773980224520710419185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059182653483013806946123 1588773980224520710419185)
          ·
            refine ⟨1191580485168390532814389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1588773980224520710419185 1191580485168390532814389)
            ·
              refine ⟨111710670484536612451349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1191580485168390532814389 111710670484536612451349)
              ·
                refine ⟨5236437678962653708657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111710670484536612451349 5236437678962653708657)
                ·
                  rfl

theorem cell21_68836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_68836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68836 prefixEnd_68836 := by exact prefixLift 68836
  have htrace : WordTrace (prefixWord ++ tailWord_68836) baseStart_68836 baseEnd_68836 := by
    simpa [prefixWord, tailWord_68836, baseEnd_68836] using wordTrace_append hprefix tailTrace_68836
  have hstable : (prefixWord ++ tailWord_68836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68836).length < 2 ^ (prefixWord ++ tailWord_68836).sum := by decide
  have hdescent : baseEnd_68836 < baseStart_68836 := by decide
  rcases family_descends (prefixWord ++ tailWord_68836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68881 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_68881 : Nat := 118140960795 + 68881 * 2 ^ 59
def prefixEnd_68881 : Nat := 4983230072969 + 3 ^ 40 * 68881 * 2
def baseEnd_68881 : Nat := 15719582649977882875879

theorem tailTrace_68881 : CollatzResearch.WordTrace tailWord_68881 prefixEnd_68881 15719582649977882875879 := by
  unfold tailWord_68881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512296463463375783334497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1674864308975583855556331 2512296463463375783334497)
  ·
    refine ⟨1884222347597531837500873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2512296463463375783334497 1884222347597531837500873)
    ·
      refine ⟨1413166760698148878125655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884222347597531837500873 1413166760698148878125655)
      ·
        refine ⟨2119750141047223317188483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413166760698148878125655 2119750141047223317188483)
        ·
          refine ⟨3179625211570834975782725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119750141047223317188483 3179625211570834975782725)
          ·
            refine ⟨596179727169531557959261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3179625211570834975782725 596179727169531557959261)
            ·
              refine ⟨223567397688574334234723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 596179727169531557959261 223567397688574334234723)
              ·
                refine ⟨335351096532861501352085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223567397688574334234723 335351096532861501352085)
                ·
                  refine ⟨15719582649977882875879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 335351096532861501352085 15719582649977882875879)
                  ·
                    rfl

theorem cell21_68881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_68881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68881 prefixEnd_68881 := by exact prefixLift 68881
  have htrace : WordTrace (prefixWord ++ tailWord_68881) baseStart_68881 baseEnd_68881 := by
    simpa [prefixWord, tailWord_68881, baseEnd_68881] using wordTrace_append hprefix tailTrace_68881
  have hstable : (prefixWord ++ tailWord_68881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68881).length < 2 ^ (prefixWord ++ tailWord_68881).sum := by decide
  have hdescent : baseEnd_68881 < baseStart_68881 := by decide
  rcases family_descends (prefixWord ++ tailWord_68881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68929 : List Nat := [1, 2, 5, 2, 1, 3, 7]
def baseStart_68929 : Nat := 118140960795 + 68929 * 2 ^ 59
def prefixEnd_68929 : Nat := 4983230072969 + 3 ^ 40 * 68929 * 2
def baseEnd_68929 : Nat := 1747837433771162897309

theorem tailTrace_68929 : CollatzResearch.WordTrace tailWord_68929 prefixEnd_68929 1747837433771162897309 := by
  unfold tailWord_68929
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514047167289479981081841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1676031444859653320721227 2514047167289479981081841)
  ·
    refine ⟨1885535375467109985811381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2514047167289479981081841 1885535375467109985811381)
    ·
      refine ⟨176768941450041561169817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1885535375467109985811381 176768941450041561169817)
      ·
        refine ⟨132576706087531170877363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176768941450041561169817 132576706087531170877363)
        ·
          refine ⟨198865059131296756316045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132576706087531170877363 198865059131296756316045)
          ·
            refine ⟨74574397174236283618517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198865059131296756316045 74574397174236283618517)
            ·
              refine ⟨1747837433771162897309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74574397174236283618517 1747837433771162897309)
              ·
                rfl

theorem cell21_68929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 7].length) (baseStart_68929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68929 prefixEnd_68929 := by exact prefixLift 68929
  have htrace : WordTrace (prefixWord ++ tailWord_68929) baseStart_68929 baseEnd_68929 := by
    simpa [prefixWord, tailWord_68929, baseEnd_68929] using wordTrace_append hprefix tailTrace_68929
  have hstable : (prefixWord ++ tailWord_68929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68929).length < 2 ^ (prefixWord ++ tailWord_68929).sum := by decide
  have hdescent : baseEnd_68929 < baseStart_68929 := by decide
  rcases family_descends (prefixWord ++ tailWord_68929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68994 : List Nat := [3, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_68994 : Nat := 118140960795 + 68994 * 2 ^ 59
def prefixEnd_68994 : Nat := 4983230072969 + 3 ^ 40 * 68994 * 2
def baseEnd_68994 : Nat := 15745370789514797492315

theorem tailTrace_68994 : CollatzResearch.WordTrace tailWord_68994 prefixEnd_68994 15745370789514797492315 := by
  unfold tailWord_68994
  simp only [CollatzResearch.WordTrace]
  refine ⟨629104478013499020549509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1677611941369330721465357 629104478013499020549509)
  ·
    refine ⟨117957089627531066353033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 629104478013499020549509 117957089627531066353033)
    ·
      refine ⟨88467817220648299764775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117957089627531066353033 88467817220648299764775)
      ·
        refine ⟨132701725830972449647163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88467817220648299764775 132701725830972449647163)
        ·
          refine ⟨199052588746458674470745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132701725830972449647163 199052588746458674470745)
          ·
            refine ⟨149289441559844005853059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199052588746458674470745 149289441559844005853059)
            ·
              refine ⟨223934162339766008779589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149289441559844005853059 223934162339766008779589)
              ·
                refine ⟨41987655438706126646173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223934162339766008779589 41987655438706126646173)
                ·
                  refine ⟨15745370789514797492315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41987655438706126646173 15745370789514797492315)
                  ·
                    rfl

theorem cell21_68994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_68994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_68994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_68994 prefixEnd_68994 := by exact prefixLift 68994
  have htrace : WordTrace (prefixWord ++ tailWord_68994) baseStart_68994 baseEnd_68994 := by
    simpa [prefixWord, tailWord_68994, baseEnd_68994] using wordTrace_append hprefix tailTrace_68994
  have hstable : (prefixWord ++ tailWord_68994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68994).length < 2 ^ (prefixWord ++ tailWord_68994).sum := by decide
  have hdescent : baseEnd_68994 < baseStart_68994 := by decide
  rcases family_descends (prefixWord ++ tailWord_68994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69047 : List Nat := [1, 1, 3, 1, 3, 2, 10]
def baseStart_69047 : Nat := 118140960795 + 69047 * 2 ^ 59
def prefixEnd_69047 : Nat := 4983230072969 + 3 ^ 40 * 69047 * 2
def baseEnd_69047 : Nat := 1750829567955387012097

theorem tailTrace_69047 : CollatzResearch.WordTrace tailWord_69047 prefixEnd_69047 1750829567955387012097 := by
  unfold tailWord_69047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518350980861986133877395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1678900653907990755918263 2518350980861986133877395)
  ·
    refine ⟨3777526471292979200816093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518350980861986133877395 3777526471292979200816093)
    ·
      refine ⟨1416572426734867200306035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3777526471292979200816093 1416572426734867200306035)
      ·
        refine ⟨2124858640102300800459053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416572426734867200306035 2124858640102300800459053)
        ·
          refine ⟨796821990038362800172145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2124858640102300800459053 796821990038362800172145)
          ·
            refine ⟨597616492528772100129109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796821990038362800172145 597616492528772100129109)
            ·
              refine ⟨1750829567955387012097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 597616492528772100129109 1750829567955387012097)
              ·
                rfl

theorem cell21_69047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 10].length) (baseStart_69047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69047 prefixEnd_69047 := by exact prefixLift 69047
  have htrace : WordTrace (prefixWord ++ tailWord_69047) baseStart_69047 baseEnd_69047 := by
    simpa [prefixWord, tailWord_69047, baseEnd_69047] using wordTrace_append hprefix tailTrace_69047
  have hstable : (prefixWord ++ tailWord_69047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69047).length < 2 ^ (prefixWord ++ tailWord_69047).sum := by decide
  have hdescent : baseEnd_69047 < baseStart_69047 := by decide
  rcases family_descends (prefixWord ++ tailWord_69047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69081 : List Nat := [1, 2, 1, 2, 4, 4, 2, 5]
def baseStart_69081 : Nat := 118140960795 + 69081 * 2 ^ 59
def prefixEnd_69081 : Nat := 4983230072969 + 3 ^ 40 * 69081 * 2
def baseEnd_69081 : Nat := 5255075124940659847379

theorem tailTrace_69081 : CollatzResearch.WordTrace tailWord_69081 prefixEnd_69081 5255075124940659847379 := by
  unfold tailWord_69081
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519591062738809940615097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1679727375159206627076731 2519591062738809940615097)
  ·
    refine ⟨1889693297054107455461323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2519591062738809940615097 1889693297054107455461323)
    ·
      refine ⟨2834539945581161183191985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889693297054107455461323 2834539945581161183191985)
      ·
        refine ⟨2125904959185870887393989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2834539945581161183191985 2125904959185870887393989)
        ·
          refine ⟨398607179847350791386373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2125904959185870887393989 398607179847350791386373)
          ·
            refine ⟨74738846221378273384945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398607179847350791386373 74738846221378273384945)
            ·
              refine ⟨56054134666033705038709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74738846221378273384945 56054134666033705038709)
              ·
                refine ⟨5255075124940659847379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56054134666033705038709 5255075124940659847379)
                ·
                  rfl

theorem cell21_69081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 5].length) (baseStart_69081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69081 prefixEnd_69081 := by exact prefixLift 69081
  have htrace : WordTrace (prefixWord ++ tailWord_69081) baseStart_69081 baseEnd_69081 := by
    simpa [prefixWord, tailWord_69081, baseEnd_69081] using wordTrace_append hprefix tailTrace_69081
  have hstable : (prefixWord ++ tailWord_69081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69081).length < 2 ^ (prefixWord ++ tailWord_69081).sum := by decide
  have hdescent : baseEnd_69081 < baseStart_69081 := by decide
  rcases family_descends (prefixWord ++ tailWord_69081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69118 : List Nat := [4, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_69118 : Nat := 118140960795 + 69118 * 2 ^ 59
def prefixEnd_69118 : Nat := 4983230072969 + 3 ^ 40 * 69118 * 2
def baseEnd_69118 : Nat := 15773669278918137425395

theorem tailTrace_69118 : CollatzResearch.WordTrace tailWord_69118 prefixEnd_69118 15773669278918137425395 := by
  unfold tailWord_69118
  simp only [CollatzResearch.WordTrace]
  refine ⟨315117570450595657464001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1680627042403176839808005 315117570450595657464001)
  ·
    refine ⟨236338177837946743098001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 315117570450595657464001 236338177837946743098001)
    ·
      refine ⟨177253633378460057323501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236338177837946743098001 177253633378460057323501)
      ·
        refine ⟨66470112516922521496313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177253633378460057323501 66470112516922521496313)
        ·
          refine ⟨49852584387691891122235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66470112516922521496313 49852584387691891122235)
          ·
            refine ⟨74778876581537836683353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49852584387691891122235 74778876581537836683353)
            ·
              refine ⟨56084157436153377512515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74778876581537836683353 56084157436153377512515)
              ·
                refine ⟨84126236154230066268773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56084157436153377512515 84126236154230066268773)
                ·
                  refine ⟨15773669278918137425395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84126236154230066268773 15773669278918137425395)
                  ·
                    rfl

theorem cell21_69118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_69118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69118 prefixEnd_69118 := by exact prefixLift 69118
  have htrace : WordTrace (prefixWord ++ tailWord_69118) baseStart_69118 baseEnd_69118 := by
    simpa [prefixWord, tailWord_69118, baseEnd_69118] using wordTrace_append hprefix tailTrace_69118
  have hstable : (prefixWord ++ tailWord_69118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69118).length < 2 ^ (prefixWord ++ tailWord_69118).sum := by decide
  have hdescent : baseEnd_69118 < baseStart_69118 := by decide
  rcases family_descends (prefixWord ++ tailWord_69118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69174 : List Nat := [5, 1, 2, 1, 3, 2, 1, 6]
def baseStart_69174 : Nat := 118140960795 + 69174 * 2 ^ 59
def prefixEnd_69174 : Nat := 4983230072969 + 3 ^ 40 * 69174 * 2
def baseEnd_69174 : Nat := 5262149747291494830649

theorem tailTrace_69174 : CollatzResearch.WordTrace tailWord_69174 prefixEnd_69174 5262149747291494830649 := by
  unfold tailWord_69174
  simp only [CollatzResearch.WordTrace]
  refine ⟨157686440712617926484411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1681988700934591215833717 157686440712617926484411)
  ·
    refine ⟨236529661068926889726617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157686440712617926484411 236529661068926889726617)
    ·
      refine ⟨177397245801695167294963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236529661068926889726617 177397245801695167294963)
      ·
        refine ⟨266095868702542750942445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177397245801695167294963 266095868702542750942445)
        ·
          refine ⟨99785950763453531603417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266095868702542750942445 99785950763453531603417)
          ·
            refine ⟨74839463072590148702563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99785950763453531603417 74839463072590148702563)
            ·
              refine ⟨112259194608885223053845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74839463072590148702563 112259194608885223053845)
              ·
                refine ⟨5262149747291494830649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112259194608885223053845 5262149747291494830649)
                ·
                  rfl

theorem cell21_69174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_69174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69174 prefixEnd_69174 := by exact prefixLift 69174
  have htrace : WordTrace (prefixWord ++ tailWord_69174) baseStart_69174 baseEnd_69174 := by
    simpa [prefixWord, tailWord_69174, baseEnd_69174] using wordTrace_append hprefix tailTrace_69174
  have hstable : (prefixWord ++ tailWord_69174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69174).length < 2 ^ (prefixWord ++ tailWord_69174).sum := by decide
  have hdescent : baseEnd_69174 < baseStart_69174 := by decide
  rcases family_descends (prefixWord ++ tailWord_69174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69278 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_69278 : Nat := 118140960795 + 69278 * 2 ^ 59
def prefixEnd_69278 : Nat := 4983230072969 + 3 ^ 40 * 69278 * 2
def baseEnd_69278 : Nat := 15810183458793414758401

theorem tailTrace_69278 : CollatzResearch.WordTrace tailWord_69278 prefixEnd_69278 15810183458793414758401 := by
  unfold tailWord_69278
  simp only [CollatzResearch.WordTrace]
  refine ⟨315847030378139073192061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1684517495350075057024325 315847030378139073192061)
  ·
    refine ⟨118442636391802152447023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 315847030378139073192061 118442636391802152447023)
    ·
      refine ⟨177663954587703228670535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118442636391802152447023 177663954587703228670535)
      ·
        refine ⟨266495931881554843005803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177663954587703228670535 266495931881554843005803)
        ·
          refine ⟨399743897822332264508705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266495931881554843005803 399743897822332264508705)
          ·
            refine ⟨299807923366749198381529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399743897822332264508705 299807923366749198381529)
            ·
              refine ⟨224855942525061898786147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299807923366749198381529 224855942525061898786147)
              ·
                refine ⟨337283913787592848179221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224855942525061898786147 337283913787592848179221)
                ·
                  refine ⟨15810183458793414758401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 337283913787592848179221 15810183458793414758401)
                  ·
                    rfl

theorem cell21_69278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_69278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69278 prefixEnd_69278 := by exact prefixLift 69278
  have htrace : WordTrace (prefixWord ++ tailWord_69278) baseStart_69278 baseEnd_69278 := by
    simpa [prefixWord, tailWord_69278, baseEnd_69278] using wordTrace_append hprefix tailTrace_69278
  have hstable : (prefixWord ++ tailWord_69278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69278).length < 2 ^ (prefixWord ++ tailWord_69278).sum := by decide
  have hdescent : baseEnd_69278 < baseStart_69278 := by decide
  rcases family_descends (prefixWord ++ tailWord_69278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69281 : List Nat := [1, 2, 3, 3, 2, 2, 3, 2, 3]
def baseStart_69281 : Nat := 118140960795 + 69281 * 2 ^ 59
def prefixEnd_69281 : Nat := 4983230072969 + 3 ^ 40 * 69281 * 2
def baseEnd_69281 : Nat := 15810868099666076208395

theorem tailTrace_69281 : CollatzResearch.WordTrace tailWord_69281 prefixEnd_69281 15810868099666076208395 := by
  unfold tailWord_69281
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526885662014244097895697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1684590441342829398597131 2526885662014244097895697)
  ·
    refine ⟨1895164246510683073421773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2526885662014244097895697 1895164246510683073421773)
    ·
      refine ⟨710686592441506152533165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1895164246510683073421773 710686592441506152533165)
      ·
        refine ⟨266507472165564807199937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 710686592441506152533165 266507472165564807199937)
        ·
          refine ⟨199880604124173605399953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266507472165564807199937 199880604124173605399953)
          ·
            refine ⟨149910453093130204049965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199880604124173605399953 149910453093130204049965)
            ·
              refine ⟨56216419909923826518737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149910453093130204049965 56216419909923826518737)
              ·
                refine ⟨42162314932442869889053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56216419909923826518737 42162314932442869889053)
                ·
                  refine ⟨15810868099666076208395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42162314932442869889053 15810868099666076208395)
                  ·
                    rfl

theorem cell21_69281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_69281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69281 prefixEnd_69281 := by exact prefixLift 69281
  have htrace : WordTrace (prefixWord ++ tailWord_69281) baseStart_69281 baseEnd_69281 := by
    simpa [prefixWord, tailWord_69281, baseEnd_69281] using wordTrace_append hprefix tailTrace_69281
  have hstable : (prefixWord ++ tailWord_69281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69281).length < 2 ^ (prefixWord ++ tailWord_69281).sum := by decide
  have hdescent : baseEnd_69281 < baseStart_69281 := by decide
  rcases family_descends (prefixWord ++ tailWord_69281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69337 : List Nat := [1, 2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_69337 : Nat := 118140960795 + 69337 * 2 ^ 59
def prefixEnd_69337 : Nat := 4983230072969 + 3 ^ 40 * 69337 * 2
def baseEnd_69337 : Nat := 15823648062622423274947

theorem tailTrace_69337 : CollatzResearch.WordTrace tailWord_69337 prefixEnd_69337 15823648062622423274947 := by
  unfold tailWord_69337
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528928149811365661934265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1685952099874243774622843 2528928149811365661934265)
  ·
    refine ⟨1896696112358524246450699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2528928149811365661934265 1896696112358524246450699)
    ·
      refine ⟨2845044168537786369676049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896696112358524246450699 2845044168537786369676049)
      ·
        refine ⟨2133783126403339777257037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2845044168537786369676049 2133783126403339777257037)
        ·
          refine ⟨800168672401252416471389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2133783126403339777257037 800168672401252416471389)
          ·
            refine ⟨300063252150469656176771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800168672401252416471389 300063252150469656176771)
            ·
              refine ⟨450094878225704484265157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300063252150469656176771 450094878225704484265157)
              ·
                refine ⟨84392789667319590799717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450094878225704484265157 84392789667319590799717)
                ·
                  refine ⟨15823648062622423274947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84392789667319590799717 15823648062622423274947)
                  ·
                    rfl

theorem cell21_69337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_69337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69337 prefixEnd_69337 := by exact prefixLift 69337
  have htrace : WordTrace (prefixWord ++ tailWord_69337) baseStart_69337 baseEnd_69337 := by
    simpa [prefixWord, tailWord_69337, baseEnd_69337] using wordTrace_append hprefix tailTrace_69337
  have hstable : (prefixWord ++ tailWord_69337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69337).length < 2 ^ (prefixWord ++ tailWord_69337).sum := by decide
  have hdescent : baseEnd_69337 < baseStart_69337 := by decide
  rcases family_descends (prefixWord ++ tailWord_69337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69399 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_69399 : Nat := 118140960795 + 69399 * 2 ^ 59
def prefixEnd_69399 : Nat := 4983230072969 + 3 ^ 40 * 69399 * 2
def baseEnd_69399 : Nat := 15837797307324093241487

theorem tailTrace_69399 : CollatzResearch.WordTrace tailWord_69399 prefixEnd_69399 15837797307324093241487 := by
  unfold tailWord_69399
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531189475586750250691251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1687459650391166833794167 2531189475586750250691251)
  ·
    refine ⟨3796784213380125376036877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531189475586750250691251 3796784213380125376036877)
    ·
      refine ⟨1423794080017547016013829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3796784213380125376036877 1423794080017547016013829)
      ·
        refine ⟨266961390003290065502593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1423794080017547016013829 266961390003290065502593)
        ·
          refine ⟨200221042502467549126945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266961390003290065502593 200221042502467549126945)
          ·
            refine ⟨150165781876850661845209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200221042502467549126945 150165781876850661845209)
            ·
              refine ⟨112624336407637996383907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150165781876850661845209 112624336407637996383907)
              ·
                refine ⟨168936504611456994575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112624336407637996383907 168936504611456994575861)
                ·
                  refine ⟨15837797307324093241487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168936504611456994575861 15837797307324093241487)
                  ·
                    rfl

theorem cell21_69399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_69399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69399 prefixEnd_69399 := by exact prefixLift 69399
  have htrace : WordTrace (prefixWord ++ tailWord_69399) baseStart_69399 baseEnd_69399 := by
    simpa [prefixWord, tailWord_69399, baseEnd_69399] using wordTrace_append hprefix tailTrace_69399
  have hstable : (prefixWord ++ tailWord_69399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69399).length < 2 ^ (prefixWord ++ tailWord_69399).sum := by decide
  have hdescent : baseEnd_69399 < baseStart_69399 := by decide
  rcases family_descends (prefixWord ++ tailWord_69399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69430 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_69430 : Nat := 118140960795 + 69430 * 2 ^ 59
def prefixEnd_69430 : Nat := 4983230072969 + 3 ^ 40 * 69430 * 2
def baseEnd_69430 : Nat := 15844871929674928224757

theorem tailTrace_69430 : CollatzResearch.WordTrace tailWord_69430 prefixEnd_69430 15844871929674928224757 := by
  unfold tailWord_69430
  simp only [CollatzResearch.WordTrace]
  refine ⟨158270008654652659066859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1688213425649628363379829 158270008654652659066859)
  ·
    refine ⟨237405012981978988600289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158270008654652659066859 237405012981978988600289)
    ·
      refine ⟨178053759736484241450217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237405012981978988600289 178053759736484241450217)
      ·
        refine ⟨133540319802363181087663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178053759736484241450217 133540319802363181087663)
        ·
          refine ⟨200310479703544771631495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133540319802363181087663 200310479703544771631495)
          ·
            refine ⟨300465719555317157447243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200310479703544771631495 300465719555317157447243)
            ·
              refine ⟨450698579332975736170865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300465719555317157447243 450698579332975736170865)
              ·
                refine ⟨338023934499731802128149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450698579332975736170865 338023934499731802128149)
                ·
                  refine ⟨15844871929674928224757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 338023934499731802128149 15844871929674928224757)
                  ·
                    rfl

theorem cell21_69430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_69430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69430 prefixEnd_69430 := by exact prefixLift 69430
  have htrace : WordTrace (prefixWord ++ tailWord_69430) baseStart_69430 baseEnd_69430 := by
    simpa [prefixWord, tailWord_69430, baseEnd_69430] using wordTrace_append hprefix tailTrace_69430
  have hstable : (prefixWord ++ tailWord_69430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69430).length < 2 ^ (prefixWord ++ tailWord_69430).sum := by decide
  have hdescent : baseEnd_69430 < baseStart_69430 := by decide
  rcases family_descends (prefixWord ++ tailWord_69430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69537 : List Nat := [1, 2, 3, 4, 2, 1, 3, 5]
def baseStart_69537 : Nat := 118140960795 + 69537 * 2 ^ 59
def prefixEnd_69537 : Nat := 4983230072969 + 3 ^ 40 * 69537 * 2
def baseEnd_69537 : Nat := 5289763595822173313735

theorem tailTrace_69537 : CollatzResearch.WordTrace tailWord_69537 prefixEnd_69537 5289763595822173313735 := by
  unfold tailWord_69537
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536222749086799819214865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1690815166057866546143243 2536222749086799819214865)
  ·
    refine ⟨1902167061815099864411149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2536222749086799819214865 1902167061815099864411149)
    ·
      refine ⟨713312648180662449154181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1902167061815099864411149 713312648180662449154181)
      ·
        refine ⟨133746121533874209216409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 713312648180662449154181 133746121533874209216409)
        ·
          refine ⟨100309591150405656912307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133746121533874209216409 100309591150405656912307)
          ·
            refine ⟨150464386725608485368461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100309591150405656912307 150464386725608485368461)
            ·
              refine ⟨56424145022103182013173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150464386725608485368461 56424145022103182013173)
              ·
                refine ⟨5289763595822173313735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56424145022103182013173 5289763595822173313735)
                ·
                  rfl

theorem cell21_69537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 5].length) (baseStart_69537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69537 prefixEnd_69537 := by exact prefixLift 69537
  have htrace : WordTrace (prefixWord ++ tailWord_69537) baseStart_69537 baseEnd_69537 := by
    simpa [prefixWord, tailWord_69537, baseEnd_69537] using wordTrace_append hprefix tailTrace_69537
  have hstable : (prefixWord ++ tailWord_69537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69537).length < 2 ^ (prefixWord ++ tailWord_69537).sum := by decide
  have hdescent : baseEnd_69537 < baseStart_69537 := by decide
  rcases family_descends (prefixWord ++ tailWord_69537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69551 : List Nat := [1, 1, 2, 1, 2, 2, 6, 3, 3]
def baseStart_69551 : Nat := 118140960795 + 69551 * 2 ^ 59
def prefixEnd_69551 : Nat := 4983230072969 + 3 ^ 40 * 69551 * 2
def baseEnd_69551 : Nat := 15872485778205606707843

theorem tailTrace_69551 : CollatzResearch.WordTrace tailWord_69551 prefixEnd_69551 15872485778205606707843 := by
  unfold tailWord_69551
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536733371036080210224507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1691155580690720140149671 2536733371036080210224507)
  ·
    refine ⟨3805100056554120315336761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536733371036080210224507 3805100056554120315336761)
    ·
      refine ⟨2853825042415590236502571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805100056554120315336761 2853825042415590236502571)
      ·
        refine ⟨4280737563623385354753857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853825042415590236502571 4280737563623385354753857)
        ·
          refine ⟨3210553172717539016065393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280737563623385354753857 3210553172717539016065393)
          ·
            refine ⟨2407914879538154262049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210553172717539016065393 2407914879538154262049045)
            ·
              refine ⟨112871009978350981033549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2407914879538154262049045 112871009978350981033549)
              ·
                refine ⟨42326628741881617887581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112871009978350981033549 42326628741881617887581)
                ·
                  refine ⟨15872485778205606707843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42326628741881617887581 15872485778205606707843)
                  ·
                    rfl

theorem cell21_69551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3, 3].length) (baseStart_69551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69551 prefixEnd_69551 := by exact prefixLift 69551
  have htrace : WordTrace (prefixWord ++ tailWord_69551) baseStart_69551 baseEnd_69551 := by
    simpa [prefixWord, tailWord_69551, baseEnd_69551] using wordTrace_append hprefix tailTrace_69551
  have hstable : (prefixWord ++ tailWord_69551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69551).length < 2 ^ (prefixWord ++ tailWord_69551).sum := by decide
  have hdescent : baseEnd_69551 < baseStart_69551 := by decide
  rcases family_descends (prefixWord ++ tailWord_69551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69565 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_69565 : Nat := 118140960795 + 69565 * 2 ^ 59
def prefixEnd_69565 : Nat := 4983230072969 + 3 ^ 40 * 69565 * 2
def baseEnd_69565 : Nat := 15875680768944693474481

theorem tailTrace_69565 : CollatzResearch.WordTrace tailWord_69565 prefixEnd_69565 15875680768944693474481 := by
  unfold tailWord_69565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537243992985360601234149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1691495995323573734156099 2537243992985360601234149)
  ·
    refine ⟨475733248684755112731403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2537243992985360601234149 475733248684755112731403)
    ·
      refine ⟨713599873027132669097105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475733248684755112731403 713599873027132669097105)
      ·
        refine ⟨535199904770349501822829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 713599873027132669097105 535199904770349501822829)
        ·
          refine ⟨200699964288881063183561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 535199904770349501822829 200699964288881063183561)
          ·
            refine ⟨150524973216660797387671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200699964288881063183561 150524973216660797387671)
            ·
              refine ⟨225787459824991196081507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150524973216660797387671 225787459824991196081507)
              ·
                refine ⟨338681189737486794122261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225787459824991196081507 338681189737486794122261)
                ·
                  refine ⟨15875680768944693474481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 338681189737486794122261 15875680768944693474481)
                  ·
                    rfl

theorem cell21_69565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_69565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69565 prefixEnd_69565 := by exact prefixLift 69565
  have htrace : WordTrace (prefixWord ++ tailWord_69565) baseStart_69565 baseEnd_69565 := by
    simpa [prefixWord, tailWord_69565, baseEnd_69565] using wordTrace_append hprefix tailTrace_69565
  have hstable : (prefixWord ++ tailWord_69565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69565).length < 2 ^ (prefixWord ++ tailWord_69565).sum := by decide
  have hdescent : baseEnd_69565 < baseStart_69565 := by decide
  rcases family_descends (prefixWord ++ tailWord_69565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69582 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_69582 : Nat := 118140960795 + 69582 * 2 ^ 59
def prefixEnd_69582 : Nat := 4983230072969 + 3 ^ 40 * 69582 * 2
def baseEnd_69582 : Nat := 15879560400556441691113

theorem tailTrace_69582 : CollatzResearch.WordTrace tailWord_69582 prefixEnd_69582 15879560400556441691113 := by
  unfold tailWord_69582
  simp only [CollatzResearch.WordTrace]
  refine ⟨317233004240471563075375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1691909355949181669735333 317233004240471563075375)
  ·
    refine ⟨475849506360707344613063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317233004240471563075375 475849506360707344613063)
    ·
      refine ⟨713774259541061016919595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 475849506360707344613063 713774259541061016919595)
      ·
        refine ⟨1070661389311591525379393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713774259541061016919595 1070661389311591525379393)
        ·
          refine ⟨802996041983693644034545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070661389311591525379393 802996041983693644034545)
          ·
            refine ⟨602247031487770233025909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802996041983693644034545 602247031487770233025909)
            ·
              refine ⟨56460659201978459346179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 602247031487770233025909 56460659201978459346179)
              ·
                refine ⟨84690988802967689019269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56460659201978459346179 84690988802967689019269)
                ·
                  refine ⟨15879560400556441691113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84690988802967689019269 15879560400556441691113)
                  ·
                    rfl

theorem cell21_69582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_69582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69582 prefixEnd_69582 := by exact prefixLift 69582
  have htrace : WordTrace (prefixWord ++ tailWord_69582) baseStart_69582 baseEnd_69582 := by
    simpa [prefixWord, tailWord_69582, baseEnd_69582] using wordTrace_append hprefix tailTrace_69582
  have hstable : (prefixWord ++ tailWord_69582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69582).length < 2 ^ (prefixWord ++ tailWord_69582).sum := by decide
  have hdescent : baseEnd_69582 < baseStart_69582 := by decide
  rcases family_descends (prefixWord ++ tailWord_69582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69602 : List Nat := [3, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_69602 : Nat := 118140960795 + 69602 * 2 ^ 59
def prefixEnd_69602 : Nat := 4983230072969 + 3 ^ 40 * 69602 * 2
def baseEnd_69602 : Nat := 15884124673040851357739

theorem tailTrace_69602 : CollatzResearch.WordTrace tailWord_69602 prefixEnd_69602 15884124673040851357739 := by
  unfold tailWord_69602
  simp only [CollatzResearch.WordTrace]
  refine ⟨634648373462828980082765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1692395662567543946887373 634648373462828980082765)
  ·
    refine ⟨237993140048560867531037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 634648373462828980082765 237993140048560867531037)
    ·
      refine ⟨89247427518210325324139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237993140048560867531037 89247427518210325324139)
      ·
        refine ⟨133871141277315487986209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89247427518210325324139 133871141277315487986209)
        ·
          refine ⟨100403355957986615989657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133871141277315487986209 100403355957986615989657)
          ·
            refine ⟨75302516968489961992243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100403355957986615989657 75302516968489961992243)
            ·
              refine ⟨112953775452734942988365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75302516968489961992243 112953775452734942988365)
              ·
                refine ⟨42357665794775603620637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112953775452734942988365 42357665794775603620637)
                ·
                  refine ⟨15884124673040851357739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42357665794775603620637 15884124673040851357739)
                  ·
                    rfl

theorem cell21_69602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_69602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69602 prefixEnd_69602 := by exact prefixLift 69602
  have htrace : WordTrace (prefixWord ++ tailWord_69602) baseStart_69602 baseEnd_69602 := by
    simpa [prefixWord, tailWord_69602, baseEnd_69602] using wordTrace_append hprefix tailTrace_69602
  have hstable : (prefixWord ++ tailWord_69602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69602).length < 2 ^ (prefixWord ++ tailWord_69602).sum := by decide
  have hdescent : baseEnd_69602 < baseStart_69602 := by decide
  rcases family_descends (prefixWord ++ tailWord_69602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69613 : List Nat := [1, 5, 1, 4, 1, 2, 7]
def baseStart_69613 : Nat := 118140960795 + 69613 * 2 ^ 59
def prefixEnd_69613 : Nat := 4983230072969 + 3 ^ 40 * 69613 * 2
def baseEnd_69613 : Nat := 1765181669211919630487

theorem tailTrace_69613 : CollatzResearch.WordTrace tailWord_69613 prefixEnd_69613 1765181669211919630487 := by
  unfold tailWord_69613
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538994696811464798981493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1692663131207643199320995 2538994696811464798981493)
  ·
    refine ⟨238030752826074824904515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2538994696811464798981493 238030752826074824904515)
    ·
      refine ⟨357046129239112237356773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 238030752826074824904515 357046129239112237356773)
      ·
        refine ⟨66946149232333544504395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 357046129239112237356773 66946149232333544504395)
        ·
          refine ⟨100419223848500316756593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66946149232333544504395 100419223848500316756593)
          ·
            refine ⟨75314417886375237567445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100419223848500316756593 75314417886375237567445)
            ·
              refine ⟨1765181669211919630487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75314417886375237567445 1765181669211919630487)
              ·
                rfl

theorem cell21_69613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 7].length) (baseStart_69613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69613 prefixEnd_69613 := by exact prefixLift 69613
  have htrace : WordTrace (prefixWord ++ tailWord_69613) baseStart_69613 baseEnd_69613 := by
    simpa [prefixWord, tailWord_69613, baseEnd_69613] using wordTrace_append hprefix tailTrace_69613
  have hstable : (prefixWord ++ tailWord_69613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69613).length < 2 ^ (prefixWord ++ tailWord_69613).sum := by decide
  have hdescent : baseEnd_69613 < baseStart_69613 := by decide
  rcases family_descends (prefixWord ++ tailWord_69613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69624 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_69624 : Nat := 118140960795 + 69624 * 2 ^ 59
def prefixEnd_69624 : Nat := 4983230072969 + 3 ^ 40 * 69624 * 2
def baseEnd_69624 : Nat := 15889145372773701991027

theorem tailTrace_69624 : CollatzResearch.WordTrace tailWord_69624 prefixEnd_69624 15889145372773701991027 := by
  unfold tailWord_69624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1269697949885806838815963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1692930599847742451754617 1269697949885806838815963)
  ·
    refine ⟨1904546924828710258223945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1269697949885806838815963 1904546924828710258223945)
    ·
      refine ⟨1428410193621532693667959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1904546924828710258223945 1428410193621532693667959)
      ·
        refine ⟨2142615290432299040501939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428410193621532693667959 2142615290432299040501939)
        ·
          refine ⟨3213922935648448560752909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142615290432299040501939 3213922935648448560752909)
          ·
            refine ⟨1205221100868168210282341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3213922935648448560752909 1205221100868168210282341)
            ·
              refine ⟨225978956412781539427939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1205221100868168210282341 225978956412781539427939)
              ·
                refine ⟨338968434619172309141909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225978956412781539427939 338968434619172309141909)
                ·
                  refine ⟨15889145372773701991027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 338968434619172309141909 15889145372773701991027)
                  ·
                    rfl

theorem cell21_69624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_69624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69624 prefixEnd_69624 := by exact prefixLift 69624
  have htrace : WordTrace (prefixWord ++ tailWord_69624) baseStart_69624 baseEnd_69624 := by
    simpa [prefixWord, tailWord_69624, baseEnd_69624] using wordTrace_append hprefix tailTrace_69624
  have hstable : (prefixWord ++ tailWord_69624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69624).length < 2 ^ (prefixWord ++ tailWord_69624).sum := by decide
  have hdescent : baseEnd_69624 < baseStart_69624 := by decide
  rcases family_descends (prefixWord ++ tailWord_69624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69672 : List Nat := [2, 1, 5, 3, 1, 9]
def baseStart_69672 : Nat := 118140960795 + 69672 * 2 ^ 59
def prefixEnd_69672 : Nat := 4983230072969 + 3 ^ 40 * 69672 * 2
def baseEnd_69672 : Nat := 588892578768010562627

theorem tailTrace_69672 : CollatzResearch.WordTrace tailWord_69672 prefixEnd_69672 588892578768010562627 := by
  unfold tailWord_69672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270573301798858937689635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1694097735731811916919513 1270573301798858937689635)
  ·
    refine ⟨1905859952698288406534453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270573301798858937689635 1905859952698288406534453)
    ·
      refine ⟨178674370565464538112605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1905859952698288406534453 178674370565464538112605)
      ·
        refine ⟨67002888962049201792227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178674370565464538112605 67002888962049201792227)
        ·
          refine ⟨100504333443073802688341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67002888962049201792227 100504333443073802688341)
          ·
            refine ⟨588892578768010562627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 100504333443073802688341 588892578768010562627)
            ·
              rfl

theorem cell21_69672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 9].length) (baseStart_69672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69672 prefixEnd_69672 := by exact prefixLift 69672
  have htrace : WordTrace (prefixWord ++ tailWord_69672) baseStart_69672 baseEnd_69672 := by
    simpa [prefixWord, tailWord_69672, baseEnd_69672] using wordTrace_append hprefix tailTrace_69672
  have hstable : (prefixWord ++ tailWord_69672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69672).length < 2 ^ (prefixWord ++ tailWord_69672).sum := by decide
  have hdescent : baseEnd_69672 < baseStart_69672 := by decide
  rcases family_descends (prefixWord ++ tailWord_69672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69689 : List Nat := [1, 2, 1, 5, 4, 1, 1, 6]
def baseStart_69689 : Nat := 118140960795 + 69689 * 2 ^ 59
def prefixEnd_69689 : Nat := 4983230072969 + 3 ^ 40 * 69689 * 2
def baseEnd_69689 : Nat := 5301326419449344469187

theorem tailTrace_69689 : CollatzResearch.WordTrace tailWord_69689 prefixEnd_69689 5301326419449344469187 := by
  unfold tailWord_69689
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541766644536129778748121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694511096357419852498747 2541766644536129778748121)
  ·
    refine ⟨1906324983402097334061091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2541766644536129778748121 1906324983402097334061091)
    ·
      refine ⟨2859487475103146001091637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906324983402097334061091 2859487475103146001091637)
      ·
        refine ⟨268076950790919937602341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2859487475103146001091637 268076950790919937602341)
        ·
          refine ⟨50264428273297488300439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 268076950790919937602341 50264428273297488300439)
          ·
            refine ⟨75396642409946232450659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50264428273297488300439 75396642409946232450659)
            ·
              refine ⟨113094963614919348675989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75396642409946232450659 113094963614919348675989)
              ·
                refine ⟨5301326419449344469187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113094963614919348675989 5301326419449344469187)
                ·
                  rfl

theorem cell21_69689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 6].length) (baseStart_69689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69689 prefixEnd_69689 := by exact prefixLift 69689
  have htrace : WordTrace (prefixWord ++ tailWord_69689) baseStart_69689 baseEnd_69689 := by
    simpa [prefixWord, tailWord_69689, baseEnd_69689] using wordTrace_append hprefix tailTrace_69689
  have hstable : (prefixWord ++ tailWord_69689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69689).length < 2 ^ (prefixWord ++ tailWord_69689).sum := by decide
  have hdescent : baseEnd_69689 < baseStart_69689 := by decide
  rcases family_descends (prefixWord ++ tailWord_69689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69796 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_69796 : Nat := 118140960795 + 69796 * 2 ^ 59
def prefixEnd_69796 : Nat := 4983230072969 + 3 ^ 40 * 69796 * 2
def baseEnd_69796 : Nat := 15928398116139625124009

theorem tailTrace_69796 : CollatzResearch.WordTrace tailWord_69796 prefixEnd_69796 15928398116139625124009 := by
  unfold tailWord_69796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272834627574243526446621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1697112836765658035262161 1272834627574243526446621)
  ·
    refine ⟨477312985340341322417483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1272834627574243526446621 477312985340341322417483)
    ·
      refine ⟨715969478010511983626225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477312985340341322417483 715969478010511983626225)
      ·
        refine ⟨536977108507883987719669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 715969478010511983626225 536977108507883987719669)
        ·
          refine ⟨50341603922614123848719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 536977108507883987719669 50341603922614123848719)
          ·
            refine ⟨75512405883921185773079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50341603922614123848719 75512405883921185773079)
            ·
              refine ⟨113268608825881778659619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75512405883921185773079 113268608825881778659619)
              ·
                refine ⟨169902913238822667989429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113268608825881778659619 169902913238822667989429)
                ·
                  refine ⟨15928398116139625124009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 169902913238822667989429 15928398116139625124009)
                  ·
                    rfl

theorem cell21_69796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_69796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69796 prefixEnd_69796 := by exact prefixLift 69796
  have htrace : WordTrace (prefixWord ++ tailWord_69796) baseStart_69796 baseEnd_69796 := by
    simpa [prefixWord, tailWord_69796, baseEnd_69796] using wordTrace_append hprefix tailTrace_69796
  have hstable : (prefixWord ++ tailWord_69796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69796).length < 2 ^ (prefixWord ++ tailWord_69796).sum := by decide
  have hdescent : baseEnd_69796 < baseStart_69796 := by decide
  rcases family_descends (prefixWord ++ tailWord_69796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69821 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_69821 : Nat := 118140960795 + 69821 * 2 ^ 59
def prefixEnd_69821 : Nat := 4983230072969 + 3 ^ 40 * 69821 * 2
def baseEnd_69821 : Nat := 15934103456745137207291

theorem tailTrace_69821 : CollatzResearch.WordTrace tailWord_69821 prefixEnd_69821 15934103456745137207291 := by
  unfold tailWord_69821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546581080057916322553317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1697720720038610881702211 2546581080057916322553317)
  ·
    refine ⟨477483952510859310478747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2546581080057916322553317 477483952510859310478747)
    ·
      refine ⟨716225928766288965718121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477483952510859310478747 716225928766288965718121)
      ·
        refine ⟨537169446574716724288591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 716225928766288965718121 537169446574716724288591)
        ·
          refine ⟨805754169862075086432887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537169446574716724288591 805754169862075086432887)
          ·
            refine ⟨1208631254793112629649331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805754169862075086432887 1208631254793112629649331)
            ·
              refine ⟨1812946882189668944473997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208631254793112629649331 1812946882189668944473997)
              ·
                refine ⟨679855080821125854177749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1812946882189668944473997 679855080821125854177749)
                ·
                  refine ⟨15934103456745137207291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 679855080821125854177749 15934103456745137207291)
                  ·
                    rfl

theorem cell21_69821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_69821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69821 prefixEnd_69821 := by exact prefixLift 69821
  have htrace : WordTrace (prefixWord ++ tailWord_69821) baseStart_69821 baseEnd_69821 := by
    simpa [prefixWord, tailWord_69821, baseEnd_69821] using wordTrace_append hprefix tailTrace_69821
  have hstable : (prefixWord ++ tailWord_69821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69821).length < 2 ^ (prefixWord ++ tailWord_69821).sum := by decide
  have hdescent : baseEnd_69821 < baseStart_69821 := by decide
  rcases family_descends (prefixWord ++ tailWord_69821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69934 : List Nat := [4, 1, 3, 3, 1, 2, 2, 5]
def baseStart_69934 : Nat := 118140960795 + 69934 * 2 ^ 59
def prefixEnd_69934 : Nat := 4983230072969 + 3 ^ 40 * 69934 * 2
def baseEnd_69934 : Nat := 5319963865427350607909

theorem tailTrace_69934 : CollatzResearch.WordTrace tailWord_69934 prefixEnd_69934 5319963865427350607909 := by
  unfold tailWord_69934
  simp only [CollatzResearch.WordTrace]
  refine ⟨318837816081067077677107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1700468352432357747611237 318837816081067077677107)
  ·
    refine ⟨478256724121600616515661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318837816081067077677107 478256724121600616515661)
    ·
      refine ⟨179346271545600231193373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 478256724121600616515661 179346271545600231193373)
      ·
        refine ⟨67254851829600086697515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179346271545600231193373 67254851829600086697515)
        ·
          refine ⟨100882277744400130046273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67254851829600086697515 100882277744400130046273)
          ·
            refine ⟨75661708308300097534705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100882277744400130046273 75661708308300097534705)
            ·
              refine ⟨56746281231225073151029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75661708308300097534705 56746281231225073151029)
              ·
                refine ⟨5319963865427350607909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56746281231225073151029 5319963865427350607909)
                ·
                  rfl

theorem cell21_69934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_69934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_69934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_69934 prefixEnd_69934 := by exact prefixLift 69934
  have htrace : WordTrace (prefixWord ++ tailWord_69934) baseStart_69934 baseEnd_69934 := by
    simpa [prefixWord, tailWord_69934, baseEnd_69934] using wordTrace_append hprefix tailTrace_69934
  have hstable : (prefixWord ++ tailWord_69934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69934).length < 2 ^ (prefixWord ++ tailWord_69934).sum := by decide
  have hdescent : baseEnd_69934 < baseStart_69934 := by decide
  rcases family_descends (prefixWord ++ tailWord_69934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70058 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_70058 : Nat := 118140960795 + 70058 * 2 ^ 59
def prefixEnd_70058 : Nat := 4983230072969 + 3 ^ 40 * 70058 * 2
def baseEnd_70058 : Nat := 15988190085685391756807

theorem tailTrace_70058 : CollatzResearch.WordTrace tailWord_70058 prefixEnd_70058 15988190085685391756807 := by
  unfold tailWord_70058
  simp only [CollatzResearch.WordTrace]
  refine ⟨638806295049826449732707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1703483453466203865953885 638806295049826449732707)
  ·
    refine ⟨958209442574739674599061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 638806295049826449732707 958209442574739674599061)
    ·
      refine ⟨44916067620690922246831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 958209442574739674599061 44916067620690922246831)
      ·
        refine ⟨67374101431036383370247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44916067620690922246831 67374101431036383370247)
        ·
          refine ⟨101061152146554575055371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67374101431036383370247 101061152146554575055371)
          ·
            refine ⟨151591728219831862583057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101061152146554575055371 151591728219831862583057)
            ·
              refine ⟨113693796164873896937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151591728219831862583057 113693796164873896937293)
              ·
                refine ⟨42635173561827711351485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113693796164873896937293 42635173561827711351485)
                ·
                  refine ⟨15988190085685391756807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42635173561827711351485 15988190085685391756807)
                  ·
                    rfl

theorem cell21_70058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_70058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70058 prefixEnd_70058 := by exact prefixLift 70058
  have htrace : WordTrace (prefixWord ++ tailWord_70058) baseStart_70058 baseEnd_70058 := by
    simpa [prefixWord, tailWord_70058, baseEnd_70058] using wordTrace_append hprefix tailTrace_70058
  have hstable : (prefixWord ++ tailWord_70058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70058).length < 2 ^ (prefixWord ++ tailWord_70058).sum := by decide
  have hdescent : baseEnd_70058 < baseStart_70058 := by decide
  rcases family_descends (prefixWord ++ tailWord_70058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70094 : List Nat := [4, 1, 1, 1, 2, 1, 1, 10]
def baseStart_70094 : Nat := 118140960795 + 70094 * 2 ^ 59
def prefixEnd_70094 : Nat := 4983230072969 + 3 ^ 40 * 70094 * 2
def baseEnd_70094 : Nat := 5332135258719109718911

theorem tailTrace_70094 : CollatzResearch.WordTrace tailWord_70094 prefixEnd_70094 5332135258719109718911 := by
  unfold tailWord_70094
  simp only [CollatzResearch.WordTrace]
  refine ⟨319567276008610493405167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1704358805379255964827557 319567276008610493405167)
  ·
    refine ⟨479350914012915740107751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319567276008610493405167 479350914012915740107751)
    ·
      refine ⟨719026371019373610161627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479350914012915740107751 719026371019373610161627)
      ·
        refine ⟨1078539556529060415242441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719026371019373610161627 1078539556529060415242441)
        ·
          refine ⟨808904667396795311431831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078539556529060415242441 808904667396795311431831)
          ·
            refine ⟨1213357001095192967147747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808904667396795311431831 1213357001095192967147747)
            ·
              refine ⟨1820035501642789450721621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213357001095192967147747 1820035501642789450721621)
              ·
                refine ⟨5332135258719109718911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1820035501642789450721621 5332135258719109718911)
                ·
                  rfl

theorem cell21_70094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_70094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70094 prefixEnd_70094 := by exact prefixLift 70094
  have htrace : WordTrace (prefixWord ++ tailWord_70094) baseStart_70094 baseEnd_70094 := by
    simpa [prefixWord, tailWord_70094, baseEnd_70094] using wordTrace_append hprefix tailTrace_70094
  have hstable : (prefixWord ++ tailWord_70094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70094).length < 2 ^ (prefixWord ++ tailWord_70094).sum := by decide
  have hdescent : baseEnd_70094 < baseStart_70094 := by decide
  rcases family_descends (prefixWord ++ tailWord_70094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70111 : List Nat := [1, 1, 2, 3, 3, 2, 4, 5]
def baseStart_70111 : Nat := 118140960795 + 70111 * 2 ^ 59
def prefixEnd_70111 : Nat := 4983230072969 + 3 ^ 40 * 70111 * 2
def baseEnd_70111 : Nat := 5333428469256359124455

theorem tailTrace_70111 : CollatzResearch.WordTrace tailWord_70111 prefixEnd_70111 5333428469256359124455 := by
  unfold tailWord_70111
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557158249007295850610187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704772166004863900406791 2557158249007295850610187)
  ·
    refine ⟨3835737373510943775915281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2557158249007295850610187 3835737373510943775915281)
    ·
      refine ⟨2876803030133207831936461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3835737373510943775915281 2876803030133207831936461)
      ·
        refine ⟨1078801136299952936976173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2876803030133207831936461 1078801136299952936976173)
        ·
          refine ⟨404550426112482351366065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1078801136299952936976173 404550426112482351366065)
          ·
            refine ⟨303412819584361763524549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404550426112482351366065 303412819584361763524549)
            ·
              refine ⟨56889903672067830660853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 303412819584361763524549 56889903672067830660853)
              ·
                refine ⟨5333428469256359124455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56889903672067830660853 5333428469256359124455)
                ·
                  rfl

theorem cell21_70111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 5].length) (baseStart_70111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70111 prefixEnd_70111 := by exact prefixLift 70111
  have htrace : WordTrace (prefixWord ++ tailWord_70111) baseStart_70111 baseEnd_70111 := by
    simpa [prefixWord, tailWord_70111, baseEnd_70111] using wordTrace_append hprefix tailTrace_70111
  have hstable : (prefixWord ++ tailWord_70111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70111).length < 2 ^ (prefixWord ++ tailWord_70111).sum := by decide
  have hdescent : baseEnd_70111 < baseStart_70111 := by decide
  rcases family_descends (prefixWord ++ tailWord_70111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70117 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 3]
def baseStart_70117 : Nat := 118140960795 + 70117 * 2 ^ 59
def prefixEnd_70117 : Nat := 4983230072969 + 3 ^ 40 * 70117 * 2
def baseEnd_70117 : Nat := 16001654689514400273353

theorem tailTrace_70117 : CollatzResearch.WordTrace tailWord_70117 prefixEnd_70117 16001654689514400273353 := by
  unfold tailWord_70117
  simp only [CollatzResearch.WordTrace]
  refine ⟨2557377086985558875328605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704918057990372583552403 2557377086985558875328605)
  ·
    refine ⟨959016407619584578248227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2557377086985558875328605 959016407619584578248227)
    ·
      refine ⟨1438524611429376867372341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959016407619584578248227 1438524611429376867372341)
      ·
        refine ⟨134861682321504081316157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1438524611429376867372341 134861682321504081316157)
        ·
          refine ⟨50573130870564030493559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134861682321504081316157 50573130870564030493559)
          ·
            refine ⟨75859696305846045740339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50573130870564030493559 75859696305846045740339)
            ·
              refine ⟨113789544458769068610509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75859696305846045740339 113789544458769068610509)
              ·
                refine ⟨42671079172038400728941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113789544458769068610509 42671079172038400728941)
                ·
                  refine ⟨16001654689514400273353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42671079172038400728941 16001654689514400273353)
                  ·
                    rfl

theorem cell21_70117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_70117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70117 prefixEnd_70117 := by exact prefixLift 70117
  have htrace : WordTrace (prefixWord ++ tailWord_70117) baseStart_70117 baseEnd_70117 := by
    simpa [prefixWord, tailWord_70117, baseEnd_70117] using wordTrace_append hprefix tailTrace_70117
  have hstable : (prefixWord ++ tailWord_70117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70117).length < 2 ^ (prefixWord ++ tailWord_70117).sum := by decide
  have hdescent : baseEnd_70117 < baseStart_70117 := by decide
  rcases family_descends (prefixWord ++ tailWord_70117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70170 : List Nat := [3, 1, 1, 3, 1, 1, 4, 7]
def baseStart_70170 : Nat := 118140960795 + 70170 * 2 ^ 59
def prefixEnd_70170 : Nat := 4983230072969 + 3 ^ 40 * 70170 * 2
def baseEnd_70170 : Nat := 5337916670532695296637

theorem tailTrace_70170 : CollatzResearch.WordTrace tailWord_70170 prefixEnd_70170 5337916670532695296637 := by
  unfold tailWord_70170
  simp only [CollatzResearch.WordTrace]
  refine ⟨639827538948387231751991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1706206770529032618005309 639827538948387231751991)
  ·
    refine ⟨959741308422580847627987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639827538948387231751991 959741308422580847627987)
    ·
      refine ⟨1439611962633871271441981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959741308422580847627987 1439611962633871271441981)
      ·
        refine ⟨539854485987701726790743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1439611962633871271441981 539854485987701726790743)
        ·
          refine ⟨809781728981552590186115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539854485987701726790743 809781728981552590186115)
          ·
            refine ⟨1214672593472328885279173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809781728981552590186115 1214672593472328885279173)
            ·
              refine ⟨227751111276061665989845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1214672593472328885279173 227751111276061665989845)
              ·
                refine ⟨5337916670532695296637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 227751111276061665989845 5337916670532695296637)
                ·
                  rfl

theorem cell21_70170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_70170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70170 prefixEnd_70170 := by exact prefixLift 70170
  have htrace : WordTrace (prefixWord ++ tailWord_70170) baseStart_70170 baseEnd_70170 := by
    simpa [prefixWord, tailWord_70170, baseEnd_70170] using wordTrace_append hprefix tailTrace_70170
  have hstable : (prefixWord ++ tailWord_70170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70170).length < 2 ^ (prefixWord ++ tailWord_70170).sum := by decide
  have hdescent : baseEnd_70170 < baseStart_70170 := by decide
  rcases family_descends (prefixWord ++ tailWord_70170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70190 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_70190 : Nat := 118140960795 + 70190 * 2 ^ 59
def prefixEnd_70190 : Nat := 4983230072969 + 3 ^ 40 * 70190 * 2
def baseEnd_70190 : Nat := 16018314284082495556537

theorem tailTrace_70190 : CollatzResearch.WordTrace tailWord_70190 prefixEnd_70190 16018314284082495556537 := by
  unfold tailWord_70190
  simp only [CollatzResearch.WordTrace]
  refine ⟨320004951965136542842003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1706693077147394895157349 320004951965136542842003)
  ·
    refine ⟨480007427947704814263005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320004951965136542842003 480007427947704814263005)
    ·
      refine ⟨180002785480389305348627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 480007427947704814263005 180002785480389305348627)
      ·
        refine ⟨270004178220583958022941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180002785480389305348627 270004178220583958022941)
        ·
          refine ⟨101251566832718984258603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270004178220583958022941 101251566832718984258603)
          ·
            refine ⟨151877350249078476387905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101251566832718984258603 151877350249078476387905)
            ·
              refine ⟨113908012686808857290929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151877350249078476387905 113908012686808857290929)
              ·
                refine ⟨85431009515106642968197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113908012686808857290929 85431009515106642968197)
                ·
                  refine ⟨16018314284082495556537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85431009515106642968197 16018314284082495556537)
                  ·
                    rfl

theorem cell21_70190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_70190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70190 prefixEnd_70190 := by exact prefixLift 70190
  have htrace : WordTrace (prefixWord ++ tailWord_70190) baseStart_70190 baseEnd_70190 := by
    simpa [prefixWord, tailWord_70190, baseEnd_70190] using wordTrace_append hprefix tailTrace_70190
  have hstable : (prefixWord ++ tailWord_70190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70190).length < 2 ^ (prefixWord ++ tailWord_70190).sum := by decide
  have hdescent : baseEnd_70190 < baseStart_70190 := by decide
  rcases family_descends (prefixWord ++ tailWord_70190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70201 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_70201 : Nat := 118140960795 + 70201 * 2 ^ 59
def prefixEnd_70201 : Nat := 4983230072969 + 3 ^ 40 * 70201 * 2
def baseEnd_70201 : Nat := 16020824633948920873181

theorem tailTrace_70201 : CollatzResearch.WordTrace tailWord_70201 prefixEnd_70201 16020824633948920873181 := by
  unfold tailWord_70201
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560440818681241221386457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1706960545787494147590971 2560440818681241221386457)
  ·
    refine ⟨1920330614010930916039843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2560440818681241221386457 1920330614010930916039843)
    ·
      refine ⟨2880495921016396374059765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920330614010930916039843 2880495921016396374059765)
      ·
        refine ⟨270046492595287160068103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2880495921016396374059765 270046492595287160068103)
        ·
          refine ⟨405069738892930740102155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270046492595287160068103 405069738892930740102155)
          ·
            refine ⟨607604608339396110153233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405069738892930740102155 607604608339396110153233)
            ·
              refine ⟨455703456254547082614925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607604608339396110153233 455703456254547082614925)
              ·
                refine ⟨170888796095455155980597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455703456254547082614925 170888796095455155980597)
                ·
                  refine ⟨16020824633948920873181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170888796095455155980597 16020824633948920873181)
                  ·
                    rfl

theorem cell21_70201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_70201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70201 prefixEnd_70201 := by exact prefixLift 70201
  have htrace : WordTrace (prefixWord ++ tailWord_70201) baseStart_70201 baseEnd_70201 := by
    simpa [prefixWord, tailWord_70201, baseEnd_70201] using wordTrace_append hprefix tailTrace_70201
  have hstable : (prefixWord ++ tailWord_70201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70201).length < 2 ^ (prefixWord ++ tailWord_70201).sum := by decide
  have hdescent : baseEnd_70201 < baseStart_70201 := by decide
  rcases family_descends (prefixWord ++ tailWord_70201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70277 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_70277 : Nat := 118140960795 + 70277 * 2 ^ 59
def prefixEnd_70277 : Nat := 4983230072969 + 3 ^ 40 * 70277 * 2
def baseEnd_70277 : Nat := 16038168869389677606359

theorem tailTrace_70277 : CollatzResearch.WordTrace tailWord_70277 prefixEnd_70277 16038168869389677606359 := by
  unfold tailWord_70277
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563212766405906201153085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1708808510937270800768723 2563212766405906201153085)
  ·
    refine ⟨961204787402214825432407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2563212766405906201153085 961204787402214825432407)
    ·
      refine ⟨1441807181103322238148611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961204787402214825432407 1441807181103322238148611)
      ·
        refine ⟨2162710771654983357222917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441807181103322238148611 2162710771654983357222917)
        ·
          refine ⟨405508269685309379479297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2162710771654983357222917 405508269685309379479297)
          ·
            refine ⟨304131202263982034609473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405508269685309379479297 304131202263982034609473)
            ·
              refine ⟨228098401697986525957105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304131202263982034609473 228098401697986525957105)
              ·
                refine ⟨171073801273489894467829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228098401697986525957105 171073801273489894467829)
                ·
                  refine ⟨16038168869389677606359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171073801273489894467829 16038168869389677606359)
                  ·
                    rfl

theorem cell21_70277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_70277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70277 prefixEnd_70277 := by exact prefixLift 70277
  have htrace : WordTrace (prefixWord ++ tailWord_70277) baseStart_70277 baseEnd_70277 := by
    simpa [prefixWord, tailWord_70277, baseEnd_70277] using wordTrace_append hprefix tailTrace_70277
  have hstable : (prefixWord ++ tailWord_70277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70277).length < 2 ^ (prefixWord ++ tailWord_70277).sum := by decide
  have hdescent : baseEnd_70277 < baseStart_70277 := by decide
  rcases family_descends (prefixWord ++ tailWord_70277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70308 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_70308 : Nat := 118140960795 + 70308 * 2 ^ 59
def prefixEnd_70308 : Nat := 4983230072969 + 3 ^ 40 * 70308 * 2
def baseEnd_70308 : Nat := 16045243491740512589629

theorem tailTrace_70308 : CollatzResearch.WordTrace tailWord_70308 prefixEnd_70308 16045243491740512589629 := by
  unfold tailWord_70308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282171714646799247765789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1709562286195732330354385 1282171714646799247765789)
  ·
    refine ⟨480814392992549717912171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1282171714646799247765789 480814392992549717912171)
    ·
      refine ⟨721221589488824576868257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480814392992549717912171 721221589488824576868257)
      ·
        refine ⟨540916192116618432651193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 721221589488824576868257 540916192116618432651193)
        ·
          refine ⟨405687144087463824488395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540916192116618432651193 405687144087463824488395)
          ·
            refine ⟨608530716131195736732593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405687144087463824488395 608530716131195736732593)
            ·
              refine ⟨456398037098396802549445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608530716131195736732593 456398037098396802549445)
              ·
                refine ⟨85574631955949400478021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456398037098396802549445 85574631955949400478021)
                ·
                  refine ⟨16045243491740512589629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85574631955949400478021 16045243491740512589629)
                  ·
                    rfl

theorem cell21_70308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_70308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70308 prefixEnd_70308 := by exact prefixLift 70308
  have htrace : WordTrace (prefixWord ++ tailWord_70308) baseStart_70308 baseEnd_70308 := by
    simpa [prefixWord, tailWord_70308, baseEnd_70308] using wordTrace_append hprefix tailTrace_70308
  have hstable : (prefixWord ++ tailWord_70308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70308).length < 2 ^ (prefixWord ++ tailWord_70308).sum := by decide
  have hdescent : baseEnd_70308 < baseStart_70308 := by decide
  rcases family_descends (prefixWord ++ tailWord_70308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70325 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_70325 : Nat := 118140960795 + 70325 * 2 ^ 59
def prefixEnd_70325 : Nat := 4983230072969 + 3 ^ 40 * 70325 * 2
def baseEnd_70325 : Nat := 16049123123352260806261

theorem tailTrace_70325 : CollatzResearch.WordTrace tailWord_70325 prefixEnd_70325 16049123123352260806261 := by
  unfold tailWord_70325
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564963470232010398900429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1709975646821340265933619 2564963470232010398900429)
  ·
    refine ⟨961861301337003899587661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2564963470232010398900429 961861301337003899587661)
    ·
      refine ⟨360697988001376462345373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 961861301337003899587661 360697988001376462345373)
      ·
        refine ⟨135261745500516173379515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360697988001376462345373 135261745500516173379515)
        ·
          refine ⟨202892618250774260069273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135261745500516173379515 202892618250774260069273)
          ·
            refine ⟨152169463688080695051955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202892618250774260069273 152169463688080695051955)
            ·
              refine ⟨228254195532121042577933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152169463688080695051955 228254195532121042577933)
              ·
                refine ⟨85595323324545390966725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228254195532121042577933 85595323324545390966725)
                ·
                  refine ⟨16049123123352260806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85595323324545390966725 16049123123352260806261)
                  ·
                    rfl

theorem cell21_70325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_70325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70325 prefixEnd_70325 := by exact prefixLift 70325
  have htrace : WordTrace (prefixWord ++ tailWord_70325) baseStart_70325 baseEnd_70325 := by
    simpa [prefixWord, tailWord_70325, baseEnd_70325] using wordTrace_append hprefix tailTrace_70325
  have hstable : (prefixWord ++ tailWord_70325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70325).length < 2 ^ (prefixWord ++ tailWord_70325).sum := by decide
  have hdescent : baseEnd_70325 < baseStart_70325 := by decide
  rcases family_descends (prefixWord ++ tailWord_70325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70412 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_70412 : Nat := 118140960795 + 70412 * 2 ^ 59
def prefixEnd_70412 : Nat := 4983230072969 + 3 ^ 40 * 70412 * 2
def baseEnd_70412 : Nat := 16068977708659442856083

theorem tailTrace_70412 : CollatzResearch.WordTrace tailWord_70412 prefixEnd_70412 16068977708659442856083 := by
  unfold tailWord_70412
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284068310458412128658745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1712091080611216171544993 1284068310458412128658745)
  ·
    refine ⟨963051232843809096494059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1284068310458412128658745 963051232843809096494059)
    ·
      refine ⟨1444576849265713644741089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963051232843809096494059 1444576849265713644741089)
      ·
        refine ⟨1083432636949285233555817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1444576849265713644741089 1083432636949285233555817)
        ·
          refine ⟨812574477711963925166863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083432636949285233555817 812574477711963925166863)
          ·
            refine ⟨1218861716567945887750295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812574477711963925166863 1218861716567945887750295)
            ·
              refine ⟨1828292574851918831625443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218861716567945887750295 1828292574851918831625443)
              ·
                refine ⟨2742438862277878247438165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828292574851918831625443 2742438862277878247438165)
                ·
                  refine ⟨16068977708659442856083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2742438862277878247438165 16068977708659442856083)
                  ·
                    rfl

theorem cell21_70412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_70412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70412 prefixEnd_70412 := by exact prefixLift 70412
  have htrace : WordTrace (prefixWord ++ tailWord_70412) baseStart_70412 baseEnd_70412 := by
    simpa [prefixWord, tailWord_70412, baseEnd_70412] using wordTrace_append hprefix tailTrace_70412
  have hstable : (prefixWord ++ tailWord_70412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70412).length < 2 ^ (prefixWord ++ tailWord_70412).sum := by decide
  have hdescent : baseEnd_70412 < baseStart_70412 := by decide
  rcases family_descends (prefixWord ++ tailWord_70412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70446 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_70446 : Nat := 118140960795 + 70446 * 2 ^ 59
def prefixEnd_70446 : Nat := 4983230072969 + 3 ^ 40 * 70446 * 2
def baseEnd_70446 : Nat := 16076736971882939289347

theorem tailTrace_70446 : CollatzResearch.WordTrace tailWord_70446 prefixEnd_70446 16076736971882939289347 := by
  unfold tailWord_70446
  simp only [CollatzResearch.WordTrace]
  refine ⟨321172087849206008006899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1712917801862432042703461 321172087849206008006899)
  ·
    refine ⟨481758131773809012010349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321172087849206008006899 481758131773809012010349)
    ·
      refine ⟨180659299415178379503881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 481758131773809012010349 180659299415178379503881)
      ·
        refine ⟨135494474561383784627911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180659299415178379503881 135494474561383784627911)
        ·
          refine ⟨203241711842075676941867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135494474561383784627911 203241711842075676941867)
          ·
            refine ⟨304862567763113515412801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203241711842075676941867 304862567763113515412801)
            ·
              refine ⟨228646925822335136559601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304862567763113515412801 228646925822335136559601)
              ·
                refine ⟨171485194366751352419701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228646925822335136559601 171485194366751352419701)
                ·
                  refine ⟨16076736971882939289347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171485194366751352419701 16076736971882939289347)
                  ·
                    rfl

theorem cell21_70446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_70446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70446 prefixEnd_70446 := by exact prefixLift 70446
  have htrace : WordTrace (prefixWord ++ tailWord_70446) baseStart_70446 baseEnd_70446 := by
    simpa [prefixWord, tailWord_70446, baseEnd_70446] using wordTrace_append hprefix tailTrace_70446
  have hstable : (prefixWord ++ tailWord_70446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70446).length < 2 ^ (prefixWord ++ tailWord_70446).sum := by decide
  have hdescent : baseEnd_70446 < baseStart_70446 := by decide
  rcases family_descends (prefixWord ++ tailWord_70446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70463 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 3]
def baseStart_70463 : Nat := 118140960795 + 70463 * 2 ^ 59
def prefixEnd_70463 : Nat := 4983230072969 + 3 ^ 40 * 70463 * 2
def baseEnd_70463 : Nat := 16080616603494687505979

theorem tailTrace_70463 : CollatzResearch.WordTrace tailWord_70463 prefixEnd_70463 16080616603494687505979 := by
  unfold tailWord_70463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569996743732059967424043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1713331162488039978282695 2569996743732059967424043)
  ·
    refine ⟨3854995115598089951136065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569996743732059967424043 3854995115598089951136065)
    ·
      refine ⟨2891246336698567463352049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854995115598089951136065 2891246336698567463352049)
      ·
        refine ⟨2168434752523925597514037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2891246336698567463352049 2168434752523925597514037)
        ·
          refine ⟨203290758049118024766941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2168434752523925597514037 203290758049118024766941)
          ·
            refine ⟨76234034268419259287603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203290758049118024766941 76234034268419259287603)
            ·
              refine ⟨114351051402628888931405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76234034268419259287603 114351051402628888931405)
              ·
                refine ⟨42881644275985833349277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114351051402628888931405 42881644275985833349277)
                ·
                  refine ⟨16080616603494687505979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42881644275985833349277 16080616603494687505979)
                  ·
                    rfl

theorem cell21_70463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3].length) (baseStart_70463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70463 prefixEnd_70463 := by exact prefixLift 70463
  have htrace : WordTrace (prefixWord ++ tailWord_70463) baseStart_70463 baseEnd_70463 := by
    simpa [prefixWord, tailWord_70463, baseEnd_70463] using wordTrace_append hprefix tailTrace_70463
  have hstable : (prefixWord ++ tailWord_70463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70463).length < 2 ^ (prefixWord ++ tailWord_70463).sum := by decide
  have hdescent : baseEnd_70463 < baseStart_70463 := by decide
  rcases family_descends (prefixWord ++ tailWord_70463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70533 : List Nat := [1, 3, 1, 1, 3, 12]
def baseStart_70533 : Nat := 118140960795 + 70533 * 2 ^ 59
def prefixEnd_70533 : Nat := 4983230072969 + 3 ^ 40 * 70533 * 2
def baseEnd_70533 : Nat := 596170057673708197747

theorem tailTrace_70533 : CollatzResearch.WordTrace tailWord_70533 prefixEnd_70533 596170057673708197747 := by
  unfold tailWord_70533
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572549853478461922472253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1715033235652307948314835 2572549853478461922472253)
  ·
    refine ⟨964706195054423220927095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2572549853478461922472253 964706195054423220927095)
    ·
      refine ⟨1447059292581634831390643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964706195054423220927095 1447059292581634831390643)
      ·
        refine ⟨2170588938872452247085965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447059292581634831390643 2170588938872452247085965)
        ·
          refine ⟨813970852077169592657237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2170588938872452247085965 813970852077169592657237)
          ·
            refine ⟨596170057673708197747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 813970852077169592657237 596170057673708197747)
            ·
              rfl

theorem cell21_70533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 12].length) (baseStart_70533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70533 prefixEnd_70533 := by exact prefixLift 70533
  have htrace : WordTrace (prefixWord ++ tailWord_70533) baseStart_70533 baseEnd_70533 := by
    simpa [prefixWord, tailWord_70533, baseEnd_70533] using wordTrace_append hprefix tailTrace_70533
  have hstable : (prefixWord ++ tailWord_70533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70533).length < 2 ^ (prefixWord ++ tailWord_70533).sum := by decide
  have hdescent : baseEnd_70533 < baseStart_70533 := by decide
  rcases family_descends (prefixWord ++ tailWord_70533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70536 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_70536 : Nat := 118140960795 + 70536 * 2 ^ 59
def prefixEnd_70536 : Nat := 4983230072969 + 3 ^ 40 * 70536 * 2
def baseEnd_70536 : Nat := 16097276198062782789163

theorem tailTrace_70536 : CollatzResearch.WordTrace tailWord_70536 prefixEnd_70536 16097276198062782789163 := by
  unfold tailWord_70536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286329636233796717415731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1715106181645062289887641 1286329636233796717415731)
  ·
    refine ⟨1929494454350695076123597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1286329636233796717415731 1929494454350695076123597)
    ·
      refine ⟨723560420381510653546349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1929494454350695076123597 723560420381510653546349)
      ·
        refine ⟨271335157643066495079881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 723560420381510653546349 271335157643066495079881)
        ·
          refine ⟨203501368232299871309911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271335157643066495079881 203501368232299871309911)
          ·
            refine ⟨305252052348449806964867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203501368232299871309911 305252052348449806964867)
            ·
              refine ⟨457878078522674710447301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305252052348449806964867 457878078522674710447301)
              ·
                refine ⟨85852139723001508208869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457878078522674710447301 85852139723001508208869)
                ·
                  refine ⟨16097276198062782789163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85852139723001508208869 16097276198062782789163)
                  ·
                    rfl

theorem cell21_70536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_70536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70536 prefixEnd_70536 := by exact prefixLift 70536
  have htrace : WordTrace (prefixWord ++ tailWord_70536) baseStart_70536 baseEnd_70536 := by
    simpa [prefixWord, tailWord_70536, baseEnd_70536] using wordTrace_append hprefix tailTrace_70536
  have hstable : (prefixWord ++ tailWord_70536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70536).length < 2 ^ (prefixWord ++ tailWord_70536).sum := by decide
  have hdescent : baseEnd_70536 < baseStart_70536 := by decide
  rcases family_descends (prefixWord ++ tailWord_70536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70609 : List Nat := [1, 2, 2, 1, 2, 1, 4, 8]
def baseStart_70609 : Nat := 118140960795 + 70609 * 2 ^ 59
def prefixEnd_70609 : Nat := 4983230072969 + 3 ^ 40 * 70609 * 2
def baseEnd_70609 : Nat := 5371311930876959357449

theorem tailTrace_70609 : CollatzResearch.WordTrace tailWord_70609 prefixEnd_70609 5371311930876959357449 := by
  unfold tailWord_70609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575321801203126902238881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1716881200802084601492587 2575321801203126902238881)
  ·
    refine ⟨1931491350902345176679161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2575321801203126902238881 1931491350902345176679161)
    ·
      refine ⟨1448618513176758882509371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1931491350902345176679161 1448618513176758882509371)
      ·
        refine ⟨2172927769765138323764057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448618513176758882509371 2172927769765138323764057)
        ·
          refine ⟨1629695827323853742823043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172927769765138323764057 1629695827323853742823043)
          ·
            refine ⟨2444543740985780614234565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629695827323853742823043 2444543740985780614234565)
            ·
              refine ⟨458351951434833865168981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2444543740985780614234565 458351951434833865168981)
              ·
                refine ⟨5371311930876959357449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 458351951434833865168981 5371311930876959357449)
                ·
                  rfl

theorem cell21_70609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_70609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70609 prefixEnd_70609 := by exact prefixLift 70609
  have htrace : WordTrace (prefixWord ++ tailWord_70609) baseStart_70609 baseEnd_70609 := by
    simpa [prefixWord, tailWord_70609, baseEnd_70609] using wordTrace_append hprefix tailTrace_70609
  have hstable : (prefixWord ++ tailWord_70609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70609).length < 2 ^ (prefixWord ++ tailWord_70609).sum := by decide
  have hdescent : baseEnd_70609 < baseStart_70609 := by decide
  rcases family_descends (prefixWord ++ tailWord_70609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70657 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_70657 : Nat := 118140960795 + 70657 * 2 ^ 59
def prefixEnd_70657 : Nat := 4983230072969 + 3 ^ 40 * 70657 * 2
def baseEnd_70657 : Nat := 16124890046593461272249

theorem tailTrace_70657 : CollatzResearch.WordTrace tailWord_70657 prefixEnd_70657 16124890046593461272249 := by
  unfold tailWord_70657
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577072505029231099986225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1718048336686154066657483 2577072505029231099986225)
  ·
    refine ⟨1932804378771923324989669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2577072505029231099986225 1932804378771923324989669)
    ·
      refine ⟨362400821019735623435563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1932804378771923324989669 362400821019735623435563)
      ·
        refine ⟨543601231529603435153345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362400821019735623435563 543601231529603435153345)
        ·
          refine ⟨407700923647202576365009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543601231529603435153345 407700923647202576365009)
          ·
            refine ⟨305775692735401932273757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407700923647202576365009 305775692735401932273757)
            ·
              refine ⟨114665884775775724602659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305775692735401932273757 114665884775775724602659)
              ·
                refine ⟨171998827163663586903989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114665884775775724602659 171998827163663586903989)
                ·
                  refine ⟨16124890046593461272249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171998827163663586903989 16124890046593461272249)
                  ·
                    rfl

theorem cell21_70657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_70657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70657 prefixEnd_70657 := by exact prefixLift 70657
  have htrace : WordTrace (prefixWord ++ tailWord_70657) baseStart_70657 baseEnd_70657 := by
    simpa [prefixWord, tailWord_70657, baseEnd_70657] using wordTrace_append hprefix tailTrace_70657
  have hstable : (prefixWord ++ tailWord_70657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70657).length < 2 ^ (prefixWord ++ tailWord_70657).sum := by decide
  have hdescent : baseEnd_70657 < baseStart_70657 := by decide
  rcases family_descends (prefixWord ++ tailWord_70657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70708 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_70708 : Nat := 118140960795 + 70708 * 2 ^ 59
def prefixEnd_70708 : Nat := 4983230072969 + 3 ^ 40 * 70708 * 2
def baseEnd_70708 : Nat := 16136528941428705922145

theorem tailTrace_70708 : CollatzResearch.WordTrace tailWord_70708 prefixEnd_70708 16136528941428705922145 := by
  unfold tailWord_70708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289466313922233405046389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1719288418562977873395185 1289466313922233405046389)
  ·
    refine ⟨120887466930209381723099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1289466313922233405046389 120887466930209381723099)
    ·
      refine ⟨181331200395314072584649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120887466930209381723099 181331200395314072584649)
      ·
        refine ⟨135998400296485554438487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181331200395314072584649 135998400296485554438487)
        ·
          refine ⟨203997600444728331657731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135998400296485554438487 203997600444728331657731)
          ·
            refine ⟨305996400667092497486597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203997600444728331657731 305996400667092497486597)
            ·
              refine ⟨57374325125079843278737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305996400667092497486597 57374325125079843278737)
              ·
                refine ⟨43030743843809882459053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57374325125079843278737 43030743843809882459053)
                ·
                  refine ⟨16136528941428705922145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43030743843809882459053 16136528941428705922145)
                  ·
                    rfl

theorem cell21_70708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_70708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70708 prefixEnd_70708 := by exact prefixLift 70708
  have htrace : WordTrace (prefixWord ++ tailWord_70708) baseStart_70708 baseEnd_70708 := by
    simpa [prefixWord, tailWord_70708, baseEnd_70708] using wordTrace_append hprefix tailTrace_70708
  have hstable : (prefixWord ++ tailWord_70708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70708).length < 2 ^ (prefixWord ++ tailWord_70708).sum := by decide
  have hdescent : baseEnd_70708 < baseStart_70708 := by decide
  rcases family_descends (prefixWord ++ tailWord_70708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70733 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_70733 : Nat := 118140960795 + 70733 * 2 ^ 59
def prefixEnd_70733 : Nat := 4983230072969 + 3 ^ 40 * 70733 * 2
def baseEnd_70733 : Nat := 16142234282034218005427

theorem tailTrace_70733 : CollatzResearch.WordTrace tailWord_70733 prefixEnd_70733 16142234282034218005427 := by
  unfold tailWord_70733
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579844452753896079752853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1719896301835930719835235 2579844452753896079752853)
  ·
    refine ⟨120930208722838878738415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2579844452753896079752853 120930208722838878738415)
    ·
      refine ⟨181395313084258318107623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120930208722838878738415 181395313084258318107623)
      ·
        refine ⟨272092969626387477161435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181395313084258318107623 272092969626387477161435)
        ·
          refine ⟨408139454439581215742153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272092969626387477161435 408139454439581215742153)
          ·
            refine ⟨306104590829685911806615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408139454439581215742153 306104590829685911806615)
            ·
              refine ⟨459156886244528867709923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306104590829685911806615 459156886244528867709923)
              ·
                refine ⟨688735329366793301564885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459156886244528867709923 688735329366793301564885)
                ·
                  refine ⟨16142234282034218005427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 688735329366793301564885 16142234282034218005427)
                  ·
                    rfl

theorem cell21_70733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_70733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70733 prefixEnd_70733 := by exact prefixLift 70733
  have htrace : WordTrace (prefixWord ++ tailWord_70733) baseStart_70733 baseEnd_70733 := by
    simpa [prefixWord, tailWord_70733, baseEnd_70733] using wordTrace_append hprefix tailTrace_70733
  have hstable : (prefixWord ++ tailWord_70733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70733).length < 2 ^ (prefixWord ++ tailWord_70733).sum := by decide
  have hdescent : baseEnd_70733 < baseStart_70733 := by decide
  rcases family_descends (prefixWord ++ tailWord_70733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70761 : List Nat := [1, 2, 1, 1, 1, 7, 8]
def baseStart_70761 : Nat := 118140960795 + 70761 * 2 ^ 59
def prefixEnd_70761 : Nat := 4983230072969 + 3 ^ 40 * 70761 * 2
def baseEnd_70761 : Nat := 1794291584834710170967

theorem tailTrace_70761 : CollatzResearch.WordTrace tailWord_70761 prefixEnd_70761 1794291584834710170967 := by
  unfold tailWord_70761
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580865696652456861772137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1720577131101637907848091 2580865696652456861772137)
  ·
    refine ⟨1935649272489342646329103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2580865696652456861772137 1935649272489342646329103)
    ·
      refine ⟨2903473908734013969493655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935649272489342646329103 2903473908734013969493655)
      ·
        refine ⟨4355210863101020954240483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903473908734013969493655 4355210863101020954240483)
        ·
          refine ⟨6532816294651531431360725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355210863101020954240483 6532816294651531431360725)
          ·
            refine ⟨153112881905895267922517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6532816294651531431360725 153112881905895267922517)
            ·
              refine ⟨1794291584834710170967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 153112881905895267922517 1794291584834710170967)
              ·
                rfl

theorem cell21_70761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 8].length) (baseStart_70761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70761 prefixEnd_70761 := by exact prefixLift 70761
  have htrace : WordTrace (prefixWord ++ tailWord_70761) baseStart_70761 baseEnd_70761 := by
    simpa [prefixWord, tailWord_70761, baseEnd_70761] using wordTrace_append hprefix tailTrace_70761
  have hstable : (prefixWord ++ tailWord_70761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70761).length < 2 ^ (prefixWord ++ tailWord_70761).sum := by decide
  have hdescent : baseEnd_70761 < baseStart_70761 := by decide
  rcases family_descends (prefixWord ++ tailWord_70761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70826 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_70826 : Nat := 118140960795 + 70826 * 2 ^ 59
def prefixEnd_70826 : Nat := 4983230072969 + 3 ^ 40 * 70826 * 2
def baseEnd_70826 : Nat := 16163458149086722955237

theorem tailTrace_70826 : CollatzResearch.WordTrace tailWord_70826 prefixEnd_70826 16163458149086722955237 := by
  unfold tailWord_70826
  simp only [CollatzResearch.WordTrace]
  refine ⟨645809110354243240722083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1722157627611315308592221 645809110354243240722083)
  ·
    refine ⟨968713665531364861083125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 645809110354243240722083 968713665531364861083125)
    ·
      refine ⟨90816906143565455726543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 968713665531364861083125 90816906143565455726543)
      ·
        refine ⟨136225359215348183589815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90816906143565455726543 136225359215348183589815)
        ·
          refine ⟨204338038823022275384723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136225359215348183589815 204338038823022275384723)
          ·
            refine ⟨306507058234533413077085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204338038823022275384723 306507058234533413077085)
            ·
              refine ⟨114940146837950029903907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306507058234533413077085 114940146837950029903907)
              ·
                refine ⟨172410220256925044855861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114940146837950029903907 172410220256925044855861)
                ·
                  refine ⟨16163458149086722955237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172410220256925044855861 16163458149086722955237)
                  ·
                    rfl

theorem cell21_70826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_70826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70826 prefixEnd_70826 := by exact prefixLift 70826
  have htrace : WordTrace (prefixWord ++ tailWord_70826) baseStart_70826 baseEnd_70826 := by
    simpa [prefixWord, tailWord_70826, baseEnd_70826] using wordTrace_append hprefix tailTrace_70826
  have hstable : (prefixWord ++ tailWord_70826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70826).length < 2 ^ (prefixWord ++ tailWord_70826).sum := by decide
  have hdescent : baseEnd_70826 < baseStart_70826 := by decide
  rcases family_descends (prefixWord ++ tailWord_70826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70877 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 3]
def baseStart_70877 : Nat := 118140960795 + 70877 * 2 ^ 59
def prefixEnd_70877 : Nat := 4983230072969 + 3 ^ 40 * 70877 * 2
def baseEnd_70877 : Nat := 16175097043921967605133

theorem tailTrace_70877 : CollatzResearch.WordTrace tailWord_70877 prefixEnd_70877 16175097043921967605133 := by
  unfold tailWord_70877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585096564232208672994885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1723397709488139115329923 2585096564232208672994885)
  ·
    refine ⟨484705605793539126186541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2585096564232208672994885 484705605793539126186541)
    ·
      refine ⟨181764602172577172319953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 484705605793539126186541 181764602172577172319953)
      ·
        refine ⟨136323451629432879239965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181764602172577172319953 136323451629432879239965)
        ·
          refine ⟨51121294361037329714987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136323451629432879239965 51121294361037329714987)
          ·
            refine ⟨76681941541555994572481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51121294361037329714987 76681941541555994572481)
            ·
              refine ⟨57511456156166995929361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76681941541555994572481 57511456156166995929361)
              ·
                refine ⟨43133592117125246947021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57511456156166995929361 43133592117125246947021)
                ·
                  refine ⟨16175097043921967605133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43133592117125246947021 16175097043921967605133)
                  ·
                    rfl

theorem cell21_70877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_70877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70877 prefixEnd_70877 := by exact prefixLift 70877
  have htrace : WordTrace (prefixWord ++ tailWord_70877) baseStart_70877 baseEnd_70877 := by
    simpa [prefixWord, tailWord_70877, baseEnd_70877] using wordTrace_append hprefix tailTrace_70877
  have hstable : (prefixWord ++ tailWord_70877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70877).length < 2 ^ (prefixWord ++ tailWord_70877).sum := by decide
  have hdescent : baseEnd_70877 < baseStart_70877 := by decide
  rcases family_descends (prefixWord ++ tailWord_70877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70899 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_70899 : Nat := 118140960795 + 70899 * 2 ^ 59
def prefixEnd_70899 : Nat := 4983230072969 + 3 ^ 40 * 70899 * 2
def baseEnd_70899 : Nat := 16180117743654818238421

theorem tailTrace_70899 : CollatzResearch.WordTrace tailWord_70899 prefixEnd_70899 16180117743654818238421 := by
  unfold tailWord_70899
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585898970152506430295751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1723932646768337620197167 2585898970152506430295751)
  ·
    refine ⟨3878848455228759645443627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2585898970152506430295751 3878848455228759645443627)
    ·
      refine ⟨5818272682843139468165441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3878848455228759645443627 5818272682843139468165441)
      ·
        refine ⟨4363704512132354601124081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5818272682843139468165441 4363704512132354601124081)
        ·
          refine ⟨3272778384099265950843061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363704512132354601124081 3272778384099265950843061)
          ·
            refine ⟨306822973509306182891537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3272778384099265950843061 306822973509306182891537)
            ·
              refine ⟨230117230131979637168653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306822973509306182891537 230117230131979637168653)
              ·
                refine ⟨86293961299492363938245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 230117230131979637168653 86293961299492363938245)
                ·
                  refine ⟨16180117743654818238421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86293961299492363938245 16180117743654818238421)
                  ·
                    rfl

theorem cell21_70899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_70899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_70899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_70899 prefixEnd_70899 := by exact prefixLift 70899
  have htrace : WordTrace (prefixWord ++ tailWord_70899) baseStart_70899 baseEnd_70899 := by
    simpa [prefixWord, tailWord_70899, baseEnd_70899] using wordTrace_append hprefix tailTrace_70899
  have hstable : (prefixWord ++ tailWord_70899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70899).length < 2 ^ (prefixWord ++ tailWord_70899).sum := by decide
  have hdescent : baseEnd_70899 < baseStart_70899 := by decide
  rcases family_descends (prefixWord ++ tailWord_70899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71037 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 3]
def baseStart_71037 : Nat := 118140960795 + 71037 * 2 ^ 59
def prefixEnd_71037 : Nat := 4983230072969 + 3 ^ 40 * 71037 * 2
def baseEnd_71037 : Nat := 16211611223797244938139

theorem tailTrace_71037 : CollatzResearch.WordTrace tailWord_71037 prefixEnd_71037 16211611223797244938139 := by
  unfold tailWord_71037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590932243652555998819365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1727288162435037332546243 2590932243652555998819365)
  ·
    refine ⟨485799795684854249778631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2590932243652555998819365 485799795684854249778631)
    ·
      refine ⟨728699693527281374667947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485799795684854249778631 728699693527281374667947)
      ·
        refine ⟨1093049540290922062001921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728699693527281374667947 1093049540290922062001921)
        ·
          refine ⟨819787155218191546501441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093049540290922062001921 819787155218191546501441)
          ·
            refine ⟨614840366413643659876081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819787155218191546501441 614840366413643659876081)
            ·
              refine ⟨461130274810232744907061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614840366413643659876081 461130274810232744907061)
              ·
                refine ⟨43230963263459319835037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461130274810232744907061 43230963263459319835037)
                ·
                  refine ⟨16211611223797244938139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43230963263459319835037 16211611223797244938139)
                  ·
                    rfl

theorem cell21_71037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_71037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71037 prefixEnd_71037 := by exact prefixLift 71037
  have htrace : WordTrace (prefixWord ++ tailWord_71037) baseStart_71037 baseEnd_71037 := by
    simpa [prefixWord, tailWord_71037, baseEnd_71037] using wordTrace_append hprefix tailTrace_71037
  have hstable : (prefixWord ++ tailWord_71037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71037).length < 2 ^ (prefixWord ++ tailWord_71037).sum := by decide
  have hdescent : baseEnd_71037 < baseStart_71037 := by decide
  rcases family_descends (prefixWord ++ tailWord_71037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71051 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_71051 : Nat := 118140960795 + 71051 * 2 ^ 59
def prefixEnd_71051 : Nat := 4983230072969 + 3 ^ 40 * 71051 * 2
def baseEnd_71051 : Nat := 16214806214536331704777

theorem tailTrace_71051 : CollatzResearch.WordTrace tailWord_71051 prefixEnd_71051 16214806214536331704777 := by
  unfold tailWord_71051
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591442865601836389829007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1727628577067890926552671 2591442865601836389829007)
  ·
    refine ⟨3887164298402754584743511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591442865601836389829007 3887164298402754584743511)
    ·
      refine ⟨5830746447604131877115267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3887164298402754584743511 5830746447604131877115267)
      ·
        refine ⟨8746119671406197815672901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830746447604131877115267 8746119671406197815672901)
        ·
          refine ⟨1639897438388662090438669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8746119671406197815672901 1639897438388662090438669)
          ·
            refine ⟨614961539395748283914501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1639897438388662090438669 614961539395748283914501)
            ·
              refine ⟨115305288636702803233969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 614961539395748283914501 115305288636702803233969)
              ·
                refine ⟨86478966477527102425477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115305288636702803233969 86478966477527102425477)
                ·
                  refine ⟨16214806214536331704777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86478966477527102425477 16214806214536331704777)
                  ·
                    rfl

theorem cell21_71051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_71051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71051 prefixEnd_71051 := by exact prefixLift 71051
  have htrace : WordTrace (prefixWord ++ tailWord_71051) baseStart_71051 baseEnd_71051 := by
    simpa [prefixWord, tailWord_71051, baseEnd_71051] using wordTrace_append hprefix tailTrace_71051
  have hstable : (prefixWord ++ tailWord_71051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71051).length < 2 ^ (prefixWord ++ tailWord_71051).sum := by decide
  have hdescent : baseEnd_71051 < baseStart_71051 := by decide
  rcases family_descends (prefixWord ++ tailWord_71051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71065 : List Nat := [1, 2, 1, 2, 1, 5, 3, 6]
def baseStart_71065 : Nat := 118140960795 + 71065 * 2 ^ 59
def prefixEnd_71065 : Nat := 4983230072969 + 3 ^ 40 * 71065 * 2
def baseEnd_71065 : Nat := 5406000401758472823805

theorem tailTrace_71065 : CollatzResearch.WordTrace tailWord_71065 prefixEnd_71065 5406000401758472823805 := by
  unfold tailWord_71065
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591953487551116780838649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1727968991700744520559099 2591953487551116780838649)
  ·
    refine ⟨1943965115663337585628987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2591953487551116780838649 1943965115663337585628987)
    ·
      refine ⟨2915947673495006378443481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943965115663337585628987 2915947673495006378443481)
      ·
        refine ⟨2186960755121254783832611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2915947673495006378443481 2186960755121254783832611)
        ·
          refine ⟨3280441132681882175748917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186960755121254783832611 3280441132681882175748917)
          ·
            refine ⟨307541356188926453976461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3280441132681882175748917 307541356188926453976461)
            ·
              refine ⟨115328008570847420241173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307541356188926453976461 115328008570847420241173)
              ·
                refine ⟨5406000401758472823805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115328008570847420241173 5406000401758472823805)
                ·
                  rfl

theorem cell21_71065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_71065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71065 prefixEnd_71065 := by exact prefixLift 71065
  have htrace : WordTrace (prefixWord ++ tailWord_71065) baseStart_71065 baseEnd_71065 := by
    simpa [prefixWord, tailWord_71065, baseEnd_71065] using wordTrace_append hprefix tailTrace_71065
  have hstable : (prefixWord ++ tailWord_71065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71065).length < 2 ^ (prefixWord ++ tailWord_71065).sum := by decide
  have hdescent : baseEnd_71065 < baseStart_71065 := by decide
  rcases family_descends (prefixWord ++ tailWord_71065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71158 : List Nat := [5, 1, 1, 1, 2, 4, 7]
def baseStart_71158 : Nat := 118140960795 + 71158 * 2 ^ 59
def prefixEnd_71158 : Nat := 4983230072969 + 3 ^ 40 * 71158 * 2
def baseEnd_71158 : Nat := 1804358341369769269025

theorem tailTrace_71158 : CollatzResearch.WordTrace tailWord_71158 prefixEnd_71158 1804358341369769269025 := by
  unfold tailWord_71158
  simp only [CollatzResearch.WordTrace]
  refine ⟨162209092263387103998383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1730230317476129109316085 162209092263387103998383)
  ·
    refine ⟨243313638395080655997575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162209092263387103998383 243313638395080655997575)
    ·
      refine ⟨364970457592620983996363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243313638395080655997575 364970457592620983996363)
      ·
        refine ⟨547455686388931475994545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364970457592620983996363 547455686388931475994545)
        ·
          refine ⟨410591764791698606995909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547455686388931475994545 410591764791698606995909)
          ·
            refine ⟨76985955898443488811733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 410591764791698606995909 76985955898443488811733)
            ·
              refine ⟨1804358341369769269025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76985955898443488811733 1804358341369769269025)
              ·
                rfl

theorem cell21_71158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 7].length) (baseStart_71158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71158 prefixEnd_71158 := by exact prefixLift 71158
  have htrace : WordTrace (prefixWord ++ tailWord_71158) baseStart_71158 baseEnd_71158 := by
    simpa [prefixWord, tailWord_71158, baseEnd_71158] using wordTrace_append hprefix tailTrace_71158
  have hstable : (prefixWord ++ tailWord_71158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71158).length < 2 ^ (prefixWord ++ tailWord_71158).sum := by decide
  have hdescent : baseEnd_71158 < baseStart_71158 := by decide
  rcases family_descends (prefixWord ++ tailWord_71158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71265 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 3]
def baseStart_71265 : Nat := 118140960795 + 71265 * 2 ^ 59
def prefixEnd_71265 : Nat := 4983230072969 + 3 ^ 40 * 71265 * 2
def baseEnd_71265 : Nat := 16263643930119515137673

theorem tailTrace_71265 : CollatzResearch.WordTrace tailWord_71265 prefixEnd_71265 16263643930119515137673 := by
  unfold tailWord_71265
  simp only [CollatzResearch.WordTrace]
  refine ⟨2599248086826550938119249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1732832057884367292079499 2599248086826550938119249)
  ·
    refine ⟨1949436065119913203589437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2599248086826550938119249 1949436065119913203589437)
    ·
      refine ⟨731038524419967451346039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1949436065119913203589437 731038524419967451346039)
      ·
        refine ⟨1096557786629951177019059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 731038524419967451346039 1096557786629951177019059)
        ·
          refine ⟨1644836679944926765528589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096557786629951177019059 1644836679944926765528589)
          ·
            refine ⟨616813754979347537073221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1644836679944926765528589 616813754979347537073221)
            ·
              refine ⟨115652579058627663201229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 616813754979347537073221 115652579058627663201229)
              ·
                refine ⟨43369717146985373700461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115652579058627663201229 43369717146985373700461)
                ·
                  refine ⟨16263643930119515137673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43369717146985373700461 16263643930119515137673)
                  ·
                    rfl

theorem cell21_71265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_71265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71265 prefixEnd_71265 := by exact prefixLift 71265
  have htrace : WordTrace (prefixWord ++ tailWord_71265) baseStart_71265 baseEnd_71265 := by
    simpa [prefixWord, tailWord_71265, baseEnd_71265] using wordTrace_append hprefix tailTrace_71265
  have hstable : (prefixWord ++ tailWord_71265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71265).length < 2 ^ (prefixWord ++ tailWord_71265).sum := by decide
  have hdescent : baseEnd_71265 < baseStart_71265 := by decide
  rcases family_descends (prefixWord ++ tailWord_71265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71307 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_71307 : Nat := 118140960795 + 71307 * 2 ^ 59
def prefixEnd_71307 : Nat := 4983230072969 + 3 ^ 40 * 71307 * 2
def baseEnd_71307 : Nat := 16273228902336775437587

theorem tailTrace_71307 : CollatzResearch.WordTrace tailWord_71307 prefixEnd_71307 16273228902336775437587 := by
  unfold tailWord_71307
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600779952674392111148175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1733853301782928074098783 2600779952674392111148175)
  ·
    refine ⟨3901169929011588166722263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600779952674392111148175 3901169929011588166722263)
    ·
      refine ⟨5851754893517382250083395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901169929011588166722263 5851754893517382250083395)
      ·
        refine ⟨8777632340276073375125093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5851754893517382250083395 8777632340276073375125093)
        ·
          refine ⟨1645806063801763757835955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8777632340276073375125093 1645806063801763757835955)
          ·
            refine ⟨2468709095702645636753933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645806063801763757835955 2468709095702645636753933)
            ·
              refine ⟨925765910888492113782725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2468709095702645636753933 925765910888492113782725)
              ·
                refine ⟨173581108291592271334261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 925765910888492113782725 173581108291592271334261)
                ·
                  refine ⟨16273228902336775437587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173581108291592271334261 16273228902336775437587)
                  ·
                    rfl

theorem cell21_71307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_71307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71307 prefixEnd_71307 := by exact prefixLift 71307
  have htrace : WordTrace (prefixWord ++ tailWord_71307) baseStart_71307 baseEnd_71307 := by
    simpa [prefixWord, tailWord_71307, baseEnd_71307] using wordTrace_append hprefix tailTrace_71307
  have hstable : (prefixWord ++ tailWord_71307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71307).length < 2 ^ (prefixWord ++ tailWord_71307).sum := by decide
  have hdescent : baseEnd_71307 < baseStart_71307 := by decide
  rcases family_descends (prefixWord ++ tailWord_71307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71310 : List Nat := [4, 1, 1, 3, 1, 2, 4, 5]
def baseStart_71310 : Nat := 118140960795 + 71310 * 2 ^ 59
def prefixEnd_71310 : Nat := 4983230072969 + 3 ^ 40 * 71310 * 2
def baseEnd_71310 : Nat := 5424637847736478962527

theorem tailTrace_71310 : CollatzResearch.WordTrace tailWord_71310 prefixEnd_71310 5424637847736478962527 := by
  unfold tailWord_71310
  simp only [CollatzResearch.WordTrace]
  refine ⟨325111171457940452938423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1733926247775682415671589 325111171457940452938423)
  ·
    refine ⟨487666757186910679407635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 325111171457940452938423 487666757186910679407635)
    ·
      refine ⟨731500135780366019111453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487666757186910679407635 731500135780366019111453)
      ·
        refine ⟨274312550917637257166795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 731500135780366019111453 274312550917637257166795)
        ·
          refine ⟨411468826376455885750193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274312550917637257166795 411468826376455885750193)
          ·
            refine ⟨308601619782341914312645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411468826376455885750193 308601619782341914312645)
            ·
              refine ⟨57862803709189108933621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 308601619782341914312645 57862803709189108933621)
              ·
                refine ⟨5424637847736478962527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57862803709189108933621 5424637847736478962527)
                ·
                  rfl

theorem cell21_71310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_71310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71310 prefixEnd_71310 := by exact prefixLift 71310
  have htrace : WordTrace (prefixWord ++ tailWord_71310) baseStart_71310 baseEnd_71310 := by
    simpa [prefixWord, tailWord_71310, baseEnd_71310] using wordTrace_append hprefix tailTrace_71310
  have hstable : (prefixWord ++ tailWord_71310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71310).length < 2 ^ (prefixWord ++ tailWord_71310).sum := by decide
  have hdescent : baseEnd_71310 < baseStart_71310 := by decide
  rcases family_descends (prefixWord ++ tailWord_71310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71316 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_71316 : Nat := 118140960795 + 71316 * 2 ^ 59
def prefixEnd_71316 : Nat := 4983230072969 + 3 ^ 40 * 71316 * 2
def baseEnd_71316 : Nat := 16275282824954759787569

theorem tailTrace_71316 : CollatzResearch.WordTrace tailWord_71316 prefixEnd_71316 16275282824954759787569 := by
  unfold tailWord_71316
  simp only [CollatzResearch.WordTrace]
  refine ⟨1300554104820893324112901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1734072139761191098817201 1300554104820893324112901)
  ·
    refine ⟨243853894653917498271169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1300554104820893324112901 243853894653917498271169)
    ·
      refine ⟨182890420990438123703377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243853894653917498271169 182890420990438123703377)
      ·
        refine ⟨137167815742828592777533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182890420990438123703377 137167815742828592777533)
        ·
          refine ⟨51437930903560722291575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137167815742828592777533 51437930903560722291575)
          ·
            refine ⟨77156896355341083437363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51437930903560722291575 77156896355341083437363)
            ·
              refine ⟨115735344533011625156045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77156896355341083437363 115735344533011625156045)
              ·
                refine ⟨43400754199879359433517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115735344533011625156045 43400754199879359433517)
                ·
                  refine ⟨16275282824954759787569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43400754199879359433517 16275282824954759787569)
                  ·
                    rfl

theorem cell21_71316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_71316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71316 prefixEnd_71316 := by exact prefixLift 71316
  have htrace : WordTrace (prefixWord ++ tailWord_71316) baseStart_71316 baseEnd_71316 := by
    simpa [prefixWord, tailWord_71316, baseEnd_71316] using wordTrace_append hprefix tailTrace_71316
  have hstable : (prefixWord ++ tailWord_71316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71316).length < 2 ^ (prefixWord ++ tailWord_71316).sum := by decide
  have hdescent : baseEnd_71316 < baseStart_71316 := by decide
  rcases family_descends (prefixWord ++ tailWord_71316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71327 : List Nat := [1, 1, 2, 7, 2, 1, 7]
def baseStart_71327 : Nat := 118140960795 + 71327 * 2 ^ 59
def prefixEnd_71327 : Nat := 4983230072969 + 3 ^ 40 * 71327 * 2
def baseEnd_71327 : Nat := 1808643686091242789357

theorem tailTrace_71327 : CollatzResearch.WordTrace tailWord_71327 prefixEnd_71327 1808643686091242789357 := by
  unfold tailWord_71327
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601509412601935526876235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1734339608401290351250823 2601509412601935526876235)
  ·
    refine ⟨3902264118902903290314353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2601509412601935526876235 3902264118902903290314353)
    ·
      refine ⟨2926698089177177467735765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3902264118902903290314353 2926698089177177467735765)
      ·
        refine ⟨68594486465090096900057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2926698089177177467735765 68594486465090096900057)
        ·
          refine ⟨51445864848817572675043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68594486465090096900057 51445864848817572675043)
          ·
            refine ⟨77168797273226359012565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51445864848817572675043 77168797273226359012565)
            ·
              refine ⟨1808643686091242789357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 77168797273226359012565 1808643686091242789357)
              ·
                rfl

theorem cell21_71327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 7].length) (baseStart_71327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71327 prefixEnd_71327 := by exact prefixLift 71327
  have htrace : WordTrace (prefixWord ++ tailWord_71327) baseStart_71327 baseEnd_71327 := by
    simpa [prefixWord, tailWord_71327, baseEnd_71327] using wordTrace_append hprefix tailTrace_71327
  have hstable : (prefixWord ++ tailWord_71327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71327).length < 2 ^ (prefixWord ++ tailWord_71327).sum := by decide
  have hdescent : baseEnd_71327 < baseStart_71327 := by decide
  rcases family_descends (prefixWord ++ tailWord_71327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71389 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 4]
def baseStart_71389 : Nat := 118140960795 + 71389 * 2 ^ 59
def prefixEnd_71389 : Nat := 4983230072969 + 3 ^ 40 * 71389 * 2
def baseEnd_71389 : Nat := 16291942419522855070753

theorem tailTrace_71389 : CollatzResearch.WordTrace tailWord_71389 prefixEnd_71389 16291942419522855070753 := by
  unfold tailWord_71389
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603770738377320115633221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1735847158918213410422147 2603770738377320115633221)
  ·
    refine ⟨488207013445747521681229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2603770738377320115633221 488207013445747521681229)
    ·
      refine ⟨183077630042155320630461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 488207013445747521681229 183077630042155320630461)
      ·
        refine ⟨68654111265808245236423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183077630042155320630461 68654111265808245236423)
        ·
          refine ⟨102981166898712367854635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68654111265808245236423 102981166898712367854635)
          ·
            refine ⟨154471750348068551781953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102981166898712367854635 154471750348068551781953)
            ·
              refine ⟨115853812761051413836465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154471750348068551781953 115853812761051413836465)
              ·
                refine ⟨86890359570788560377349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115853812761051413836465 86890359570788560377349)
                ·
                  refine ⟨16291942419522855070753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86890359570788560377349 16291942419522855070753)
                  ·
                    rfl

theorem cell21_71389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_71389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71389 prefixEnd_71389 := by exact prefixLift 71389
  have htrace : WordTrace (prefixWord ++ tailWord_71389) baseStart_71389 baseEnd_71389 := by
    simpa [prefixWord, tailWord_71389, baseEnd_71389] using wordTrace_append hprefix tailTrace_71389
  have hstable : (prefixWord ++ tailWord_71389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71389).length < 2 ^ (prefixWord ++ tailWord_71389).sum := by decide
  have hdescent : baseEnd_71389 < baseStart_71389 := by decide
  rcases family_descends (prefixWord ++ tailWord_71389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71459 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_71459 : Nat := 118140960795 + 71459 * 2 ^ 59
def prefixEnd_71459 : Nat := 4983230072969 + 3 ^ 40 * 71459 * 2
def baseEnd_71459 : Nat := 16307917373218288903943

theorem tailTrace_71459 : CollatzResearch.WordTrace tailWord_71459 prefixEnd_71459 16307917373218288903943 := by
  unfold tailWord_71459
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606323848123722070681431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1737549232082481380454287 2606323848123722070681431)
  ·
    refine ⟨3909485772185583106022147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2606323848123722070681431 3909485772185583106022147)
    ·
      refine ⟨5864228658278374659033221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909485772185583106022147 5864228658278374659033221)
      ·
        refine ⟨1099542873427195248568729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5864228658278374659033221 1099542873427195248568729)
        ·
          refine ⟨824657155070396436426547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099542873427195248568729 824657155070396436426547)
          ·
            refine ⟨1236985732605594654639821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824657155070396436426547 1236985732605594654639821)
            ·
              refine ⟨463869649727097995489933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236985732605594654639821 463869649727097995489933)
              ·
                refine ⟨173951118647661748308725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463869649727097995489933 173951118647661748308725)
                ·
                  refine ⟨16307917373218288903943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 173951118647661748308725 16307917373218288903943)
                  ·
                    rfl

theorem cell21_71459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_71459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71459 prefixEnd_71459 := by exact prefixLift 71459
  have htrace : WordTrace (prefixWord ++ tailWord_71459) baseStart_71459 baseEnd_71459 := by
    simpa [prefixWord, tailWord_71459, baseEnd_71459] using wordTrace_append hprefix tailTrace_71459
  have hstable : (prefixWord ++ tailWord_71459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71459).length < 2 ^ (prefixWord ++ tailWord_71459).sum := by decide
  have hdescent : baseEnd_71459 < baseStart_71459 := by decide
  rcases family_descends (prefixWord ++ tailWord_71459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71552 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_71552 : Nat := 118140960795 + 71552 * 2 ^ 59
def prefixEnd_71552 : Nat := 4983230072969 + 3 ^ 40 * 71552 * 2
def baseEnd_71552 : Nat := 16329141240270793853753

theorem tailTrace_71552 : CollatzResearch.WordTrace tailWord_71552 prefixEnd_71552 16329141240270793853753 := by
  unfold tailWord_71552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304857918393399476908455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1739810557857865969211273 1304857918393399476908455)
  ·
    refine ⟨1957286877590099215362683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1304857918393399476908455 1957286877590099215362683)
    ·
      refine ⟨2935930316385148823044025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957286877590099215362683 2935930316385148823044025)
      ·
        refine ⟨2201947737288861617283019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935930316385148823044025 2201947737288861617283019)
        ·
          refine ⟨3302921605933292425924529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201947737288861617283019 3302921605933292425924529)
          ·
            refine ⟨2477191204449969319443397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3302921605933292425924529 2477191204449969319443397)
            ·
              refine ⟨464473350834369247395637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2477191204449969319443397 464473350834369247395637)
              ·
                refine ⟨43544376640722116943341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464473350834369247395637 43544376640722116943341)
                ·
                  refine ⟨16329141240270793853753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43544376640722116943341 16329141240270793853753)
                  ·
                    rfl

theorem cell21_71552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_71552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71552 prefixEnd_71552 := by exact prefixLift 71552
  have htrace : WordTrace (prefixWord ++ tailWord_71552) baseStart_71552 baseEnd_71552 := by
    simpa [prefixWord, tailWord_71552, baseEnd_71552] using wordTrace_append hprefix tailTrace_71552
  have hstable : (prefixWord ++ tailWord_71552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71552).length < 2 ^ (prefixWord ++ tailWord_71552).sum := by decide
  have hdescent : baseEnd_71552 < baseStart_71552 := by decide
  rcases family_descends (prefixWord ++ tailWord_71552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71569 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 3]
def baseStart_71569 : Nat := 118140960795 + 71569 * 2 ^ 59
def prefixEnd_71569 : Nat := 4983230072969 + 3 ^ 40 * 71569 * 2
def baseEnd_71569 : Nat := 16333020871882542070385

theorem tailTrace_71569 : CollatzResearch.WordTrace tailWord_71569 prefixEnd_71569 16333020871882542070385 := by
  unfold tailWord_71569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610335877725210857185761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1740223918483473904790507 2610335877725210857185761)
  ·
    refine ⟨1957751908293908142889321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2610335877725210857185761 1957751908293908142889321)
    ·
      refine ⟨1468313931220431107166991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1957751908293908142889321 1468313931220431107166991)
      ·
        refine ⟨2202470896830646660750487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468313931220431107166991 2202470896830646660750487)
        ·
          refine ⟨3303706345245969991125731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202470896830646660750487 3303706345245969991125731)
          ·
            refine ⟨4955559517868954986688597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303706345245969991125731 4955559517868954986688597)
            ·
              refine ⟨58072963100026816250257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4955559517868954986688597 58072963100026816250257)
              ·
                refine ⟨43554722325020112187693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58072963100026816250257 43554722325020112187693)
                ·
                  refine ⟨16333020871882542070385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43554722325020112187693 16333020871882542070385)
                  ·
                    rfl

theorem cell21_71569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_71569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71569 prefixEnd_71569 := by exact prefixLift 71569
  have htrace : WordTrace (prefixWord ++ tailWord_71569) baseStart_71569 baseEnd_71569 := by
    simpa [prefixWord, tailWord_71569, baseEnd_71569] using wordTrace_append hprefix tailTrace_71569
  have hstable : (prefixWord ++ tailWord_71569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71569).length < 2 ^ (prefixWord ++ tailWord_71569).sum := by decide
  have hdescent : baseEnd_71569 < baseStart_71569 := by decide
  rcases family_descends (prefixWord ++ tailWord_71569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71625 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_71625 : Nat := 118140960795 + 71625 * 2 ^ 59
def prefixEnd_71625 : Nat := 4983230072969 + 3 ^ 40 * 71625 * 2
def baseEnd_71625 : Nat := 16345800834838889136937

theorem tailTrace_71625 : CollatzResearch.WordTrace tailWord_71625 prefixEnd_71625 16345800834838889136937 := by
  unfold tailWord_71625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612378365522332421224329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1741585577014888280816219 2612378365522332421224329)
  ·
    refine ⟨1959283774141749315918247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2612378365522332421224329 1959283774141749315918247)
    ·
      refine ⟨2938925661212623973877371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959283774141749315918247 2938925661212623973877371)
      ·
        refine ⟨4408388491818935960816057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938925661212623973877371 4408388491818935960816057)
        ·
          refine ⟨3306291368864201970612043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4408388491818935960816057 3306291368864201970612043)
          ·
            refine ⟨4959437053296302955918065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306291368864201970612043 4959437053296302955918065)
            ·
              refine ⟨3719577789972227216938549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959437053296302955918065 3719577789972227216938549)
              ·
                refine ⟨348710417809896301587989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3719577789972227216938549 348710417809896301587989)
                ·
                  refine ⟨16345800834838889136937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 348710417809896301587989 16345800834838889136937)
                  ·
                    rfl

theorem cell21_71625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_71625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71625 prefixEnd_71625 := by exact prefixLift 71625
  have htrace : WordTrace (prefixWord ++ tailWord_71625) baseStart_71625 baseEnd_71625 := by
    simpa [prefixWord, tailWord_71625, baseEnd_71625] using wordTrace_append hprefix tailTrace_71625
  have hstable : (prefixWord ++ tailWord_71625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71625).length < 2 ^ (prefixWord ++ tailWord_71625).sum := by decide
  have hdescent : baseEnd_71625 < baseStart_71625 := by decide
  rcases family_descends (prefixWord ++ tailWord_71625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71628 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_71628 : Nat := 118140960795 + 71628 * 2 ^ 59
def prefixEnd_71628 : Nat := 4983230072969 + 3 ^ 40 * 71628 * 2
def baseEnd_71628 : Nat := 16346485475711550586931

theorem tailTrace_71628 : CollatzResearch.WordTrace tailWord_71628 prefixEnd_71628 16346485475711550586931 := by
  unfold tailWord_71628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306243892255731966791769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1741658523007642622389025 1306243892255731966791769)
  ·
    refine ⟨979682919191798975093827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1306243892255731966791769 979682919191798975093827)
    ·
      refine ⟨1469524378787698462640741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979682919191798975093827 1469524378787698462640741)
      ·
        refine ⟨275535821022693461745139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1469524378787698462640741 275535821022693461745139)
        ·
          refine ⟨413303731534040192617709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275535821022693461745139 413303731534040192617709)
          ·
            refine ⟨154988899325265072231641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413303731534040192617709 154988899325265072231641)
            ·
              refine ⟨116241674493948804173731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154988899325265072231641 116241674493948804173731)
              ·
                refine ⟨174362511740923206260597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116241674493948804173731 174362511740923206260597)
                ·
                  refine ⟨16346485475711550586931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 174362511740923206260597 16346485475711550586931)
                  ·
                    rfl

theorem cell21_71628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_71628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71628 prefixEnd_71628 := by exact prefixLift 71628
  have htrace : WordTrace (prefixWord ++ tailWord_71628) baseStart_71628 baseEnd_71628 := by
    simpa [prefixWord, tailWord_71628, baseEnd_71628] using wordTrace_append hprefix tailTrace_71628
  have hstable : (prefixWord ++ tailWord_71628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71628).length < 2 ^ (prefixWord ++ tailWord_71628).sum := by decide
  have hdescent : baseEnd_71628 < baseStart_71628 := by decide
  rcases family_descends (prefixWord ++ tailWord_71628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71662 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_71662 : Nat := 118140960795 + 71662 * 2 ^ 59
def prefixEnd_71662 : Nat := 4983230072969 + 3 ^ 40 * 71662 * 2
def baseEnd_71662 : Nat := 16354244738935047020195

theorem tailTrace_71662 : CollatzResearch.WordTrace tailWord_71662 prefixEnd_71662 16354244738935047020195 := by
  unfold tailWord_71662
  simp only [CollatzResearch.WordTrace]
  refine ⟨326715983298535967540155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1742485244258858493547493 326715983298535967540155)
  ·
    refine ⟨490073974947803951310233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326715983298535967540155 490073974947803951310233)
    ·
      refine ⟨367555481210852963482675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 490073974947803951310233 367555481210852963482675)
      ·
        refine ⟨551333221816279445224013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367555481210852963482675 551333221816279445224013)
        ·
          refine ⟨206749958181104791959005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 551333221816279445224013 206749958181104791959005)
          ·
            refine ⟨77531234317914296984627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206749958181104791959005 77531234317914296984627)
            ·
              refine ⟨116296851476871445476941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77531234317914296984627 116296851476871445476941)
              ·
                refine ⟨43611319303826792053853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116296851476871445476941 43611319303826792053853)
                ·
                  refine ⟨16354244738935047020195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43611319303826792053853 16354244738935047020195)
                  ·
                    rfl

theorem cell21_71662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_71662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71662 prefixEnd_71662 := by exact prefixLift 71662
  have htrace : WordTrace (prefixWord ++ tailWord_71662) baseStart_71662 baseEnd_71662 := by
    simpa [prefixWord, tailWord_71662, baseEnd_71662] using wordTrace_append hprefix tailTrace_71662
  have hstable : (prefixWord ++ tailWord_71662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71662).length < 2 ^ (prefixWord ++ tailWord_71662).sum := by decide
  have hdescent : baseEnd_71662 < baseStart_71662 := by decide
  rcases family_descends (prefixWord ++ tailWord_71662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71777 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_71777 : Nat := 118140960795 + 71777 * 2 ^ 59
def prefixEnd_71777 : Nat := 4983230072969 + 3 ^ 40 * 71777 * 2
def baseEnd_71777 : Nat := 16380489305720402603293

theorem tailTrace_71777 : CollatzResearch.WordTrace tailWord_71777 prefixEnd_71777 16380489305720402603293 := by
  unfold tailWord_71777
  simp only [CollatzResearch.WordTrace]
  refine ⟨2617922260971662380757585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1745281507314441587171723 2617922260971662380757585)
  ·
    refine ⟨1963441695728746785568189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2617922260971662380757585 1963441695728746785568189)
    ·
      refine ⟨736290635898280044588071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1963441695728746785568189 736290635898280044588071)
      ·
        refine ⟨1104435953847420066882107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736290635898280044588071 1104435953847420066882107)
        ·
          refine ⟨1656653930771130100323161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104435953847420066882107 1656653930771130100323161)
          ·
            refine ⟨1242490448078347575242371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1656653930771130100323161 1242490448078347575242371)
            ·
              refine ⟨1863735672117521362863557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242490448078347575242371 1863735672117521362863557)
              ·
                refine ⟨349450438522035255536917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1863735672117521362863557 349450438522035255536917)
                ·
                  refine ⟨16380489305720402603293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 349450438522035255536917 16380489305720402603293)
                  ·
                    rfl

theorem cell21_71777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_71777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71777 prefixEnd_71777 := by exact prefixLift 71777
  have htrace : WordTrace (prefixWord ++ tailWord_71777) baseStart_71777 baseEnd_71777 := by
    simpa [prefixWord, tailWord_71777, baseEnd_71777] using wordTrace_append hprefix tailTrace_71777
  have hstable : (prefixWord ++ tailWord_71777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71777).length < 2 ^ (prefixWord ++ tailWord_71777).sum := by decide
  have hdescent : baseEnd_71777 < baseStart_71777 := by decide
  rcases family_descends (prefixWord ++ tailWord_71777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71780 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_71780 : Nat := 118140960795 + 71780 * 2 ^ 59
def prefixEnd_71780 : Nat := 4983230072969 + 3 ^ 40 * 71780 * 2
def baseEnd_71780 : Nat := 16381173946593064053287

theorem tailTrace_71780 : CollatzResearch.WordTrace tailWord_71780 prefixEnd_71780 16381173946593064053287 := by
  unfold tailWord_71780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1309015839980396946558397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1745354453307195928744529 1309015839980396946558397)
  ·
    refine ⟨490880939992648854959399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1309015839980396946558397 490880939992648854959399)
    ·
      refine ⟨736321409988973282439099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490880939992648854959399 736321409988973282439099)
      ·
        refine ⟨1104482114983459923658649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736321409988973282439099 1104482114983459923658649)
        ·
          refine ⟨828361586237594942743987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104482114983459923658649 828361586237594942743987)
          ·
            refine ⟨1242542379356392414115981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828361586237594942743987 1242542379356392414115981)
            ·
              refine ⟨465953392258647155293493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1242542379356392414115981 465953392258647155293493)
              ·
                refine ⟨43683130524248170808765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 465953392258647155293493 43683130524248170808765)
                ·
                  refine ⟨16381173946593064053287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43683130524248170808765 16381173946593064053287)
                  ·
                    rfl

theorem cell21_71780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_71780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71780 prefixEnd_71780 := by exact prefixLift 71780
  have htrace : WordTrace (prefixWord ++ tailWord_71780) baseStart_71780 baseEnd_71780 := by
    simpa [prefixWord, tailWord_71780, baseEnd_71780] using wordTrace_append hprefix tailTrace_71780
  have hstable : (prefixWord ++ tailWord_71780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71780).length < 2 ^ (prefixWord ++ tailWord_71780).sum := by decide
  have hdescent : baseEnd_71780 < baseStart_71780 := by decide
  rcases family_descends (prefixWord ++ tailWord_71780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71794 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_71794 : Nat := 118140960795 + 71794 * 2 ^ 59
def prefixEnd_71794 : Nat := 4983230072969 + 3 ^ 40 * 71794 * 2
def baseEnd_71794 : Nat := 16384368937332150819925

theorem tailTrace_71794 : CollatzResearch.WordTrace tailWord_71794 prefixEnd_71794 16384368937332150819925 := by
  unfold tailWord_71794
  simp only [CollatzResearch.WordTrace]
  refine ⟨654635575477518571031609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1745694867940049522750957 654635575477518571031609)
  ·
    refine ⟨490976681608138928273707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 654635575477518571031609 490976681608138928273707)
    ·
      refine ⟨736465022412208392410561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490976681608138928273707 736465022412208392410561)
      ·
        refine ⟨552348766809156294307921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 736465022412208392410561 552348766809156294307921)
        ·
          refine ⟨414261575106867220730941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552348766809156294307921 414261575106867220730941)
          ·
            refine ⟨155348090665075207774103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 414261575106867220730941 155348090665075207774103)
            ·
              refine ⟨233022135997612811661155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155348090665075207774103 233022135997612811661155)
              ·
                refine ⟨349533203996419217491733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 233022135997612811661155 349533203996419217491733)
                ·
                  refine ⟨16384368937332150819925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 349533203996419217491733 16384368937332150819925)
                  ·
                    rfl

theorem cell21_71794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_71794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71794 prefixEnd_71794 := by exact prefixLift 71794
  have htrace : WordTrace (prefixWord ++ tailWord_71794) baseStart_71794 baseEnd_71794 := by
    simpa [prefixWord, tailWord_71794, baseEnd_71794] using wordTrace_append hprefix tailTrace_71794
  have hstable : (prefixWord ++ tailWord_71794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71794).length < 2 ^ (prefixWord ++ tailWord_71794).sum := by decide
  have hdescent : baseEnd_71794 < baseStart_71794 := by decide
  rcases family_descends (prefixWord ++ tailWord_71794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71811 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 4]
def baseStart_71811 : Nat := 118140960795 + 71811 * 2 ^ 59
def prefixEnd_71811 : Nat := 4983230072969 + 3 ^ 40 * 71811 * 2
def baseEnd_71811 : Nat := 16388248568943899036557

theorem tailTrace_71811 : CollatzResearch.WordTrace tailWord_71811 prefixEnd_71811 16388248568943899036557 := by
  unfold tailWord_71811
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619162342848486187495287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1746108228565657458330191 2619162342848486187495287)
  ·
    refine ⟨3928743514272729281242931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2619162342848486187495287 3928743514272729281242931)
    ·
      refine ⟨5893115271409093921864397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928743514272729281242931 5893115271409093921864397)
      ·
        refine ⟨2209918226778410220699149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5893115271409093921864397 2209918226778410220699149)
        ·
          refine ⟨828719335041903832762181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2209918226778410220699149 828719335041903832762181)
          ·
            refine ⟨155384875320356968642909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 828719335041903832762181 155384875320356968642909)
            ·
              refine ⟨58269328245133863241091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155384875320356968642909 58269328245133863241091)
              ·
                refine ⟨87403992367700794861637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58269328245133863241091 87403992367700794861637)
                ·
                  refine ⟨16388248568943899036557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87403992367700794861637 16388248568943899036557)
                  ·
                    rfl

theorem cell21_71811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 4].length) (baseStart_71811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71811 prefixEnd_71811 := by exact prefixLift 71811
  have htrace : WordTrace (prefixWord ++ tailWord_71811) baseStart_71811 baseEnd_71811 := by
    simpa [prefixWord, tailWord_71811, baseEnd_71811] using wordTrace_append hprefix tailTrace_71811
  have hstable : (prefixWord ++ tailWord_71811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71811).length < 2 ^ (prefixWord ++ tailWord_71811).sum := by decide
  have hdescent : baseEnd_71811 < baseStart_71811 := by decide
  rcases family_descends (prefixWord ++ tailWord_71811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71907 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 3]
def baseStart_71907 : Nat := 118140960795 + 71907 * 2 ^ 59
def prefixEnd_71907 : Nat := 4983230072969 + 3 ^ 40 * 71907 * 2
def baseEnd_71907 : Nat := 16410157076869065436361

theorem tailTrace_71907 : CollatzResearch.WordTrace tailWord_71907 prefixEnd_71907 16410157076869065436361 := by
  unfold tailWord_71907
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622663750500694582989975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1748442500333796388659983 2622663750500694582989975)
  ·
    refine ⟨3933995625751041874484963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622663750500694582989975 3933995625751041874484963)
    ·
      refine ⟨5900993438626562811727445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3933995625751041874484963 5900993438626562811727445)
      ·
        refine ⟨69152266858905032949931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 5900993438626562811727445 69152266858905032949931)
        ·
          refine ⟨103728400288357549424897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69152266858905032949931 103728400288357549424897)
          ·
            refine ⟨77796300216268162068673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103728400288357549424897 77796300216268162068673)
            ·
              refine ⟨58347225162201121551505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77796300216268162068673 58347225162201121551505)
              ·
                refine ⟨43760418871650841163629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58347225162201121551505 43760418871650841163629)
                ·
                  refine ⟨16410157076869065436361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43760418871650841163629 16410157076869065436361)
                  ·
                    rfl

theorem cell21_71907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 3].length) (baseStart_71907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71907 prefixEnd_71907 := by exact prefixLift 71907
  have htrace : WordTrace (prefixWord ++ tailWord_71907) baseStart_71907 baseEnd_71907 := by
    simpa [prefixWord, tailWord_71907, baseEnd_71907] using wordTrace_append hprefix tailTrace_71907
  have hstable : (prefixWord ++ tailWord_71907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71907).length < 2 ^ (prefixWord ++ tailWord_71907).sum := by decide
  have hdescent : baseEnd_71907 < baseStart_71907 := by decide
  rcases family_descends (prefixWord ++ tailWord_71907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_71966 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_71966 : Nat := 118140960795 + 71966 * 2 ^ 59
def prefixEnd_71966 : Nat := 4983230072969 + 3 ^ 40 * 71966 * 2
def baseEnd_71966 : Nat := 16423621680698073952907

theorem tailTrace_71966 : CollatzResearch.WordTrace tailWord_71966 prefixEnd_71966 16423621680698073952907 := by
  unfold tailWord_71966
  simp only [CollatzResearch.WordTrace]
  refine ⟨328101957160868457423469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1749877104857965106258501 328101957160868457423469)
  ·
    refine ⟨123038233935325671533801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 328101957160868457423469 123038233935325671533801)
    ·
      refine ⟨92278675451494253650351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123038233935325671533801 92278675451494253650351)
      ·
        refine ⟨138418013177241380475527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92278675451494253650351 138418013177241380475527)
        ·
          refine ⟨207627019765862070713291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138418013177241380475527 207627019765862070713291)
          ·
            refine ⟨311440529648793106069937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207627019765862070713291 311440529648793106069937)
            ·
              refine ⟨233580397236594829552453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311440529648793106069937 233580397236594829552453)
              ·
                refine ⟨43796324481861530541085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233580397236594829552453 43796324481861530541085)
                ·
                  refine ⟨16423621680698073952907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43796324481861530541085 16423621680698073952907)
                  ·
                    rfl

theorem cell21_71966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_71966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_71966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_71966 prefixEnd_71966 := by exact prefixLift 71966
  have htrace : WordTrace (prefixWord ++ tailWord_71966) baseStart_71966 baseEnd_71966 := by
    simpa [prefixWord, tailWord_71966, baseEnd_71966] using wordTrace_append hprefix tailTrace_71966
  have hstable : (prefixWord ++ tailWord_71966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_71966).length < 2 ^ (prefixWord ++ tailWord_71966).sum := by decide
  have hdescent : baseEnd_71966 < baseStart_71966 := by decide
  rcases family_descends (prefixWord ++ tailWord_71966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72008 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_72008 : Nat := 118140960795 + 72008 * 2 ^ 59
def prefixEnd_72008 : Nat := 4983230072969 + 3 ^ 40 * 72008 * 2
def baseEnd_72008 : Nat := 16433206652915334252821

theorem tailTrace_72008 : CollatzResearch.WordTrace tailWord_72008 prefixEnd_72008 16433206652915334252821 := by
  unfold tailWord_72008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313173761567394416208339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1750898348756525888277785 1313173761567394416208339)
  ·
    refine ⟨1969760642351091624312509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313173761567394416208339 1969760642351091624312509)
    ·
      refine ⟨738660240881659359117191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1969760642351091624312509 738660240881659359117191)
      ·
        refine ⟨1107990361322489038675787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738660240881659359117191 1107990361322489038675787)
        ·
          refine ⟨1661985541983733558013681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107990361322489038675787 1661985541983733558013681)
          ·
            refine ⟨1246489156487800168510261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661985541983733558013681 1246489156487800168510261)
            ·
              refine ⟨116858358420731265797837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1246489156487800168510261 116858358420731265797837)
              ·
                refine ⟨43821884407774224674189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116858358420731265797837 43821884407774224674189)
                ·
                  refine ⟨16433206652915334252821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43821884407774224674189 16433206652915334252821)
                  ·
                    rfl

theorem cell21_72008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_72008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72008 prefixEnd_72008 := by exact prefixLift 72008
  have htrace : WordTrace (prefixWord ++ tailWord_72008) baseStart_72008 baseEnd_72008 := by
    simpa [prefixWord, tailWord_72008, baseEnd_72008] using wordTrace_append hprefix tailTrace_72008
  have hstable : (prefixWord ++ tailWord_72008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72008).length < 2 ^ (prefixWord ++ tailWord_72008).sum := by decide
  have hdescent : baseEnd_72008 < baseStart_72008 := by decide
  rcases family_descends (prefixWord ++ tailWord_72008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72036 : List Nat := [2, 3, 1, 1, 3, 1, 4, 6]
def baseStart_72036 : Nat := 118140960795 + 72036 * 2 ^ 59
def prefixEnd_72036 : Nat := 4983230072969 + 3 ^ 40 * 72036 * 2
def baseEnd_72036 : Nat := 5479865544797835928699

theorem tailTrace_72036 : CollatzResearch.WordTrace tailWord_72036 prefixEnd_72036 5479865544797835928699 := by
  unfold tailWord_72036
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313684383516674807217981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1751579178022233076290641 1313684383516674807217981)
  ·
    refine ⟨492631643818753052706743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1313684383516674807217981 492631643818753052706743)
    ·
      refine ⟨738947465728129579060115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492631643818753052706743 738947465728129579060115)
      ·
        refine ⟨1108421198592194368590173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738947465728129579060115 1108421198592194368590173)
        ·
          refine ⟨415657949472072888221315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1108421198592194368590173 415657949472072888221315)
          ·
            refine ⟨623486924208109332331973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415657949472072888221315 623486924208109332331973)
            ·
              refine ⟨116903798289020499812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 623486924208109332331973 116903798289020499812245)
              ·
                refine ⟨5479865544797835928699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116903798289020499812245 5479865544797835928699)
                ·
                  rfl

theorem cell21_72036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_72036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72036 prefixEnd_72036 := by exact prefixLift 72036
  have htrace : WordTrace (prefixWord ++ tailWord_72036) baseStart_72036 baseEnd_72036 := by
    simpa [prefixWord, tailWord_72036, baseEnd_72036] using wordTrace_append hprefix tailTrace_72036
  have hstable : (prefixWord ++ tailWord_72036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72036).length < 2 ^ (prefixWord ++ tailWord_72036).sum := by decide
  have hdescent : baseEnd_72036 < baseStart_72036 := by decide
  rcases family_descends (prefixWord ++ tailWord_72036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72039 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 4]
def baseStart_72039 : Nat := 118140960795 + 72039 * 2 ^ 59
def prefixEnd_72039 : Nat := 4983230072969 + 3 ^ 40 * 72039 * 2
def baseEnd_72039 : Nat := 16440281275266169236091

theorem tailTrace_72039 : CollatzResearch.WordTrace tailWord_72039 prefixEnd_72039 16440281275266169236091 := by
  unfold tailWord_72039
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627478186022481126795171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1751652124014987417863447 2627478186022481126795171)
  ·
    refine ⟨3941217279033721690192757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2627478186022481126795171 3941217279033721690192757)
    ·
      refine ⟨369489119909411408455571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3941217279033721690192757 369489119909411408455571)
      ·
        refine ⟨554233679864117112683357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369489119909411408455571 554233679864117112683357)
        ·
          refine ⟨207837629949043917256259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 554233679864117112683357 207837629949043917256259)
          ·
            refine ⟨311756444923565875884389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207837629949043917256259 311756444923565875884389)
            ·
              refine ⟨58454333423168601728323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 311756444923565875884389 58454333423168601728323)
              ·
                refine ⟨87681500134752902592485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58454333423168601728323 87681500134752902592485)
                ·
                  refine ⟨16440281275266169236091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87681500134752902592485 16440281275266169236091)
                  ·
                    rfl

theorem cell21_72039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 4].length) (baseStart_72039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72039 prefixEnd_72039 := by exact prefixLift 72039
  have htrace : WordTrace (prefixWord ++ tailWord_72039) baseStart_72039 baseEnd_72039 := by
    simpa [prefixWord, tailWord_72039, baseEnd_72039] using wordTrace_append hprefix tailTrace_72039
  have hstable : (prefixWord ++ tailWord_72039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72039).length < 2 ^ (prefixWord ++ tailWord_72039).sum := by decide
  have hdescent : baseEnd_72039 < baseStart_72039 := by decide
  rcases family_descends (prefixWord ++ tailWord_72039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72098 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_72098 : Nat := 118140960795 + 72098 * 2 ^ 59
def prefixEnd_72098 : Nat := 4983230072969 + 3 ^ 40 * 72098 * 2
def baseEnd_72098 : Nat := 16453745879095177752637

theorem tailTrace_72098 : CollatzResearch.WordTrace tailWord_72098 prefixEnd_72098 16453745879095177752637 := by
  unfold tailWord_72098
  simp only [CollatzResearch.WordTrace]
  refine ⟨657407523202183550798237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1753086728539156135461965 657407523202183550798237)
  ·
    refine ⟨246527821200818831549339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 657407523202183550798237 246527821200818831549339)
    ·
      refine ⟨369791731801228247324009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 246527821200818831549339 369791731801228247324009)
      ·
        refine ⟨277343798850921185493007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369791731801228247324009 277343798850921185493007)
        ·
          refine ⟨416015698276381778239511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277343798850921185493007 416015698276381778239511)
          ·
            refine ⟨624023547414572667359267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416015698276381778239511 624023547414572667359267)
            ·
              refine ⟨936035321121859001038901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624023547414572667359267 936035321121859001038901)
              ·
                refine ⟨87753311355174281347397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936035321121859001038901 87753311355174281347397)
                ·
                  refine ⟨16453745879095177752637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87753311355174281347397 16453745879095177752637)
                  ·
                    rfl

theorem cell21_72098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_72098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72098 prefixEnd_72098 := by exact prefixLift 72098
  have htrace : WordTrace (prefixWord ++ tailWord_72098) baseStart_72098 baseEnd_72098 := by
    simpa [prefixWord, tailWord_72098, baseEnd_72098] using wordTrace_append hprefix tailTrace_72098
  have hstable : (prefixWord ++ tailWord_72098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72098).length < 2 ^ (prefixWord ++ tailWord_72098).sum := by decide
  have hdescent : baseEnd_72098 < baseStart_72098 := by decide
  rcases family_descends (prefixWord ++ tailWord_72098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72132 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_72132 : Nat := 118140960795 + 72132 * 2 ^ 59
def prefixEnd_72132 : Nat := 4983230072969 + 3 ^ 40 * 72132 * 2
def baseEnd_72132 : Nat := 16461505142318674185901

theorem tailTrace_72132 : CollatzResearch.WordTrace tailWord_72132 prefixEnd_72132 16461505142318674185901 := by
  unfold tailWord_72132
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315435087342779004965325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1753913449790372006620433 1315435087342779004965325)
  ·
    refine ⟨493288157753542126861997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1315435087342779004965325 493288157753542126861997)
    ·
      refine ⟨184983059157578297573249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 493288157753542126861997 184983059157578297573249)
      ·
        refine ⟨138737294368183723179937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 184983059157578297573249 138737294368183723179937)
        ·
          refine ⟨104052970776137792384953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138737294368183723179937 104052970776137792384953)
          ·
            refine ⟨78039728082103344288715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104052970776137792384953 78039728082103344288715)
            ·
              refine ⟨117059592123155016433073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78039728082103344288715 117059592123155016433073)
              ·
                refine ⟨87794694092366262324805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117059592123155016433073 87794694092366262324805)
                ·
                  refine ⟨16461505142318674185901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87794694092366262324805 16461505142318674185901)
                  ·
                    rfl

theorem cell21_72132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_72132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72132 prefixEnd_72132 := by exact prefixLift 72132
  have htrace : WordTrace (prefixWord ++ tailWord_72132) baseStart_72132 baseEnd_72132 := by
    simpa [prefixWord, tailWord_72132, baseEnd_72132] using wordTrace_append hprefix tailTrace_72132
  have hstable : (prefixWord ++ tailWord_72132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72132).length < 2 ^ (prefixWord ++ tailWord_72132).sum := by decide
  have hdescent : baseEnd_72132 < baseStart_72132 := by decide
  rcases family_descends (prefixWord ++ tailWord_72132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72171 : List Nat := [1, 1, 1, 1, 2, 3, 5, 7]
def baseStart_72171 : Nat := 118140960795 + 72171 * 2 ^ 59
def prefixEnd_72171 : Nat := 4983230072969 + 3 ^ 40 * 72171 * 2
def baseEnd_72171 : Nat := 5490135157887757678607

theorem tailTrace_72171 : CollatzResearch.WordTrace tailWord_72171 prefixEnd_72171 5490135157887757678607 := by
  unfold tailWord_72171
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632292621544267670600367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1754861747696178447066911 2632292621544267670600367)
  ·
    refine ⟨3948438932316401505900551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2632292621544267670600367 3948438932316401505900551)
    ·
      refine ⟨5922658398474602258850827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948438932316401505900551 5922658398474602258850827)
      ·
        refine ⟨8883987597711903388276241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5922658398474602258850827 8883987597711903388276241)
        ·
          refine ⟨6662990698283927541207181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8883987597711903388276241 6662990698283927541207181)
          ·
            refine ⟨2498621511856472827952693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6662990698283927541207181 2498621511856472827952693)
            ·
              refine ⟨234245766736544327620565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2498621511856472827952693 234245766736544327620565)
              ·
                refine ⟨5490135157887757678607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 234245766736544327620565 5490135157887757678607)
                ·
                  rfl

theorem cell21_72171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_72171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72171 prefixEnd_72171 := by exact prefixLift 72171
  have htrace : WordTrace (prefixWord ++ tailWord_72171) baseStart_72171 baseEnd_72171 := by
    simpa [prefixWord, tailWord_72171, baseEnd_72171] using wordTrace_append hprefix tailTrace_72171
  have hstable : (prefixWord ++ tailWord_72171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72171).length < 2 ^ (prefixWord ++ tailWord_72171).sum := by decide
  have hdescent : baseEnd_72171 < baseStart_72171 := by decide
  rcases family_descends (prefixWord ++ tailWord_72171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72194 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_72194 : Nat := 118140960795 + 72194 * 2 ^ 59
def prefixEnd_72194 : Nat := 4983230072969 + 3 ^ 40 * 72194 * 2
def baseEnd_72194 : Nat := 16475654387020344152441

theorem tailTrace_72194 : CollatzResearch.WordTrace tailWord_72194 prefixEnd_72194 16475654387020344152441 := by
  unfold tailWord_72194
  simp only [CollatzResearch.WordTrace]
  refine ⟨658282875115235649671909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1755421000307295065791757 658282875115235649671909)
  ·
    refine ⟨123428039084106684313483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 658282875115235649671909 123428039084106684313483)
    ·
      refine ⟨185142058626160026470225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123428039084106684313483 185142058626160026470225)
      ·
        refine ⟨138856543969620019852669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185142058626160026470225 138856543969620019852669)
        ·
          refine ⟨52071203988607507444751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 138856543969620019852669 52071203988607507444751)
          ·
            refine ⟨78106805982911261167127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52071203988607507444751 78106805982911261167127)
            ·
              refine ⟨117160208974366891750691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78106805982911261167127 117160208974366891750691)
              ·
                refine ⟨175740313461550337626037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117160208974366891750691 175740313461550337626037)
                ·
                  refine ⟨16475654387020344152441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 175740313461550337626037 16475654387020344152441)
                  ·
                    rfl

theorem cell21_72194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_72194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72194 prefixEnd_72194 := by exact prefixLift 72194
  have htrace : WordTrace (prefixWord ++ tailWord_72194) baseStart_72194 baseEnd_72194 := by
    simpa [prefixWord, tailWord_72194, baseEnd_72194] using wordTrace_append hprefix tailTrace_72194
  have hstable : (prefixWord ++ tailWord_72194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72194).length < 2 ^ (prefixWord ++ tailWord_72194).sum := by decide
  have hdescent : baseEnd_72194 < baseStart_72194 := by decide
  rcases family_descends (prefixWord ++ tailWord_72194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72250 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_72250 : Nat := 118140960795 + 72250 * 2 ^ 59
def prefixEnd_72250 : Nat := 4983230072969 + 3 ^ 40 * 72250 * 2
def baseEnd_72250 : Nat := 16488434349976691218993

theorem tailTrace_72250 : CollatzResearch.WordTrace tailWord_72250 prefixEnd_72250 16488434349976691218993 := by
  unfold tailWord_72250
  simp only [CollatzResearch.WordTrace]
  refine ⟨658793497064516040681551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1756782658838709441817469 658793497064516040681551)
  ·
    refine ⟨988190245596774061022327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 658793497064516040681551 988190245596774061022327)
    ·
      refine ⟨1482285368395161091533491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988190245596774061022327 1482285368395161091533491)
      ·
        refine ⟨2223428052592741637300237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482285368395161091533491 2223428052592741637300237)
        ·
          refine ⟨833785519722278113987589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2223428052592741637300237 833785519722278113987589)
          ·
            refine ⟨156334784947927146372673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 833785519722278113987589 156334784947927146372673)
            ·
              refine ⟨117251088710945359779505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156334784947927146372673 117251088710945359779505)
              ·
                refine ⟨87938316533209019834629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117251088710945359779505 87938316533209019834629)
                ·
                  refine ⟨16488434349976691218993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87938316533209019834629 16488434349976691218993)
                  ·
                    rfl

theorem cell21_72250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_72250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72250 prefixEnd_72250 := by exact prefixLift 72250
  have htrace : WordTrace (prefixWord ++ tailWord_72250) baseStart_72250 baseEnd_72250 := by
    simpa [prefixWord, tailWord_72250, baseEnd_72250] using wordTrace_append hprefix tailTrace_72250
  have hstable : (prefixWord ++ tailWord_72250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72250).length < 2 ^ (prefixWord ++ tailWord_72250).sum := by decide
  have hdescent : baseEnd_72250 < baseStart_72250 := by decide
  rcases family_descends (prefixWord ++ tailWord_72250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72253 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 3]
def baseStart_72253 : Nat := 118140960795 + 72253 * 2 ^ 59
def prefixEnd_72253 : Nat := 4983230072969 + 3 ^ 40 * 72253 * 2
def baseEnd_72253 : Nat := 16489118990849352668987

theorem tailTrace_72253 : CollatzResearch.WordTrace tailWord_72253 prefixEnd_72253 16489118990849352668987 := by
  unfold tailWord_72253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2635283407247195675085413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1756855604831463783390275 2635283407247195675085413)
  ·
    refine ⟨494115638858849189078515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2635283407247195675085413 494115638858849189078515)
    ·
      refine ⟨741173458288273783617773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494115638858849189078515 741173458288273783617773)
      ·
        refine ⟨277940046858102668856665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 741173458288273783617773 277940046858102668856665)
        ·
          refine ⟨208455035143577001642499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277940046858102668856665 208455035143577001642499)
          ·
            refine ⟨312682552715365502463749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208455035143577001642499 312682552715365502463749)
            ·
              refine ⟨58627978634131031711953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 312682552715365502463749 58627978634131031711953)
              ·
                refine ⟨43970983975598273783965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58627978634131031711953 43970983975598273783965)
                ·
                  refine ⟨16489118990849352668987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43970983975598273783965 16489118990849352668987)
                  ·
                    rfl

theorem cell21_72253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_72253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72253 prefixEnd_72253 := by exact prefixLift 72253
  have htrace : WordTrace (prefixWord ++ tailWord_72253) baseStart_72253 baseEnd_72253 := by
    simpa [prefixWord, tailWord_72253, baseEnd_72253] using wordTrace_append hprefix tailTrace_72253
  have hstable : (prefixWord ++ tailWord_72253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72253).length < 2 ^ (prefixWord ++ tailWord_72253).sum := by decide
  have hdescent : baseEnd_72253 < baseStart_72253 := by decide
  rcases family_descends (prefixWord ++ tailWord_72253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72346 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_72346 : Nat := 118140960795 + 72346 * 2 ^ 59
def prefixEnd_72346 : Nat := 4983230072969 + 3 ^ 40 * 72346 * 2
def baseEnd_72346 : Nat := 16510342857901857618797

theorem tailTrace_72346 : CollatzResearch.WordTrace tailWord_72346 prefixEnd_72346 16510342857901857618797 := by
  unfold tailWord_72346
  simp only [CollatzResearch.WordTrace]
  refine ⟨659668848977568139555223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1759116930606848372147261 659668848977568139555223)
  ·
    refine ⟨989503273466352209332835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659668848977568139555223 989503273466352209332835)
    ·
      refine ⟨1484254910199528313999253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989503273466352209332835 1484254910199528313999253)
      ·
        refine ⟨69574448915602889718715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1484254910199528313999253 69574448915602889718715)
        ·
          refine ⟨104361673373404334578073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69574448915602889718715 104361673373404334578073)
          ·
            refine ⟨78271255030053250933555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104361673373404334578073 78271255030053250933555)
            ·
              refine ⟨117406882545079876400333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78271255030053250933555 117406882545079876400333)
              ·
                refine ⟨44027580954404953650125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117406882545079876400333 44027580954404953650125)
                ·
                  refine ⟨16510342857901857618797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44027580954404953650125 16510342857901857618797)
                  ·
                    rfl

theorem cell21_72346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_72346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72346 prefixEnd_72346 := by exact prefixLift 72346
  have htrace : WordTrace (prefixWord ++ tailWord_72346) baseStart_72346 baseEnd_72346 := by
    simpa [prefixWord, tailWord_72346, baseEnd_72346] using wordTrace_append hprefix tailTrace_72346
  have hstable : (prefixWord ++ tailWord_72346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72346).length < 2 ^ (prefixWord ++ tailWord_72346).sum := by decide
  have hdescent : baseEnd_72346 < baseStart_72346 := by decide
  rcases family_descends (prefixWord ++ tailWord_72346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72371 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 5]
def baseStart_72371 : Nat := 118140960795 + 72371 * 2 ^ 59
def prefixEnd_72371 : Nat := 4983230072969 + 3 ^ 40 * 72371 * 2
def baseEnd_72371 : Nat := 16516048198507369702079

theorem tailTrace_72371 : CollatzResearch.WordTrace tailWord_72371 prefixEnd_72371 16516048198507369702079 := by
  unfold tailWord_72371
  simp only [CollatzResearch.WordTrace]
  refine ⟨2639587220819701827880967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1759724813879801218587311 2639587220819701827880967)
  ·
    refine ⟨3959380831229552741821451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2639587220819701827880967 3959380831229552741821451)
    ·
      refine ⟨5939071246844329112732177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3959380831229552741821451 5939071246844329112732177)
      ·
        refine ⟨4454303435133246834549133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5939071246844329112732177 4454303435133246834549133)
        ·
          refine ⟨1670363788174967562955925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4454303435133246834549133 1670363788174967562955925)
          ·
            refine ⟨78298302570701604513559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1670363788174967562955925 78298302570701604513559)
            ·
              refine ⟨117447453856052406770339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78298302570701604513559 117447453856052406770339)
              ·
                refine ⟨176171180784078610155509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117447453856052406770339 176171180784078610155509)
                ·
                  refine ⟨16516048198507369702079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176171180784078610155509 16516048198507369702079)
                  ·
                    rfl

theorem cell21_72371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_72371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72371 prefixEnd_72371 := by exact prefixLift 72371
  have htrace : WordTrace (prefixWord ++ tailWord_72371) baseStart_72371 baseEnd_72371 := by
    simpa [prefixWord, tailWord_72371, baseEnd_72371] using wordTrace_append hprefix tailTrace_72371
  have hstable : (prefixWord ++ tailWord_72371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72371).length < 2 ^ (prefixWord ++ tailWord_72371).sum := by decide
  have hdescent : baseEnd_72371 < baseStart_72371 := by decide
  rcases family_descends (prefixWord ++ tailWord_72371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72374 : List Nat := [5, 1, 3, 1, 2, 1, 2, 6]
def baseStart_72374 : Nat := 118140960795 + 72374 * 2 ^ 59
def prefixEnd_72374 : Nat := 4983230072969 + 3 ^ 40 * 72374 * 2
def baseEnd_72374 : Nat := 5505577613126677050691

theorem tailTrace_72374 : CollatzResearch.WordTrace tailWord_72374 prefixEnd_72374 5505577613126677050691 := by
  unfold tailWord_72374
  simp only [CollatzResearch.WordTrace]
  refine ⟨164981039988052083765011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1759797759872555560160117 164981039988052083765011)
  ·
    refine ⟨247471559982078125647517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 164981039988052083765011 247471559982078125647517)
    ·
      refine ⟨92801834993279297117819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247471559982078125647517 92801834993279297117819)
      ·
        refine ⟨139202752489918945676729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92801834993279297117819 139202752489918945676729)
        ·
          refine ⟨104402064367439209257547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139202752489918945676729 104402064367439209257547)
          ·
            refine ⟨156603096551158813886321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104402064367439209257547 156603096551158813886321)
            ·
              refine ⟨117452322413369110414741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156603096551158813886321 117452322413369110414741)
              ·
                refine ⟨5505577613126677050691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117452322413369110414741 5505577613126677050691)
                ·
                  rfl

theorem cell21_72374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_72374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72374 prefixEnd_72374 := by exact prefixLift 72374
  have htrace : WordTrace (prefixWord ++ tailWord_72374) baseStart_72374 baseEnd_72374 := by
    simpa [prefixWord, tailWord_72374, baseEnd_72374] using wordTrace_append hprefix tailTrace_72374
  have hstable : (prefixWord ++ tailWord_72374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72374).length < 2 ^ (prefixWord ++ tailWord_72374).sum := by decide
  have hdescent : baseEnd_72374 < baseStart_72374 := by decide
  rcases family_descends (prefixWord ++ tailWord_72374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72489 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_72489 : Nat := 118140960795 + 72489 * 2 ^ 59
def prefixEnd_72489 : Nat := 4983230072969 + 3 ^ 40 * 72489 * 2
def baseEnd_72489 : Nat := 16542977406165386735171

theorem tailTrace_72489 : CollatzResearch.WordTrace tailWord_72489 prefixEnd_72489 16542977406165386735171 := by
  unfold tailWord_72489
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643891034392207980676521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1762594022928138653784347 2643891034392207980676521)
  ·
    refine ⟨1982918275794155985507391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2643891034392207980676521 1982918275794155985507391)
    ·
      refine ⟨2974377413691233978261087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1982918275794155985507391 2974377413691233978261087)
      ·
        refine ⟨4461566120536850967391631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974377413691233978261087 4461566120536850967391631)
        ·
          refine ⟨6692349180805276451087447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461566120536850967391631 6692349180805276451087447)
          ·
            refine ⟨10038523771207914676631171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6692349180805276451087447 10038523771207914676631171)
            ·
              refine ⟨15057785656811872014946757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10038523771207914676631171 15057785656811872014946757)
              ·
                refine ⟨2823334810652226002802517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15057785656811872014946757 2823334810652226002802517)
                ·
                  refine ⟨16542977406165386735171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2823334810652226002802517 16542977406165386735171)
                  ·
                    rfl

theorem cell21_72489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_72489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72489 prefixEnd_72489 := by exact prefixLift 72489
  have htrace : WordTrace (prefixWord ++ tailWord_72489) baseStart_72489 baseEnd_72489 := by
    simpa [prefixWord, tailWord_72489, baseEnd_72489] using wordTrace_append hprefix tailTrace_72489
  have hstable : (prefixWord ++ tailWord_72489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72489).length < 2 ^ (prefixWord ++ tailWord_72489).sum := by decide
  have hdescent : baseEnd_72489 < baseStart_72489 := by decide
  rcases family_descends (prefixWord ++ tailWord_72489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72520 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_72520 : Nat := 118140960795 + 72520 * 2 ^ 59
def prefixEnd_72520 : Nat := 4983230072969 + 3 ^ 40 * 72520 * 2
def baseEnd_72520 : Nat := 16550052028516221718441

theorem tailTrace_72520 : CollatzResearch.WordTrace tailWord_72520 prefixEnd_72520 16550052028516221718441 := by
  unfold tailWord_72520
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322510848639950137527507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1763347798186600183370009 1322510848639950137527507)
  ·
    refine ⟨1983766272959925206291261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322510848639950137527507 1983766272959925206291261)
    ·
      refine ⟨743912352359971952359223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1983766272959925206291261 743912352359971952359223)
      ·
        refine ⟨1115868528539957928538835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743912352359971952359223 1115868528539957928538835)
        ·
          refine ⟨1673802792809936892808253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115868528539957928538835 1673802792809936892808253)
          ·
            refine ⟨627676047303726334803095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1673802792809936892808253 627676047303726334803095)
            ·
              refine ⟨941514070955589502204643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627676047303726334803095 941514070955589502204643)
              ·
                refine ⟨1412271106433384253306965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941514070955589502204643 1412271106433384253306965)
                ·
                  refine ⟨16550052028516221718441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1412271106433384253306965 16550052028516221718441)
                  ·
                    rfl

theorem cell21_72520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_72520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72520 prefixEnd_72520 := by exact prefixLift 72520
  have htrace : WordTrace (prefixWord ++ tailWord_72520) baseStart_72520 baseEnd_72520 := by
    simpa [prefixWord, tailWord_72520, baseEnd_72520] using wordTrace_append hprefix tailTrace_72520
  have hstable : (prefixWord ++ tailWord_72520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72520).length < 2 ^ (prefixWord ++ tailWord_72520).sum := by decide
  have hdescent : baseEnd_72520 < baseStart_72520 := by decide
  rcases family_descends (prefixWord ++ tailWord_72520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72540 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_72540 : Nat := 118140960795 + 72540 * 2 ^ 59
def prefixEnd_72540 : Nat := 4983230072969 + 3 ^ 40 * 72540 * 2
def baseEnd_72540 : Nat := 16554616301000631385067

theorem tailTrace_72540 : CollatzResearch.WordTrace tailWord_72540 prefixEnd_72540 16554616301000631385067 := by
  unfold tailWord_72540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322875578603721845391537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1763834104804962460522049 1322875578603721845391537)
  ·
    refine ⟨992156683952791384043653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1322875578603721845391537 992156683952791384043653)
    ·
      refine ⟨186029378241148384508185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 992156683952791384043653 186029378241148384508185)
      ·
        refine ⟨139522033680861288381139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186029378241148384508185 139522033680861288381139)
        ·
          refine ⟨209283050521291932571709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139522033680861288381139 209283050521291932571709)
          ·
            refine ⟨78481143945484474714391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209283050521291932571709 78481143945484474714391)
            ·
              refine ⟨117721715918226712071587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78481143945484474714391 117721715918226712071587)
              ·
                refine ⟨176582573877340068107381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117721715918226712071587 176582573877340068107381)
                ·
                  refine ⟨16554616301000631385067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176582573877340068107381 16554616301000631385067)
                  ·
                    rfl

theorem cell21_72540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_72540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72540 prefixEnd_72540 := by exact prefixLift 72540
  have htrace : WordTrace (prefixWord ++ tailWord_72540) baseStart_72540 baseEnd_72540 := by
    simpa [prefixWord, tailWord_72540, baseEnd_72540] using wordTrace_append hprefix tailTrace_72540
  have hstable : (prefixWord ++ tailWord_72540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72540).length < 2 ^ (prefixWord ++ tailWord_72540).sum := by decide
  have hdescent : baseEnd_72540 < baseStart_72540 := by decide
  rcases family_descends (prefixWord ++ tailWord_72540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72551 : List Nat := [1, 1, 5, 1, 2, 2, 1, 8]
def baseStart_72551 : Nat := 118140960795 + 72551 * 2 ^ 59
def prefixEnd_72551 : Nat := 4983230072969 + 3 ^ 40 * 72551 * 2
def baseEnd_72551 : Nat := 5519042216955685567237

theorem tailTrace_72551 : CollatzResearch.WordTrace tailWord_72551 prefixEnd_72551 5519042216955685567237 := by
  unfold tailWord_72551
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646152360167592569433507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1764101573445061712955671 2646152360167592569433507)
  ·
    refine ⟨3969228540251388854150261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646152360167592569433507 3969228540251388854150261)
    ·
      refine ⟨372115175648567705076587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3969228540251388854150261 372115175648567705076587)
      ·
        refine ⟨558172763472851557614881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372115175648567705076587 558172763472851557614881)
        ·
          refine ⟨418629572604638668211161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558172763472851557614881 418629572604638668211161)
          ·
            refine ⟨313972179453479001158371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418629572604638668211161 313972179453479001158371)
            ·
              refine ⟨470958269180218501737557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313972179453479001158371 470958269180218501737557)
              ·
                refine ⟨5519042216955685567237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 470958269180218501737557 5519042216955685567237)
                ·
                  rfl

theorem cell21_72551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_72551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72551 prefixEnd_72551 := by exact prefixLift 72551
  have htrace : WordTrace (prefixWord ++ tailWord_72551) baseStart_72551 baseEnd_72551 := by
    simpa [prefixWord, tailWord_72551, baseEnd_72551] using wordTrace_append hprefix tailTrace_72551
  have hstable : (prefixWord ++ tailWord_72551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72551).length < 2 ^ (prefixWord ++ tailWord_72551).sum := by decide
  have hdescent : baseEnd_72551 < baseStart_72551 := by decide
  rcases family_descends (prefixWord ++ tailWord_72551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72599 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 3]
def baseStart_72599 : Nat := 118140960795 + 72599 * 2 ^ 59
def prefixEnd_72599 : Nat := 4983230072969 + 3 ^ 40 * 72599 * 2
def baseEnd_72599 : Nat := 16568080904829639901613

theorem tailTrace_72599 : CollatzResearch.WordTrace tailWord_72599 prefixEnd_72599 16568080904829639901613 := by
  unfold tailWord_72599
  simp only [CollatzResearch.WordTrace]
  refine ⟨2647903063993696767180851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1765268709329131178120567 2647903063993696767180851)
  ·
    refine ⟨3971854595990545150771277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2647903063993696767180851 3971854595990545150771277)
    ·
      refine ⟨1489445473496454431539229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3971854595990545150771277 1489445473496454431539229)
      ·
        refine ⟨558542052561170411827211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1489445473496454431539229 558542052561170411827211)
        ·
          refine ⟨837813078841755617740817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558542052561170411827211 837813078841755617740817)
          ·
            refine ⟨628359809131316713305613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837813078841755617740817 628359809131316713305613)
            ·
              refine ⟨235634928424243767489605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628359809131316713305613 235634928424243767489605)
              ·
                refine ⟨44181549079545706404301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235634928424243767489605 44181549079545706404301)
                ·
                  refine ⟨16568080904829639901613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44181549079545706404301 16568080904829639901613)
                  ·
                    rfl

theorem cell21_72599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 3].length) (baseStart_72599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72599 prefixEnd_72599 := by exact prefixLift 72599
  have htrace : WordTrace (prefixWord ++ tailWord_72599) baseStart_72599 baseEnd_72599 := by
    simpa [prefixWord, tailWord_72599, baseEnd_72599] using wordTrace_append hprefix tailTrace_72599
  have hstable : (prefixWord ++ tailWord_72599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72599).length < 2 ^ (prefixWord ++ tailWord_72599).sum := by decide
  have hdescent : baseEnd_72599 < baseStart_72599 := by decide
  rcases family_descends (prefixWord ++ tailWord_72599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72765 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_72765 : Nat := 118140960795 + 72765 * 2 ^ 59
def prefixEnd_72765 : Nat := 4983230072969 + 3 ^ 40 * 72765 * 2
def baseEnd_72765 : Nat := 16605964366450240134607

theorem tailTrace_72765 : CollatzResearch.WordTrace tailWord_72765 prefixEnd_72765 16605964366450240134607 := by
  unfold tailWord_72765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653957581392307117723749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1769305054261538078482499 2653957581392307117723749)
  ·
    refine ⟨497617046511057584573203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2653957581392307117723749 497617046511057584573203)
    ·
      refine ⟨746425569766586376859805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 497617046511057584573203 746425569766586376859805)
      ·
        refine ⟨279909588662469891322427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 746425569766586376859805 279909588662469891322427)
        ·
          refine ⟨419864382993704836983641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279909588662469891322427 419864382993704836983641)
          ·
            refine ⟨314898287245278627737731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419864382993704836983641 314898287245278627737731)
            ·
              refine ⟨472347430867917941606597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314898287245278627737731 472347430867917941606597)
              ·
                refine ⟨88565143287734614051237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 472347430867917941606597 88565143287734614051237)
                ·
                  refine ⟨16605964366450240134607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88565143287734614051237 16605964366450240134607)
                  ·
                    rfl

theorem cell21_72765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_72765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72765 prefixEnd_72765 := by exact prefixLift 72765
  have htrace : WordTrace (prefixWord ++ tailWord_72765) baseStart_72765 baseEnd_72765 := by
    simpa [prefixWord, tailWord_72765, baseEnd_72765] using wordTrace_append hprefix tailTrace_72765
  have hstable : (prefixWord ++ tailWord_72765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72765).length < 2 ^ (prefixWord ++ tailWord_72765).sum := by decide
  have hdescent : baseEnd_72765 < baseStart_72765 := by decide
  rcases family_descends (prefixWord ++ tailWord_72765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
