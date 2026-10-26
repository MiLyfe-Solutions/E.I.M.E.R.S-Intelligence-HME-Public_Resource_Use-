import V185TrunkScan23Chunk0563

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3334525 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_3334525 : Nat := 118140960795 + 3334525 * 2 ^ 59
def prefixEnd_3334525 : Nat := 4983230072969 + 3 ^ 40 * 3334525 * 2
def baseEnd_3334525 : Nat := 1712214079433671389302305

theorem tailTrace_3334525 : CollatzResearch.WordTrace tailWord_3334525 prefixEnd_3334525 1712214079433671389302305 := by
  unfold tailWord_3334525
  simp only [CollatzResearch.WordTrace]
  refine ⟨121620118244592891375573029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81080078829728594250382019 121620118244592891375573029)
  ·
    refine ⟨22803772170861167132919943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121620118244592891375573029 22803772170861167132919943)
    ·
      refine ⟨34205658256291750699379915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22803772170861167132919943 34205658256291750699379915)
      ·
        refine ⟨51308487384437626049069873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34205658256291750699379915 51308487384437626049069873)
        ·
          refine ⟨38481365538328219536802405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51308487384437626049069873 38481365538328219536802405)
          ·
            refine ⟨7215256038436541163150451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38481365538328219536802405 7215256038436541163150451)
            ·
              refine ⟨10822884057654811744725677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215256038436541163150451 10822884057654811744725677)
              ·
                refine ⟨4058581521620554404272129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10822884057654811744725677 4058581521620554404272129)
                ·
                  refine ⟨3043936141215415803204097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4058581521620554404272129 3043936141215415803204097)
                  ·
                    refine ⟨2282952105911561852403073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3043936141215415803204097 2282952105911561852403073)
                    ·
                      refine ⟨1712214079433671389302305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2282952105911561852403073 1712214079433671389302305)
                      ·
                        rfl

theorem cell23_3334525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_3334525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334525 prefixEnd_3334525 := by exact prefixLift 3334525
  have htrace : WordTrace (prefixWord ++ tailWord_3334525) baseStart_3334525 baseEnd_3334525 := by
    simpa [prefixWord, tailWord_3334525, baseEnd_3334525] using wordTrace_append hprefix tailTrace_3334525
  have hstable : (prefixWord ++ tailWord_3334525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334525).length < 2 ^ (prefixWord ++ tailWord_3334525).sum := by decide
  have hdescent : baseEnd_3334525 < baseStart_3334525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334621 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 8]
def baseStart_3334621 : Nat := 118140960795 + 3334621 * 2 ^ 59
def prefixEnd_3334621 : Nat := 4983230072969 + 3 ^ 40 * 3334621 * 2
def baseEnd_3334621 : Nat := 190251485952944779300207

theorem tailTrace_3334621 : CollatzResearch.WordTrace tailWord_3334621 prefixEnd_3334621 190251485952944779300207 := by
  unfold tailWord_3334621
  simp only [CollatzResearch.WordTrace]
  refine ⟨121623619652245099771067717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81082413101496733180711811 121623619652245099771067717)
  ·
    refine ⟨22804428684795956207075197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121623619652245099771067717 22804428684795956207075197)
    ·
      refine ⟨8551660756798483577653199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22804428684795956207075197 8551660756798483577653199)
      ·
        refine ⟨12827491135197725366479799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551660756798483577653199 12827491135197725366479799)
        ·
          refine ⟨19241236702796588049719699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827491135197725366479799 19241236702796588049719699)
          ·
            refine ⟨28861855054194882074579549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19241236702796588049719699 28861855054194882074579549)
            ·
              refine ⟨10823195645323080777967331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28861855054194882074579549 10823195645323080777967331)
              ·
                refine ⟨16234793467984621166950997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10823195645323080777967331 16234793467984621166950997)
                ·
                  refine ⟨190251485952944779300207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16234793467984621166950997 190251485952944779300207)
                  ·
                    rfl

theorem cell23_3334621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_3334621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334621 prefixEnd_3334621 := by exact prefixLift 3334621
  have htrace : WordTrace (prefixWord ++ tailWord_3334621) baseStart_3334621 baseEnd_3334621 := by
    simpa [prefixWord, tailWord_3334621, baseEnd_3334621] using wordTrace_append hprefix tailTrace_3334621
  have hstable : (prefixWord ++ tailWord_3334621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334621).length < 2 ^ (prefixWord ++ tailWord_3334621).sum := by decide
  have hdescent : baseEnd_3334621 < baseStart_3334621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334624 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_3334624 : Nat := 118140960795 + 3334624 * 2 ^ 59
def prefixEnd_3334624 : Nat := 4983230072969 + 3 ^ 40 * 3334624 * 2
def baseEnd_3334624 : Nat := 1712264914018466501964349

theorem tailTrace_3334624 : CollatzResearch.WordTrace tailWord_3334624 prefixEnd_3334624 1712264914018466501964349 := by
  unfold tailWord_3334624
  simp only [CollatzResearch.WordTrace]
  refine ⟨60811864535617115641713463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81082486047489487522284617 60811864535617115641713463)
  ·
    refine ⟨91217796803425673462570195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60811864535617115641713463 91217796803425673462570195)
    ·
      refine ⟨136826695205138510193855293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91217796803425673462570195 136826695205138510193855293)
      ·
        refine ⟨51310010701926941322695735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136826695205138510193855293 51310010701926941322695735)
        ·
          refine ⟨76965016052890411984043603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51310010701926941322695735 76965016052890411984043603)
          ·
            refine ⟨115447524079335617976065405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76965016052890411984043603 115447524079335617976065405)
            ·
              refine ⟨43292821529750856741024527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115447524079335617976065405 43292821529750856741024527)
              ·
                refine ⟨64939232294626285111536791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43292821529750856741024527 64939232294626285111536791)
                ·
                  refine ⟨97408848441939427667305187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64939232294626285111536791 97408848441939427667305187)
                  ·
                    refine ⟨146113272662909141500957781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97408848441939427667305187 146113272662909141500957781)
                    ·
                      refine ⟨1712264914018466501964349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146113272662909141500957781 1712264914018466501964349)
                      ·
                        rfl

theorem cell23_3334624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_3334624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334624 prefixEnd_3334624 := by exact prefixLift 3334624
  have htrace : WordTrace (prefixWord ++ tailWord_3334624) baseStart_3334624 baseEnd_3334624 := by
    simpa [prefixWord, tailWord_3334624, baseEnd_3334624] using wordTrace_append hprefix tailTrace_3334624
  have hstable : (prefixWord ++ tailWord_3334624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334624).length < 2 ^ (prefixWord ++ tailWord_3334624).sum := by decide
  have hdescent : baseEnd_3334624 < baseStart_3334624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334648 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_3334648 : Nat := 118140960795 + 3334648 * 2 ^ 59
def prefixEnd_3334648 : Nat := 4983230072969 + 3 ^ 40 * 3334648 * 2
def baseEnd_3334648 : Nat := 1712277237554174408064239

theorem tailTrace_3334648 : CollatzResearch.WordTrace tailWord_3334648 prefixEnd_3334648 1712277237554174408064239 := by
  unfold tailWord_3334648
  simp only [CollatzResearch.WordTrace]
  refine ⟨60812302211573641691150299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81083069615431522254867065 60812302211573641691150299)
  ·
    refine ⟨91218453317360462536725449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60812302211573641691150299 91218453317360462536725449)
    ·
      refine ⟨68413839988020346902544087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91218453317360462536725449 68413839988020346902544087)
      ·
        refine ⟨102620759982030520353816131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68413839988020346902544087 102620759982030520353816131)
        ·
          refine ⟨153931139973045780530724197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102620759982030520353816131 153931139973045780530724197)
          ·
            refine ⟨28862088744946083849510787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153931139973045780530724197 28862088744946083849510787)
            ·
              refine ⟨43293133117419125774266181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28862088744946083849510787 43293133117419125774266181)
              ·
                refine ⟨8117462459516086082674909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43293133117419125774266181 8117462459516086082674909)
                ·
                  refine ⟨3044048422318532281003091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8117462459516086082674909 3044048422318532281003091)
                  ·
                    refine ⟨4566072633477798421504637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3044048422318532281003091 4566072633477798421504637)
                    ·
                      refine ⟨1712277237554174408064239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566072633477798421504637 1712277237554174408064239)
                      ·
                        rfl

theorem cell23_3334648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_3334648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334648 prefixEnd_3334648 := by exact prefixLift 3334648
  have htrace : WordTrace (prefixWord ++ tailWord_3334648) baseStart_3334648 baseEnd_3334648 := by
    simpa [prefixWord, tailWord_3334648, baseEnd_3334648] using wordTrace_append hprefix tailTrace_3334648
  have hstable : (prefixWord ++ tailWord_3334648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334648).length < 2 ^ (prefixWord ++ tailWord_3334648).sum := by decide
  have hdescent : baseEnd_3334648 < baseStart_3334648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334665 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 1, 1, 3]
def baseStart_3334665 : Nat := 118140960795 + 3334665 * 2 ^ 59
def prefixEnd_3334665 : Nat := 4983230072969 + 3 ^ 40 * 3334665 * 2
def baseEnd_3334665 : Nat := 1712285966725300841551661

theorem tailTrace_3334665 : CollatzResearch.WordTrace tailWord_3334665 prefixEnd_3334665 1712285966725300841551661 := by
  unfold tailWord_3334665
  simp only [CollatzResearch.WordTrace]
  refine ⟨121625224464085695285669449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81083482976057130190446299 121625224464085695285669449)
  ·
    refine ⟨91218918348064271464252087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121625224464085695285669449 91218918348064271464252087)
    ·
      refine ⟨136828377522096407196378131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91218918348064271464252087 136828377522096407196378131)
      ·
        refine ⟨205242566283144610794567197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136828377522096407196378131 205242566283144610794567197)
        ·
          refine ⟨76965962356179229047962699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205242566283144610794567197 76965962356179229047962699)
          ·
            refine ⟨115448943534268843571944049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76965962356179229047962699 115448943534268843571944049)
            ·
              refine ⟨86586707650701632678958037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115448943534268843571944049 86586707650701632678958037)
              ·
                refine ⟨2029375960563319515913079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86586707650701632678958037 2029375960563319515913079)
                ·
                  refine ⟨3044063940844979273869619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029375960563319515913079 3044063940844979273869619)
                  ·
                    refine ⟨4566095911267468910804429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3044063940844979273869619 4566095911267468910804429)
                    ·
                      refine ⟨1712285966725300841551661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566095911267468910804429 1712285966725300841551661)
                      ·
                        rfl

theorem cell23_3334665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 1, 3].length) (baseStart_3334665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334665 prefixEnd_3334665 := by exact prefixLift 3334665
  have htrace : WordTrace (prefixWord ++ tailWord_3334665) baseStart_3334665 baseEnd_3334665 := by
    simpa [prefixWord, tailWord_3334665, baseEnd_3334665] using wordTrace_append hprefix tailTrace_3334665
  have hstable : (prefixWord ++ tailWord_3334665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334665).length < 2 ^ (prefixWord ++ tailWord_3334665).sum := by decide
  have hdescent : baseEnd_3334665 < baseStart_3334665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334668 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_3334668 : Nat := 118140960795 + 3334668 * 2 ^ 59
def prefixEnd_3334668 : Nat := 4983230072969 + 3 ^ 40 * 3334668 * 2
def baseEnd_3334668 : Nat := 570762502389088109938049

theorem tailTrace_3334668 : CollatzResearch.WordTrace tailWord_3334668 prefixEnd_3334668 570762502389088109938049 := by
  unfold tailWord_3334668
  simp only [CollatzResearch.WordTrace]
  refine ⟨60812666941537413399014329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81083555922049884532019105 60812666941537413399014329)
  ·
    refine ⟨45609500206153060049260747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60812666941537413399014329 45609500206153060049260747)
    ·
      refine ⟨68414250309229590073891121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45609500206153060049260747 68414250309229590073891121)
      ·
        refine ⟨51310687731922192555418341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68414250309229590073891121 51310687731922192555418341)
        ·
          refine ⟨9620753949735411104140939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51310687731922192555418341 9620753949735411104140939)
          ·
            refine ⟨14431130924603116656211409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9620753949735411104140939 14431130924603116656211409)
            ·
              refine ⟨10823348193452337492158557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14431130924603116656211409 10823348193452337492158557)
              ·
                refine ⟨4058755572544626559559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10823348193452337492158557 4058755572544626559559459)
                ·
                  refine ⟨6088133358816939839339189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058755572544626559559459 6088133358816939839339189)
                  ·
                    refine ⟨570762502389088109938049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6088133358816939839339189 570762502389088109938049)
                    ·
                      rfl

theorem cell23_3334668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_3334668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334668 prefixEnd_3334668 := by exact prefixLift 3334668
  have htrace : WordTrace (prefixWord ++ tailWord_3334668) baseStart_3334668 baseEnd_3334668 := by
    simpa [prefixWord, tailWord_3334668, baseEnd_3334668] using wordTrace_append hprefix tailTrace_3334668
  have hstable : (prefixWord ++ tailWord_3334668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334668).length < 2 ^ (prefixWord ++ tailWord_3334668).sum := by decide
  have hdescent : baseEnd_3334668 < baseStart_3334668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334702 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_3334702 : Nat := 118140960795 + 3334702 * 2 ^ 59
def prefixEnd_3334702 : Nat := 4983230072969 + 3 ^ 40 * 3334702 * 2
def baseEnd_3334702 : Nat := 570768321836505732262997

theorem tailTrace_3334702 : CollatzResearch.WordTrace tailWord_3334702 prefixEnd_3334702 570768321836505732262997 := by
  unfold tailWord_3334702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15203321745618956325595795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81084382643301100403177573 15203321745618956325595795)
  ·
    refine ⟨22804982618428434488393693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15203321745618956325595795 22804982618428434488393693)
    ·
      refine ⟨8551868481910662933147635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22804982618428434488393693 8551868481910662933147635)
      ·
        refine ⟨12827802722865994399721453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551868481910662933147635 12827802722865994399721453)
        ·
          refine ⟨4810426021074747899895545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12827802722865994399721453 4810426021074747899895545)
          ·
            refine ⟨3607819515806060924921659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4810426021074747899895545 3607819515806060924921659)
            ·
              refine ⟨5411729273709091387382489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3607819515806060924921659 5411729273709091387382489)
              ·
                refine ⟨4058796955281818540536867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5411729273709091387382489 4058796955281818540536867)
                ·
                  refine ⟨6088195432922727810805301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4058796955281818540536867 6088195432922727810805301)
                  ·
                    refine ⟨570768321836505732262997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6088195432922727810805301 570768321836505732262997)
                    ·
                      rfl

theorem cell23_3334702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_3334702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334702 prefixEnd_3334702 := by exact prefixLift 3334702
  have htrace : WordTrace (prefixWord ++ tailWord_3334702) baseStart_3334702 baseEnd_3334702 := by
    simpa [prefixWord, tailWord_3334702, baseEnd_3334702] using wordTrace_append hprefix tailTrace_3334702
  have hstable : (prefixWord ++ tailWord_3334702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334702).length < 2 ^ (prefixWord ++ tailWord_3334702).sum := by decide
  have hdescent : baseEnd_3334702 < baseStart_3334702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334705 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_3334705 : Nat := 118140960795 + 3334705 * 2 ^ 59
def prefixEnd_3334705 : Nat := 4983230072969 + 3 ^ 40 * 3334705 * 2
def baseEnd_3334705 : Nat := 1712306505951480685051477

theorem tailTrace_3334705 : CollatzResearch.WordTrace tailWord_3334705 prefixEnd_3334705 1712306505951480685051477 := by
  unfold tailWord_3334705
  simp only [CollatzResearch.WordTrace]
  refine ⟨121626683383940782117125569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81084455589293854744750379 121626683383940782117125569)
  ·
    refine ⟨91220012537955586587844177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121626683383940782117125569 91220012537955586587844177)
    ·
      refine ⟨68415009403466689940883133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91220012537955586587844177 68415009403466689940883133)
      ·
        refine ⟨25655628526300008727831175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68415009403466689940883133 25655628526300008727831175)
        ·
          refine ⟨38483442789450013091746763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25655628526300008727831175 38483442789450013091746763)
          ·
            refine ⟨57725164184175019637620145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38483442789450013091746763 57725164184175019637620145)
            ·
              refine ⟨43293873138131264728215109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57725164184175019637620145 43293873138131264728215109)
              ·
                refine ⟨8117601213399612136540333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43293873138131264728215109 8117601213399612136540333)
                ·
                  refine ⟨3044100455024854551202625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8117601213399612136540333 3044100455024854551202625)
                  ·
                    refine ⟨2283075341268640913401969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3044100455024854551202625 2283075341268640913401969)
                    ·
                      refine ⟨1712306505951480685051477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283075341268640913401969 1712306505951480685051477)
                      ·
                        rfl

theorem cell23_3334705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_3334705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334705 prefixEnd_3334705 := by exact prefixLift 3334705
  have htrace : WordTrace (prefixWord ++ tailWord_3334705) baseStart_3334705 baseEnd_3334705 := by
    simpa [prefixWord, tailWord_3334705, baseEnd_3334705] using wordTrace_append hprefix tailTrace_3334705
  have hstable : (prefixWord ++ tailWord_3334705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334705).length < 2 ^ (prefixWord ++ tailWord_3334705).sum := by decide
  have hdescent : baseEnd_3334705 < baseStart_3334705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334738 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3334738 : Nat := 118140960795 + 3334738 * 2 ^ 59
def prefixEnd_3334738 : Nat := 4983230072969 + 3 ^ 40 * 3334738 * 2
def baseEnd_3334738 : Nat := 1712323450813079055938825

theorem tailTrace_3334738 : CollatzResearch.WordTrace tailWord_3334738 prefixEnd_3334738 1712323450813079055938825 := by
  unfold tailWord_3334738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30406971748205307188269217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81085257995214152502051245 30406971748205307188269217)
  ·
    refine ⟨22805228811153980391201913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30406971748205307188269217 22805228811153980391201913)
    ·
      refine ⟨17103921608365485293401435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22805228811153980391201913 17103921608365485293401435)
      ·
        refine ⟨25655882412548227940102153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103921608365485293401435 25655882412548227940102153)
        ·
          refine ⟨19241911809411170955076615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25655882412548227940102153 19241911809411170955076615)
          ·
            refine ⟨28862867714116756432614923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19241911809411170955076615 28862867714116756432614923)
            ·
              refine ⟨43294301571175134648922385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28862867714116756432614923 43294301571175134648922385)
              ·
                refine ⟨32470726178381350986691789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43294301571175134648922385 32470726178381350986691789)
                ·
                  refine ⟨12176522316893006620009421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32470726178381350986691789 12176522316893006620009421)
                  ·
                    refine ⟨4566195868834877482503533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12176522316893006620009421 4566195868834877482503533)
                    ·
                      refine ⟨1712323450813079055938825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566195868834877482503533 1712323450813079055938825)
                      ·
                        rfl

theorem cell23_3334738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3334738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334738 prefixEnd_3334738 := by exact prefixLift 3334738
  have htrace : WordTrace (prefixWord ++ tailWord_3334738) baseStart_3334738 baseEnd_3334738 := by
    simpa [prefixWord, tailWord_3334738, baseEnd_3334738] using wordTrace_append hprefix tailTrace_3334738
  have hstable : (prefixWord ++ tailWord_3334738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334738).length < 2 ^ (prefixWord ++ tailWord_3334738).sum := by decide
  have hdescent : baseEnd_3334738 < baseStart_3334738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334741 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3334741 : Nat := 118140960795 + 3334741 * 2 ^ 59
def prefixEnd_3334741 : Nat := 4983230072969 + 3 ^ 40 * 3334741 * 2
def baseEnd_3334741 : Nat := 570774997085014181400437

theorem tailTrace_3334741 : CollatzResearch.WordTrace tailWord_3334741 prefixEnd_3334741 570774997085014181400437 := by
  unfold tailWord_3334741
  simp only [CollatzResearch.WordTrace]
  refine ⟨121627996411810360265436077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81085330941206906843624051 121627996411810360265436077)
  ·
    refine ⟨45610498654428885099538529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121627996411810360265436077 45610498654428885099538529)
    ·
      refine ⟨34207873990821663824653897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45610498654428885099538529 34207873990821663824653897)
      ·
        refine ⟨25655905493116247868490423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34207873990821663824653897 25655905493116247868490423)
        ·
          refine ⟨38483858239674371802735635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25655905493116247868490423 38483858239674371802735635)
          ·
            refine ⟨57725787359511557704103453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38483858239674371802735635 57725787359511557704103453)
            ·
              refine ⟨21647170259816834139038795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57725787359511557704103453 21647170259816834139038795)
              ·
                refine ⟨32470755389725251208558193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21647170259816834139038795 32470755389725251208558193)
                ·
                  refine ⟨24353066542293938406418645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32470755389725251208558193 24353066542293938406418645)
                  ·
                    refine ⟨570774997085014181400437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24353066542293938406418645 570774997085014181400437)
                    ·
                      rfl

theorem cell23_3334741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3334741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334741 prefixEnd_3334741 := by exact prefixLift 3334741
  have htrace : WordTrace (prefixWord ++ tailWord_3334741) baseStart_3334741 baseEnd_3334741 := by
    simpa [prefixWord, tailWord_3334741, baseEnd_3334741] using wordTrace_append hprefix tailTrace_3334741
  have hstable : (prefixWord ++ tailWord_3334741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334741).length < 2 ^ (prefixWord ++ tailWord_3334741).sum := by decide
  have hdescent : baseEnd_3334741 < baseStart_3334741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334755 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3334755 : Nat := 118140960795 + 3334755 * 2 ^ 59
def prefixEnd_3334755 : Nat := 4983230072969 + 3 ^ 40 * 3334755 * 2
def baseEnd_3334755 : Nat := 1712332179984205489426247

theorem tailTrace_3334755 : CollatzResearch.WordTrace tailWord_3334755 prefixEnd_3334755 1712332179984205489426247 := by
  unfold tailWord_3334755
  simp only [CollatzResearch.WordTrace]
  refine ⟨121628507033759640656445719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81085671355839760437630479 121628507033759640656445719)
  ·
    refine ⟨182442760550639460984668579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121628507033759640656445719 182442760550639460984668579)
    ·
      refine ⟨273664140825959191477002869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182442760550639460984668579 273664140825959191477002869)
      ·
        refine ⟨25656013202433674200969019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273664140825959191477002869 25656013202433674200969019)
        ·
          refine ⟨38484019803650511301453529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25656013202433674200969019 38484019803650511301453529)
          ·
            refine ⟨28863014852737883476090147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38484019803650511301453529 28863014852737883476090147)
            ·
              refine ⟨43294522279106825214135221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28863014852737883476090147 43294522279106825214135221)
              ·
                refine ⟨4058861463666264863825177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43294522279106825214135221 4058861463666264863825177)
                ·
                  refine ⟨3044146097749698647868883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4058861463666264863825177 3044146097749698647868883)
                  ·
                    refine ⟨4566219146624547971803325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3044146097749698647868883 4566219146624547971803325)
                    ·
                      refine ⟨1712332179984205489426247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566219146624547971803325 1712332179984205489426247)
                      ·
                        rfl

theorem cell23_3334755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3334755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334755 prefixEnd_3334755 := by exact prefixLift 3334755
  have htrace : WordTrace (prefixWord ++ tailWord_3334755) baseStart_3334755 baseEnd_3334755 := by
    simpa [prefixWord, tailWord_3334755, baseEnd_3334755] using wordTrace_append hprefix tailTrace_3334755
  have hstable : (prefixWord ++ tailWord_3334755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334755).length < 2 ^ (prefixWord ++ tailWord_3334755).sum := by decide
  have hdescent : baseEnd_3334755 < baseStart_3334755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334761 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_3334761 : Nat := 118140960795 + 3334761 * 2 ^ 59
def prefixEnd_3334761 : Nat := 4983230072969 + 3 ^ 40 * 3334761 * 2
def baseEnd_3334761 : Nat := 1712335260868132465951219

theorem tailTrace_3334761 : CollatzResearch.WordTrace tailWord_3334761 prefixEnd_3334761 1712335260868132465951219 := by
  unfold tailWord_3334761
  simp only [CollatzResearch.WordTrace]
  refine ⟨121628725871737903681164137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81085817247825269120776091 121628725871737903681164137)
  ·
    refine ⟨91221544403803427760873103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121628725871737903681164137 91221544403803427760873103)
    ·
      refine ⟨136832316605705141641309655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91221544403803427760873103 136832316605705141641309655)
      ·
        refine ⟨205248474908557712461964483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136832316605705141641309655 205248474908557712461964483)
        ·
          refine ⟨307872712362836568692946725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205248474908557712461964483 307872712362836568692946725)
          ·
            refine ⟨57726133568031856629927511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307872712362836568692946725 57726133568031856629927511)
            ·
              refine ⟨86589200352047784944891267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57726133568031856629927511 86589200352047784944891267)
              ·
                refine ⟨129883800528071677417336901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86589200352047784944891267 129883800528071677417336901)
                ·
                  refine ⟨24353212599013439515750669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129883800528071677417336901 24353212599013439515750669)
                  ·
                    refine ⟨9132454724630039818406501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24353212599013439515750669 9132454724630039818406501)
                    ·
                      refine ⟨1712335260868132465951219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9132454724630039818406501 1712335260868132465951219)
                      ·
                        rfl

theorem cell23_3334761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_3334761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334761 prefixEnd_3334761 := by exact prefixLift 3334761
  have htrace : WordTrace (prefixWord ++ tailWord_3334761) baseStart_3334761 baseEnd_3334761 := by
    simpa [prefixWord, tailWord_3334761, baseEnd_3334761] using wordTrace_append hprefix tailTrace_3334761
  have hstable : (prefixWord ++ tailWord_3334761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334761).length < 2 ^ (prefixWord ++ tailWord_3334761).sum := by decide
  have hdescent : baseEnd_3334761 < baseStart_3334761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334778 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_3334778 : Nat := 118140960795 + 3334778 * 2 ^ 59
def prefixEnd_3334778 : Nat := 4983230072969 + 3 ^ 40 * 3334778 * 2
def baseEnd_3334778 : Nat := 1712343990039258899438641

theorem tailTrace_3334778 : CollatzResearch.WordTrace tailWord_3334778 prefixEnd_3334778 1712343990039258899438641 := by
  unfold tailWord_3334778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30407336478169078896133247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81086230608450877056355325 30407336478169078896133247)
  ·
    refine ⟨45611004717253618344199871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30407336478169078896133247 45611004717253618344199871)
    ·
      refine ⟨68416507075880427516299807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45611004717253618344199871 68416507075880427516299807)
      ·
        refine ⟨102624760613820641274449711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68416507075880427516299807 102624760613820641274449711)
        ·
          refine ⟨153937140920730961911674567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102624760613820641274449711 153937140920730961911674567)
          ·
            refine ⟨230905711381096442867511851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153937140920730961911674567 230905711381096442867511851)
            ·
              refine ⟨346358567071644664301267777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230905711381096442867511851 346358567071644664301267777)
              ·
                refine ⟨259768925303733498225950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346358567071644664301267777 259768925303733498225950833)
                ·
                  refine ⟨194826693977800123669463125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259768925303733498225950833 194826693977800123669463125)
                  ·
                    refine ⟨2283125320052345199251521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 194826693977800123669463125 2283125320052345199251521)
                    ·
                      refine ⟨1712343990039258899438641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283125320052345199251521 1712343990039258899438641)
                      ·
                        rfl

theorem cell23_3334778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_3334778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334778 prefixEnd_3334778 := by exact prefixLift 3334778
  have htrace : WordTrace (prefixWord ++ tailWord_3334778) baseStart_3334778 baseEnd_3334778 := by
    simpa [prefixWord, tailWord_3334778, baseEnd_3334778] using wordTrace_append hprefix tailTrace_3334778
  have hstable : (prefixWord ++ tailWord_3334778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334778).length < 2 ^ (prefixWord ++ tailWord_3334778).sum := by decide
  have hdescent : baseEnd_3334778 < baseStart_3334778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334788 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3334788 : Nat := 118140960795 + 3334788 * 2 ^ 59
def prefixEnd_3334788 : Nat := 4983230072969 + 3 ^ 40 * 3334788 * 2
def baseEnd_3334788 : Nat := 570783041615267953437865

theorem tailTrace_3334788 : CollatzResearch.WordTrace tailWord_3334788 prefixEnd_3334788 570783041615267953437865 := by
  unfold tailWord_3334788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60814855321320043646198509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81086473761760058194931345 60814855321320043646198509)
  ·
    refine ⟨22805570745495016367324441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60814855321320043646198509 22805570745495016367324441)
    ·
      refine ⟨17104178059121262275493331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22805570745495016367324441 17104178059121262275493331)
      ·
        refine ⟨25656267088681893413239997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17104178059121262275493331 25656267088681893413239997)
        ·
          refine ⟨9621100158255710029964999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25656267088681893413239997 9621100158255710029964999)
          ·
            refine ⟨14431650237383565044947499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9621100158255710029964999 14431650237383565044947499)
            ·
              refine ⟨21647475356075347567421249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14431650237383565044947499 21647475356075347567421249)
              ·
                refine ⟨16235606517056510675565937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21647475356075347567421249 16235606517056510675565937)
                ·
                  refine ⟨12176704887792383006674453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16235606517056510675565937 12176704887792383006674453)
                  ·
                    refine ⟨570783041615267953437865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12176704887792383006674453 570783041615267953437865)
                    ·
                      rfl

theorem cell23_3334788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3334788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334788 prefixEnd_3334788 := by exact prefixLift 3334788
  have htrace : WordTrace (prefixWord ++ tailWord_3334788) baseStart_3334788 baseEnd_3334788 := by
    simpa [prefixWord, tailWord_3334788, baseEnd_3334788] using wordTrace_append hprefix tailTrace_3334788
  have hstable : (prefixWord ++ tailWord_3334788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334788).length < 2 ^ (prefixWord ++ tailWord_3334788).sum := by decide
  have hdescent : baseEnd_3334788 < baseStart_3334788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334808 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3334808 : Nat := 118140960795 + 3334808 * 2 ^ 59
def prefixEnd_3334808 : Nat := 4983230072969 + 3 ^ 40 * 3334808 * 2
def baseEnd_3334808 : Nat := 1712359394458893782063503

theorem tailTrace_3334808 : CollatzResearch.WordTrace tailWord_3334808 prefixEnd_3334808 1712359394458893782063503 := by
  unfold tailWord_3334808
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815220051283815354062539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81086960068378420472083385 60815220051283815354062539)
  ·
    refine ⟨91222830076925723031093809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60815220051283815354062539 91222830076925723031093809)
    ·
      refine ⟨68417122557694292273320357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91222830076925723031093809 68417122557694292273320357)
      ·
        refine ⟨12828210479567679801247567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68417122557694292273320357 12828210479567679801247567)
        ·
          refine ⟨19242315719351519701871351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12828210479567679801247567 19242315719351519701871351)
          ·
            refine ⟨28863473579027279552807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19242315719351519701871351 28863473579027279552807027)
            ·
              refine ⟨43295210368540919329210541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28863473579027279552807027 43295210368540919329210541)
              ·
                refine ⟨16235703888202844748453953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43295210368540919329210541 16235703888202844748453953)
                ·
                  refine ⟨12176777916152133561340465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16235703888202844748453953 12176777916152133561340465)
                  ·
                    refine ⟨9132583437114100171005349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12176777916152133561340465 9132583437114100171005349)
                    ·
                      refine ⟨1712359394458893782063503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9132583437114100171005349 1712359394458893782063503)
                      ·
                        rfl

theorem cell23_3334808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3334808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334808 prefixEnd_3334808 := by exact prefixLift 3334808
  have htrace : WordTrace (prefixWord ++ tailWord_3334808) baseStart_3334808 baseEnd_3334808 := by
    simpa [prefixWord, tailWord_3334808, baseEnd_3334808] using wordTrace_append hprefix tailTrace_3334808
  have hstable : (prefixWord ++ tailWord_3334808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334808).length < 2 ^ (prefixWord ++ tailWord_3334808).sum := by decide
  have hdescent : baseEnd_3334808 < baseStart_3334808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334812 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_3334812 : Nat := 118140960795 + 3334812 * 2 ^ 59
def prefixEnd_3334812 : Nat := 4983230072969 + 3 ^ 40 * 3334812 * 2
def baseEnd_3334812 : Nat := 1712361448381511766413485

theorem tailTrace_3334812 : CollatzResearch.WordTrace tailWord_3334812 prefixEnd_3334812 1712361448381511766413485 := by
  unfold tailWord_3334812
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815292997276569695635345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81087057329702092927513793 60815292997276569695635345)
  ·
    refine ⟨45611469747957427271726509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60815292997276569695635345 45611469747957427271726509)
    ·
      refine ⟨17104301155484035226897441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45611469747957427271726509 17104301155484035226897441)
      ·
        refine ⟨12828225866613026420173081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17104301155484035226897441 12828225866613026420173081)
        ·
          refine ⟨9621169399959769815129811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12828225866613026420173081 9621169399959769815129811)
          ·
            refine ⟨14431754099939654722694717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9621169399959769815129811 14431754099939654722694717)
            ·
              refine ⟨5411907787477370521010519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14431754099939654722694717 5411907787477370521010519)
              ·
                refine ⟨8117861681216055781515779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411907787477370521010519 8117861681216055781515779)
                ·
                  refine ⟨12176792521824083672273669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8117861681216055781515779 12176792521824083672273669)
                  ·
                    refine ⟨2283148597842015688551313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12176792521824083672273669 2283148597842015688551313)
                    ·
                      refine ⟨1712361448381511766413485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283148597842015688551313 1712361448381511766413485)
                      ·
                        rfl

theorem cell23_3334812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_3334812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334812 prefixEnd_3334812 := by exact prefixLift 3334812
  have htrace : WordTrace (prefixWord ++ tailWord_3334812) baseStart_3334812 baseEnd_3334812 := by
    simpa [prefixWord, tailWord_3334812, baseEnd_3334812] using wordTrace_append hprefix tailTrace_3334812
  have hstable : (prefixWord ++ tailWord_3334812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334812).length < 2 ^ (prefixWord ++ tailWord_3334812).sum := by decide
  have hdescent : baseEnd_3334812 < baseStart_3334812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334835 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 5]
def baseStart_3334835 : Nat := 118140960795 + 3334835 * 2 ^ 59
def prefixEnd_3334835 : Nat := 4983230072969 + 3 ^ 40 * 3334835 * 2
def baseEnd_3334835 : Nat := 190263695381840575158431

theorem tailTrace_3334835 : CollatzResearch.WordTrace tailWord_3334835 prefixEnd_3334835 190263695381840575158431 := by
  unfold tailWord_3334835
  simp only [CollatzResearch.WordTrace]
  refine ⟨121631424873469814319357959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81087616582313209546238639 121631424873469814319357959)
  ·
    refine ⟨182447137310204721479036939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121631424873469814319357959 182447137310204721479036939)
    ·
      refine ⟨273670705965307082218555409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182447137310204721479036939 273670705965307082218555409)
      ·
        refine ⟨205253029473980311663916557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273670705965307082218555409 205253029473980311663916557)
        ·
          refine ⟨76969886052742616873968709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205253029473980311663916557 76969886052742616873968709)
          ·
            refine ⟨14431853634889240663869133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76969886052742616873968709 14431853634889240663869133)
            ·
              refine ⟨5411945113083465248950925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14431853634889240663869133 5411945113083465248950925)
              ·
                refine ⟨2029479417406299468356597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5411945113083465248950925 2029479417406299468356597)
                ·
                  refine ⟨190263695381840575158431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029479417406299468356597 190263695381840575158431)
                  ·
                    rfl

theorem cell23_3334835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 5].length) (baseStart_3334835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334835 prefixEnd_3334835 := by exact prefixLift 3334835
  have htrace : WordTrace (prefixWord ++ tailWord_3334835) baseStart_3334835 baseEnd_3334835 := by
    simpa [prefixWord, tailWord_3334835, baseEnd_3334835] using wordTrace_append hprefix tailTrace_3334835
  have hstable : (prefixWord ++ tailWord_3334835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334835).length < 2 ^ (prefixWord ++ tailWord_3334835).sum := by decide
  have hdescent : baseEnd_3334835 < baseStart_3334835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334848 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_3334848 : Nat := 118140960795 + 3334848 * 2 ^ 59
def prefixEnd_3334848 : Nat := 4983230072969 + 3 ^ 40 * 3334848 * 2
def baseEnd_3334848 : Nat := 570793311228357875187773

theorem tailTrace_3334848 : CollatzResearch.WordTrace tailWord_3334848 prefixEnd_3334848 570793311228357875187773 := by
  unfold tailWord_3334848
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815949511211358769790599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81087932681615145026387465 60815949511211358769790599)
  ·
    refine ⟨91223924266817038154685899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60815949511211358769790599 91223924266817038154685899)
    ·
      refine ⟨136835886400225557232028849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91223924266817038154685899 136835886400225557232028849)
      ·
        refine ⟨102626914800169167924021637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136835886400225557232028849 102626914800169167924021637)
        ·
          refine ⟨19242546525031718985754057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102626914800169167924021637 19242546525031718985754057)
          ·
            refine ⟨14431909893773789239315543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19242546525031718985754057 14431909893773789239315543)
            ·
              refine ⟨21647864840660683858973315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14431909893773789239315543 21647864840660683858973315)
              ·
                refine ⟨32471797260991025788459973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21647864840660683858973315 32471797260991025788459973)
                ·
                  refine ⟨6088461986435817335336245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32471797260991025788459973 6088461986435817335336245)
                  ·
                    refine ⟨570793311228357875187773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6088461986435817335336245 570793311228357875187773)
                    ·
                      rfl

theorem cell23_3334848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_3334848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334848 prefixEnd_3334848 := by exact prefixLift 3334848
  have htrace : WordTrace (prefixWord ++ tailWord_3334848) baseStart_3334848 baseEnd_3334848 := by
    simpa [prefixWord, tailWord_3334848, baseEnd_3334848] using wordTrace_append hprefix tailTrace_3334848
  have hstable : (prefixWord ++ tailWord_3334848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334848).length < 2 ^ (prefixWord ++ tailWord_3334848).sum := by decide
  have hdescent : baseEnd_3334848 < baseStart_3334848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334851 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8]
def baseStart_3334851 : Nat := 118140960795 + 3334851 * 2 ^ 59
def prefixEnd_3334851 : Nat := 4983230072969 + 3 ^ 40 * 3334851 * 2
def baseEnd_3334851 : Nat := 1712381474127037113825805

theorem tailTrace_3334851 : CollatzResearch.WordTrace tailWord_3334851 prefixEnd_3334851 1712381474127037113825805 := by
  unfold tailWord_3334851
  simp only [CollatzResearch.WordTrace]
  refine ⟨121632008441411849051940407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81088005627607899367960271 121632008441411849051940407)
  ·
    refine ⟨182448012662117773577910611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121632008441411849051940407 182448012662117773577910611)
    ·
      refine ⟨273672018993176660366865917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182448012662117773577910611 273672018993176660366865917)
      ·
        refine ⟨102627007122441247637574719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273672018993176660366865917 102627007122441247637574719)
        ·
          refine ⟨153940510683661871456362079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102627007122441247637574719 153940510683661871456362079)
          ·
            refine ⟨230910766025492807184543119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153940510683661871456362079 230910766025492807184543119)
            ·
              refine ⟨346366149038239210776814679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230910766025492807184543119 346366149038239210776814679)
              ·
                refine ⟨519549223557358816165222019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346366149038239210776814679 519549223557358816165222019)
                ·
                  refine ⟨779323835336038224247833029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519549223557358816165222019 779323835336038224247833029)
                  ·
                    refine ⟨146123219125507167046468693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 779323835336038224247833029 146123219125507167046468693)
                    ·
                      refine ⟨1712381474127037113825805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146123219125507167046468693 1712381474127037113825805)
                      ·
                        rfl

theorem cell23_3334851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_3334851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334851 prefixEnd_3334851 := by exact prefixLift 3334851
  have htrace : WordTrace (prefixWord ++ tailWord_3334851) baseStart_3334851 baseEnd_3334851 := by
    simpa [prefixWord, tailWord_3334851, baseEnd_3334851] using wordTrace_append hprefix tailTrace_3334851
  have hstable : (prefixWord ++ tailWord_3334851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334851).length < 2 ^ (prefixWord ++ tailWord_3334851).sum := by decide
  have hdescent : baseEnd_3334851 < baseStart_3334851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334858 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_3334858 : Nat := 118140960795 + 3334858 * 2 ^ 59
def prefixEnd_3334858 : Nat := 4983230072969 + 3 ^ 40 * 3334858 * 2
def baseEnd_3334858 : Nat := 1712385068491618586438273

theorem tailTrace_3334858 : CollatzResearch.WordTrace tailWord_3334858 prefixEnd_3334858 1712385068491618586438273 := by
  unfold tailWord_3334858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30408065938096622311861307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81088175834924326164963485 30408065938096622311861307)
  ·
    refine ⟨45612098907144933467791961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30408065938096622311861307 45612098907144933467791961)
    ·
      refine ⟨34209074180358700100843971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45612098907144933467791961 34209074180358700100843971)
      ·
        refine ⟨51313611270538050151265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34209074180358700100843971 51313611270538050151265957)
        ·
          refine ⟨9621302113225884403362367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51313611270538050151265957 9621302113225884403362367)
          ·
            refine ⟨14431953169838826605043551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9621302113225884403362367 14431953169838826605043551)
            ·
              refine ⟨21647929754758239907565327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14431953169838826605043551 21647929754758239907565327)
              ·
                refine ⟨32471894632137359861347991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21647929754758239907565327 32471894632137359861347991)
                ·
                  refine ⟨48707841948206039792021987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32471894632137359861347991 48707841948206039792021987)
                  ·
                    refine ⟨73061762922309059688032981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48707841948206039792021987 73061762922309059688032981)
                    ·
                      refine ⟨1712385068491618586438273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73061762922309059688032981 1712385068491618586438273)
                      ·
                        rfl

theorem cell23_3334858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_3334858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334858 prefixEnd_3334858 := by exact prefixLift 3334858
  have htrace : WordTrace (prefixWord ++ tailWord_3334858) baseStart_3334858 baseEnd_3334858 := by
    simpa [prefixWord, tailWord_3334858, baseEnd_3334858] using wordTrace_append hprefix tailTrace_3334858
  have hstable : (prefixWord ++ tailWord_3334858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334858).length < 2 ^ (prefixWord ++ tailWord_3334858).sum := by decide
  have hdescent : baseEnd_3334858 < baseStart_3334858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334885 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3334885 : Nat := 118140960795 + 3334885 * 2 ^ 59
def prefixEnd_3334885 : Nat := 4983230072969 + 3 ^ 40 * 3334885 * 2
def baseEnd_3334885 : Nat := 1712398932469289980800649

theorem tailTrace_3334885 : CollatzResearch.WordTrace tailWord_3334885 prefixEnd_3334885 1712398932469289980800649 := by
  unfold tailWord_3334885
  simp only [CollatzResearch.WordTrace]
  refine ⟨121633248523288672858678109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81088832348859115239118739 121633248523288672858678109)
  ·
    refine ⟨45612468196233252322004291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121633248523288672858678109 45612468196233252322004291)
    ·
      refine ⟨68418702294349878483006437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45612468196233252322004291 68418702294349878483006437)
      ·
        refine ⟨12828506680190602215563707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68418702294349878483006437 12828506680190602215563707)
        ·
          refine ⟨19242760020285903323345561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12828506680190602215563707 19242760020285903323345561)
          ·
            refine ⟨14432070015214427492509171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19242760020285903323345561 14432070015214427492509171)
            ·
              refine ⟨21648105022821641238763757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14432070015214427492509171 21648105022821641238763757)
              ·
                refine ⟨8118039383558115464536409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21648105022821641238763757 8118039383558115464536409)
                ·
                  refine ⟨6088529537668586598402307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118039383558115464536409 6088529537668586598402307)
                  ·
                    refine ⟨9132794306502879897603461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6088529537668586598402307 9132794306502879897603461)
                    ·
                      refine ⟨1712398932469289980800649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9132794306502879897603461 1712398932469289980800649)
                      ·
                        rfl

theorem cell23_3334885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3334885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334885 prefixEnd_3334885 := by exact prefixLift 3334885
  have htrace : WordTrace (prefixWord ++ tailWord_3334885) baseStart_3334885 baseEnd_3334885 := by
    simpa [prefixWord, tailWord_3334885, baseEnd_3334885] using wordTrace_append hprefix tailTrace_3334885
  have hstable : (prefixWord ++ tailWord_3334885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334885).length < 2 ^ (prefixWord ++ tailWord_3334885).sum := by decide
  have hdescent : baseEnd_3334885 < baseStart_3334885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334902 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3334902 : Nat := 118140960795 + 3334902 * 2 ^ 59
def prefixEnd_3334902 : Nat := 4983230072969 + 3 ^ 40 * 3334902 * 2
def baseEnd_3334902 : Nat := 1712407661640416414288071

theorem tailTrace_3334902 : CollatzResearch.WordTrace tailWord_3334902 prefixEnd_3334902 1712407661640416414288071 := by
  unfold tailWord_3334902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602116785264192797627935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81089245709484723174697973 7602116785264192797627935)
  ·
    refine ⟨11403175177896289196441903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7602116785264192797627935 11403175177896289196441903)
    ·
      refine ⟨17104762766844433794662855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11403175177896289196441903 17104762766844433794662855)
      ·
        refine ⟨25657144150266650691994283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17104762766844433794662855 25657144150266650691994283)
        ·
          refine ⟨38485716225399976037991425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25657144150266650691994283 38485716225399976037991425)
          ·
            refine ⟨28864287169049982028493569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38485716225399976037991425 28864287169049982028493569)
            ·
              refine ⟨21648215376787486521370177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28864287169049982028493569 21648215376787486521370177)
              ·
                refine ⟨16236161532590614891027633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21648215376787486521370177 16236161532590614891027633)
                ·
                  refine ⟨12177121149442961168270725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16236161532590614891027633 12177121149442961168270725)
                  ·
                    refine ⟨2283210215520555219050761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12177121149442961168270725 2283210215520555219050761)
                    ·
                      refine ⟨1712407661640416414288071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283210215520555219050761 1712407661640416414288071)
                      ·
                        rfl

theorem cell23_3334902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3334902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334902 prefixEnd_3334902 := by exact prefixLift 3334902
  have htrace : WordTrace (prefixWord ++ tailWord_3334902) baseStart_3334902 baseEnd_3334902 := by
    simpa [prefixWord, tailWord_3334902, baseEnd_3334902] using wordTrace_append hprefix tailTrace_3334902
  have hstable : (prefixWord ++ tailWord_3334902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334902).length < 2 ^ (prefixWord ++ tailWord_3334902).sum := by decide
  have hdescent : baseEnd_3334902 < baseStart_3334902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334952 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3334952 : Nat := 118140960795 + 3334952 * 2 ^ 59
def prefixEnd_3334952 : Nat := 4983230072969 + 3 ^ 40 * 3334952 * 2
def baseEnd_3334952 : Nat := 1712433335673141218662841

theorem tailTrace_3334952 : CollatzResearch.WordTrace tailWord_3334952 prefixEnd_3334952 1712433335673141218662841 := by
  unfold tailWord_3334952
  simp only [CollatzResearch.WordTrace]
  refine ⟨60817846107022971650683555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81090461476030628867578073 60817846107022971650683555)
  ·
    refine ⟨91226769160534457476025333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60817846107022971650683555 91226769160534457476025333)
    ·
      refine ⟨8552509608800105388377375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91226769160534457476025333 8552509608800105388377375)
      ·
        refine ⟨12828764413200158082566063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8552509608800105388377375 12828764413200158082566063)
        ·
          refine ⟨19243146619800237123849095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12828764413200158082566063 19243146619800237123849095)
          ·
            refine ⟨28864719929700355685773643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19243146619800237123849095 28864719929700355685773643)
            ·
              refine ⟨43297079894550533528660465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28864719929700355685773643 43297079894550533528660465)
              ·
                refine ⟨32472809920912900146495349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43297079894550533528660465 32472809920912900146495349)
                ·
                  refine ⟨3044325930085584388733939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32472809920912900146495349 3044325930085584388733939)
                  ·
                    refine ⟨4566488895128376583100909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3044325930085584388733939 4566488895128376583100909)
                    ·
                      refine ⟨1712433335673141218662841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566488895128376583100909 1712433335673141218662841)
                      ·
                        rfl

theorem cell23_3334952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3334952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334952 prefixEnd_3334952 := by exact prefixLift 3334952
  have htrace : WordTrace (prefixWord ++ tailWord_3334952) baseStart_3334952 baseEnd_3334952 := by
    simpa [prefixWord, tailWord_3334952, baseEnd_3334952] using wordTrace_append hprefix tailTrace_3334952
  have hstable : (prefixWord ++ tailWord_3334952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334952).length < 2 ^ (prefixWord ++ tailWord_3334952).sum := by decide
  have hdescent : baseEnd_3334952 < baseStart_3334952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334962 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2]
def baseStart_3334962 : Nat := 118140960795 + 3334962 * 2 ^ 59
def prefixEnd_3334962 : Nat := 4983230072969 + 3 ^ 40 * 3334962 * 2
def baseEnd_3334962 : Nat := 1712438470479686179537795

theorem tailTrace_3334962 : CollatzResearch.WordTrace tailWord_3334962 prefixEnd_3334962 1712438470479686179537795 := by
  unfold tailWord_3334962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30409014236002428752307785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81090704629339810006154093 30409014236002428752307785)
  ·
    refine ⟨22806760677001821564230839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30409014236002428752307785 22806760677001821564230839)
    ·
      refine ⟨34210141015502732346346259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22806760677001821564230839 34210141015502732346346259)
      ·
        refine ⟨51315211523254098519519389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34210141015502732346346259 51315211523254098519519389)
        ·
          refine ⟨19243204321220286944819771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51315211523254098519519389 19243204321220286944819771)
          ·
            refine ⟨28864806481830430417229657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19243204321220286944819771 28864806481830430417229657)
            ·
              refine ⟨21648604861372822812922243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28864806481830430417229657 21648604861372822812922243)
              ·
                refine ⟨32472907292059234219383365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21648604861372822812922243 32472907292059234219383365)
                ·
                  refine ⟨6088670117261106416134381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32472907292059234219383365 6088670117261106416134381)
                  ·
                    refine ⟨2283251293972914906050393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6088670117261106416134381 2283251293972914906050393)
                    ·
                      refine ⟨1712438470479686179537795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283251293972914906050393 1712438470479686179537795)
                      ·
                        rfl

theorem cell23_3334962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_3334962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334962 prefixEnd_3334962 := by exact prefixLift 3334962
  have htrace : WordTrace (prefixWord ++ tailWord_3334962) baseStart_3334962 baseEnd_3334962 := by
    simpa [prefixWord, tailWord_3334962, baseEnd_3334962] using wordTrace_append hprefix tailTrace_3334962
  have hstable : (prefixWord ++ tailWord_3334962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334962).length < 2 ^ (prefixWord ++ tailWord_3334962).sum := by decide
  have hdescent : baseEnd_3334962 < baseStart_3334962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334985 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_3334985 : Nat := 118140960795 + 3334985 * 2 ^ 59
def prefixEnd_3334985 : Nat := 4983230072969 + 3 ^ 40 * 3334985 * 2
def baseEnd_3334985 : Nat := 570816760178246529850063

theorem tailTrace_3334985 : CollatzResearch.WordTrace tailWord_3334985 prefixEnd_3334985 570816760178246529850063 := by
  unfold tailWord_3334985
  simp only [CollatzResearch.WordTrace]
  refine ⟨121636895822926389937318409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81091263881950926624878939 121636895822926389937318409)
  ·
    refine ⟨91227671867194792452988807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121636895822926389937318409 91227671867194792452988807)
    ·
      refine ⟨136841507800792188679483211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91227671867194792452988807 136841507800792188679483211)
      ·
        refine ⟨205262261701188283019224817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136841507800792188679483211 205262261701188283019224817)
        ·
          refine ⟨153946696275891212264418613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205262261701188283019224817 153946696275891212264418613)
          ·
            refine ⟨14432502775864801149789245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153946696275891212264418613 14432502775864801149789245)
            ·
              refine ⟨5412188540949300431170967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14432502775864801149789245 5412188540949300431170967)
              ·
                refine ⟨8118282811423950646756451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412188540949300431170967 8118282811423950646756451)
                ·
                  refine ⟨12177424217135925970134677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118282811423950646756451 12177424217135925970134677)
                  ·
                    refine ⟨570816760178246529850063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12177424217135925970134677 570816760178246529850063)
                    ·
                      rfl

theorem cell23_3334985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_3334985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334985 prefixEnd_3334985 := by exact prefixLift 3334985
  have htrace : WordTrace (prefixWord ++ tailWord_3334985) baseStart_3334985 baseEnd_3334985 := by
    simpa [prefixWord, tailWord_3334985, baseEnd_3334985] using wordTrace_append hprefix tailTrace_3334985
  have hstable : (prefixWord ++ tailWord_3334985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334985).length < 2 ^ (prefixWord ++ tailWord_3334985).sum := by decide
  have hdescent : baseEnd_3334985 < baseStart_3334985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3334995 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3]
def baseStart_3334995 : Nat := 118140960795 + 3334995 * 2 ^ 59
def prefixEnd_3334995 : Nat := 4983230072969 + 3 ^ 40 * 3334995 * 2
def baseEnd_3334995 : Nat := 1712455415341284550425143

theorem tailTrace_3334995 : CollatzResearch.WordTrace tailWord_3334995 prefixEnd_3334995 1712455415341284550425143 := by
  unfold tailWord_3334995
  simp only [CollatzResearch.WordTrace]
  refine ⟨121637260552890161645182439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81091507035260107763454959 121637260552890161645182439)
  ·
    refine ⟨182455890829335242467773659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121637260552890161645182439 182455890829335242467773659)
    ·
      refine ⟨273683836244002863701660489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182455890829335242467773659 273683836244002863701660489)
      ·
        refine ⟨205262877183002147776245367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273683836244002863701660489 205262877183002147776245367)
        ·
          refine ⟨307894315774503221664368051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205262877183002147776245367 307894315774503221664368051)
          ·
            refine ⟨461841473661754832496552077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307894315774503221664368051 461841473661754832496552077)
            ·
              refine ⟨173190552623158062186207029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461841473661754832496552077 173190552623158062186207029)
              ·
                refine ⟨16236614308421068329956909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173190552623158062186207029 16236614308421068329956909)
                ·
                  refine ⟨6088730365657900623733841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16236614308421068329956909 6088730365657900623733841)
                  ·
                    refine ⟨4566547774243425467800381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088730365657900623733841 4566547774243425467800381)
                    ·
                      refine ⟨1712455415341284550425143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566547774243425467800381 1712455415341284550425143)
                      ·
                        rfl

theorem cell23_3334995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_3334995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3334995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3334995 prefixEnd_3334995 := by exact prefixLift 3334995
  have htrace : WordTrace (prefixWord ++ tailWord_3334995) baseStart_3334995 baseEnd_3334995 := by
    simpa [prefixWord, tailWord_3334995, baseEnd_3334995] using wordTrace_append hprefix tailTrace_3334995
  have hstable : (prefixWord ++ tailWord_3334995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3334995).length < 2 ^ (prefixWord ++ tailWord_3334995).sum := by decide
  have hdescent : baseEnd_3334995 < baseStart_3334995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3334995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335012 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_3335012 : Nat := 118140960795 + 3335012 * 2 ^ 59
def prefixEnd_3335012 : Nat := 4983230072969 + 3 ^ 40 * 3335012 * 2
def baseEnd_3335012 : Nat := 1712464144512410983912565

theorem tailTrace_3335012 : CollatzResearch.WordTrace tailWord_3335012 prefixEnd_3335012 1712464144512410983912565 := by
  unfold tailWord_3335012
  simp only [CollatzResearch.WordTrace]
  refine ⟨60818940296914286774275645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81091920395885715699034193 60818940296914286774275645)
  ·
    refine ⟨22807102611342857540353367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60818940296914286774275645 22807102611342857540353367)
    ·
      refine ⟨34210653917014286310530051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22807102611342857540353367 34210653917014286310530051)
      ·
        refine ⟨51315980875521429465795077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34210653917014286310530051 51315980875521429465795077)
        ·
          refine ⟨9621746414160268024836577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51315980875521429465795077 9621746414160268024836577)
          ·
            refine ⟨7216309810620201018627433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9621746414160268024836577 7216309810620201018627433)
            ·
              refine ⟨5412232357965150763970575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216309810620201018627433 5412232357965150763970575)
              ·
                refine ⟨8118348536947726145955863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412232357965150763970575 8118348536947726145955863)
                ·
                  refine ⟨12177522805421589218933795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118348536947726145955863 12177522805421589218933795)
                  ·
                    refine ⟨18266284208132383828400693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12177522805421589218933795 18266284208132383828400693)
                    ·
                      refine ⟨1712464144512410983912565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18266284208132383828400693 1712464144512410983912565)
                      ·
                        rfl

theorem cell23_3335012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_3335012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335012 prefixEnd_3335012 := by exact prefixLift 3335012
  have htrace : WordTrace (prefixWord ++ tailWord_3335012) baseStart_3335012 baseEnd_3335012 := by
    simpa [prefixWord, tailWord_3335012, baseEnd_3335012] using wordTrace_append hprefix tailTrace_3335012
  have hstable : (prefixWord ++ tailWord_3335012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335012).length < 2 ^ (prefixWord ++ tailWord_3335012).sum := by decide
  have hdescent : baseEnd_3335012 < baseStart_3335012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335015 : List Nat := [1, 1, 5, 1, 2, 4, 9]
def baseStart_3335015 : Nat := 118140960795 + 3335015 * 2 ^ 59
def prefixEnd_3335015 : Nat := 4983230072969 + 3 ^ 40 * 3335015 * 2
def baseEnd_3335015 : Nat := 21141551666103388545371

theorem tailTrace_3335015 : CollatzResearch.WordTrace tailWord_3335015 prefixEnd_3335015 21141551666103388545371 := by
  unfold tailWord_3335015
  simp only [CollatzResearch.WordTrace]
  refine ⟨121637990012817705060910499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81091993341878470040606999 121637990012817705060910499)
  ·
    refine ⟨182456985019226557591365749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121637990012817705060910499 182456985019226557591365749)
    ·
      refine ⟨17105342345552489774190539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182456985019226557591365749 17105342345552489774190539)
      ·
        refine ⟨25658013518328734661285809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17105342345552489774190539 25658013518328734661285809)
        ·
          refine ⟨19243510138746550995964357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25658013518328734661285809 19243510138746550995964357)
          ·
            refine ⟨3608158151014978311743317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19243510138746550995964357 3608158151014978311743317)
            ·
              refine ⟨21141551666103388545371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3608158151014978311743317 21141551666103388545371)
              ·
                rfl

theorem cell23_3335015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 9].length) (baseStart_3335015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335015 prefixEnd_3335015 := by exact prefixLift 3335015
  have htrace : WordTrace (prefixWord ++ tailWord_3335015) baseStart_3335015 baseEnd_3335015 := by
    simpa [prefixWord, tailWord_3335015, baseEnd_3335015] using wordTrace_append hprefix tailTrace_3335015
  have hstable : (prefixWord ++ tailWord_3335015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335015).length < 2 ^ (prefixWord ++ tailWord_3335015).sum := by decide
  have hdescent : baseEnd_3335015 < baseStart_3335015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335026 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3335026 : Nat := 118140960795 + 3335026 * 2 ^ 59
def prefixEnd_3335026 : Nat := 4983230072969 + 3 ^ 40 * 3335026 * 2
def baseEnd_3335026 : Nat := 1712471333241573929137501

theorem tailTrace_3335026 : CollatzResearch.WordTrace tailWord_3335026 prefixEnd_3335026 1712471333241573929137501 := by
  unfold tailWord_3335026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30409597803944463484890233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81092260810518569293040621 30409597803944463484890233)
  ·
    refine ⟨22807198352958347613667675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30409597803944463484890233 22807198352958347613667675)
    ·
      refine ⟨34210797529437521420501513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22807198352958347613667675 34210797529437521420501513)
      ·
        refine ⟨25658098147078141065376135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34210797529437521420501513 25658098147078141065376135)
        ·
          refine ⟨38487147220617211598064203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25658098147078141065376135 38487147220617211598064203)
          ·
            refine ⟨57730720830925817397096305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38487147220617211598064203 57730720830925817397096305)
            ·
              refine ⟨43298040623194363047822229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57730720830925817397096305 43298040623194363047822229)
              ·
                refine ⟨2029595654212235767866667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43298040623194363047822229 2029595654212235767866667)
                ·
                  refine ⟨3044393481318353651800001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029595654212235767866667 3044393481318353651800001)
                  ·
                    refine ⟨2283295110988765238850001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3044393481318353651800001 2283295110988765238850001)
                    ·
                      refine ⟨1712471333241573929137501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283295110988765238850001 1712471333241573929137501)
                      ·
                        rfl

theorem cell23_3335026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3335026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335026 prefixEnd_3335026 := by exact prefixLift 3335026
  have htrace : WordTrace (prefixWord ++ tailWord_3335026) baseStart_3335026 baseEnd_3335026 := by
    simpa [prefixWord, tailWord_3335026, baseEnd_3335026] using wordTrace_append hprefix tailTrace_3335026
  have hstable : (prefixWord ++ tailWord_3335026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335026).length < 2 ^ (prefixWord ++ tailWord_3335026).sum := by decide
  have hdescent : baseEnd_3335026 < baseStart_3335026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335095 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_3335095 : Nat := 118140960795 + 3335095 * 2 ^ 59
def prefixEnd_3335095 : Nat := 4983230072969 + 3 ^ 40 * 3335095 * 2
def baseEnd_3335095 : Nat := 1712506763406734159174683

theorem tailTrace_3335095 : CollatzResearch.WordTrace tailWord_3335095 prefixEnd_3335095 1712506763406734159174683 := by
  unfold tailWord_3335095
  simp only [CollatzResearch.WordTrace]
  refine ⟨121640907852527878723822739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81093938568351919149215159 121640907852527878723822739)
  ·
    refine ⟨182461361778791818085734109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121640907852527878723822739 182461361778791818085734109)
    ·
      refine ⟨68423010667046931782150291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182461361778791818085734109 68423010667046931782150291)
      ·
        refine ⟨102634516000570397673225437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68423010667046931782150291 102634516000570397673225437)
        ·
          refine ⟨38487943500213899127459539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102634516000570397673225437 38487943500213899127459539)
          ·
            refine ⟨57731915250320848691189309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38487943500213899127459539 57731915250320848691189309)
            ·
              refine ⟨21649468218870318259195991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57731915250320848691189309 21649468218870318259195991)
              ·
                refine ⟨32474202328305477388793987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21649468218870318259195991 32474202328305477388793987)
                ·
                  refine ⟨48711303492458216083190981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32474202328305477388793987 48711303492458216083190981)
                  ·
                    refine ⟨9133369404835915515598309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48711303492458216083190981 9133369404835915515598309)
                    ·
                      refine ⟨1712506763406734159174683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9133369404835915515598309 1712506763406734159174683)
                      ·
                        rfl

theorem cell23_3335095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_3335095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335095 prefixEnd_3335095 := by exact prefixLift 3335095
  have htrace : WordTrace (prefixWord ++ tailWord_3335095) baseStart_3335095 baseEnd_3335095 := by
    simpa [prefixWord, tailWord_3335095, baseEnd_3335095] using wordTrace_append hprefix tailTrace_3335095
  have hstable : (prefixWord ++ tailWord_3335095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335095).length < 2 ^ (prefixWord ++ tailWord_3335095).sum := by decide
  have hdescent : baseEnd_3335095 < baseStart_3335095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335102 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_3335102 : Nat := 118140960795 + 3335102 * 2 ^ 59
def prefixEnd_3335102 : Nat := 4983230072969 + 3 ^ 40 * 3335102 * 2
def baseEnd_3335102 : Nat := 1712510357771315631787151

theorem tailTrace_3335102 : CollatzResearch.WordTrace tailWord_3335102 prefixEnd_3335102 1712510357771315631787151 := by
  unfold tailWord_3335102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205145395437814864915945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81094108775668345946218373 15205145395437814864915945)
  ·
    refine ⟨11403859046578361148686959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15205145395437814864915945 11403859046578361148686959)
    ·
      refine ⟨17105788569867541723030439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11403859046578361148686959 17105788569867541723030439)
      ·
        refine ⟨25658682854801312584545659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17105788569867541723030439 25658682854801312584545659)
        ·
          refine ⟨38488024282201968876818489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25658682854801312584545659 38488024282201968876818489)
          ·
            refine ⟨28866018211651476657613867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38488024282201968876818489 28866018211651476657613867)
            ·
              refine ⟨43299027317477214986420801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28866018211651476657613867 43299027317477214986420801)
              ·
                refine ⟨32474270488107911239815601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43299027317477214986420801 32474270488107911239815601)
                ·
                  refine ⟨24355702866080933429861701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32474270488107911239815601 24355702866080933429861701)
                  ·
                    refine ⟨4566694287390175018099069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24355702866080933429861701 4566694287390175018099069)
                    ·
                      refine ⟨1712510357771315631787151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4566694287390175018099069 1712510357771315631787151)
                      ·
                        rfl

theorem cell23_3335102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_3335102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335102 prefixEnd_3335102 := by exact prefixLift 3335102
  have htrace : WordTrace (prefixWord ++ tailWord_3335102) baseStart_3335102 baseEnd_3335102 := by
    simpa [prefixWord, tailWord_3335102, baseEnd_3335102] using wordTrace_append hprefix tailTrace_3335102
  have hstable : (prefixWord ++ tailWord_3335102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335102).length < 2 ^ (prefixWord ++ tailWord_3335102).sum := by decide
  have hdescent : baseEnd_3335102 < baseStart_3335102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335133 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_3335133 : Nat := 118140960795 + 3335133 * 2 ^ 59
def prefixEnd_3335133 : Nat := 4983230072969 + 3 ^ 40 * 3335133 * 2
def baseEnd_3335133 : Nat := 1712526275671605010499509

theorem tailTrace_3335133 : CollatzResearch.WordTrace tailWord_3335133 prefixEnd_3335133 1712526275671605010499509 := by
  unfold tailWord_3335133
  simp only [CollatzResearch.WordTrace]
  refine ⟨121642293826390211213706053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81094862550926807475804035 121642293826390211213706053)
  ·
    refine ⟨22807930092448164602569885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121642293826390211213706053 22807930092448164602569885)
    ·
      refine ⟨8552973784668061725963707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22807930092448164602569885 8552973784668061725963707)
      ·
        refine ⟨12829460677002092588945561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8552973784668061725963707 12829460677002092588945561)
        ·
          refine ⟨9622095507751569441709171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12829460677002092588945561 9622095507751569441709171)
          ·
            refine ⟨14433143261627354162563757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9622095507751569441709171 14433143261627354162563757)
            ·
              refine ⟨5412428723110257810961409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14433143261627354162563757 5412428723110257810961409)
              ·
                refine ⟨4059321542332693358221057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412428723110257810961409 4059321542332693358221057)
                ·
                  refine ⟨3044491156749520018665793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4059321542332693358221057 3044491156749520018665793)
                  ·
                    refine ⟨2283368367562140013999345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3044491156749520018665793 2283368367562140013999345)
                    ·
                      refine ⟨1712526275671605010499509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283368367562140013999345 1712526275671605010499509)
                      ·
                        rfl

theorem cell23_3335133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_3335133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335133 prefixEnd_3335133 := by exact prefixLift 3335133
  have htrace : WordTrace (prefixWord ++ tailWord_3335133) baseStart_3335133 baseEnd_3335133 := by
    simpa [prefixWord, tailWord_3335133, baseEnd_3335133] using wordTrace_append hprefix tailTrace_3335133
  have hstable : (prefixWord ++ tailWord_3335133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335133).length < 2 ^ (prefixWord ++ tailWord_3335133).sum := by decide
  have hdescent : baseEnd_3335133 < baseStart_3335133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335150 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_3335150 : Nat := 118140960795 + 3335150 * 2 ^ 59
def prefixEnd_3335150 : Nat := 4983230072969 + 3 ^ 40 * 3335150 * 2
def baseEnd_3335150 : Nat := 1712535004842731443986931

theorem tailTrace_3335150 : CollatzResearch.WordTrace tailWord_3335150 prefixEnd_3335150 1712535004842731443986931 := by
  unfold tailWord_3335150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205364233416077889634363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81095275911552415411383269 15205364233416077889634363)
  ·
    refine ⟨22808046350124116834451545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15205364233416077889634363 22808046350124116834451545)
    ·
      refine ⟨17106034762593087625838659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22808046350124116834451545 17106034762593087625838659)
      ·
        refine ⟨25659052143889631438757989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17106034762593087625838659 25659052143889631438757989)
        ·
          refine ⟨4811072276979305894767123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25659052143889631438757989 4811072276979305894767123)
          ·
            refine ⟨7216608415468958842150685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811072276979305894767123 7216608415468958842150685)
            ·
              refine ⟨2706228155800859565806507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7216608415468958842150685 2706228155800859565806507)
              ·
                refine ⟨4059342233701289348709761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706228155800859565806507 4059342233701289348709761)
                ·
                  refine ⟨3044506675275967011532321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4059342233701289348709761 3044506675275967011532321)
                  ·
                    refine ⟨2283380006456975258649241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3044506675275967011532321 2283380006456975258649241)
                    ·
                      refine ⟨1712535004842731443986931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283380006456975258649241 1712535004842731443986931)
                      ·
                        rfl

theorem cell23_3335150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_3335150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335150 prefixEnd_3335150 := by exact prefixLift 3335150
  have htrace : WordTrace (prefixWord ++ tailWord_3335150) baseStart_3335150 baseEnd_3335150 := by
    simpa [prefixWord, tailWord_3335150, baseEnd_3335150] using wordTrace_append hprefix tailTrace_3335150
  have hstable : (prefixWord ++ tailWord_3335150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335150).length < 2 ^ (prefixWord ++ tailWord_3335150).sum := by decide
  have hdescent : baseEnd_3335150 < baseStart_3335150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335165 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_3335165 : Nat := 118140960795 + 3335165 * 2 ^ 59
def prefixEnd_3335165 : Nat := 4983230072969 + 3 ^ 40 * 3335165 * 2
def baseEnd_3335165 : Nat := 570847569017516295099787

theorem tailTrace_3335165 : CollatzResearch.WordTrace tailWord_3335165 prefixEnd_3335165 570847569017516295099787 := by
  unfold tailWord_3335165
  simp only [CollatzResearch.WordTrace]
  refine ⟨121643460962274280678870949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81095640641516187119247299 121643460962274280678870949)
  ·
    refine ⟨22808148930426427627288303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121643460962274280678870949 22808148930426427627288303)
    ·
      refine ⟨34212223395639641440932455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22808148930426427627288303 34212223395639641440932455)
      ·
        refine ⟨51318335093459462161398683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34212223395639641440932455 51318335093459462161398683)
        ·
          refine ⟨76977502640189193242098025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51318335093459462161398683 76977502640189193242098025)
          ·
            refine ⟨57733126980141894931573519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76977502640189193242098025 57733126980141894931573519)
            ·
              refine ⟨86599690470212842397360279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57733126980141894931573519 86599690470212842397360279)
              ·
                refine ⟨129899535705319263596040419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86599690470212842397360279 129899535705319263596040419)
                ·
                  refine ⟨194849303557978895394060629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129899535705319263596040419 194849303557978895394060629)
                  ·
                    refine ⟨570847569017516295099787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 194849303557978895394060629 570847569017516295099787)
                    ·
                      rfl

theorem cell23_3335165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_3335165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335165 prefixEnd_3335165 := by exact prefixLift 3335165
  have htrace : WordTrace (prefixWord ++ tailWord_3335165) baseStart_3335165 baseEnd_3335165 := by
    simpa [prefixWord, tailWord_3335165, baseEnd_3335165] using wordTrace_append hprefix tailTrace_3335165
  have hstable : (prefixWord ++ tailWord_3335165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335165).length < 2 ^ (prefixWord ++ tailWord_3335165).sum := by decide
  have hdescent : baseEnd_3335165 < baseStart_3335165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335185 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3335185 : Nat := 118140960795 + 3335185 * 2 ^ 59
def prefixEnd_3335185 : Nat := 4983230072969 + 3 ^ 40 * 3335185 * 2
def baseEnd_3335185 : Nat := 1712552976665638807049269

theorem tailTrace_3335185 : CollatzResearch.WordTrace tailWord_3335185 prefixEnd_3335185 1712552976665638807049269 := by
  unfold tailWord_3335185
  simp only [CollatzResearch.WordTrace]
  refine ⟨121644190422201824094599009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81096126948134549396399339 121644190422201824094599009)
  ·
    refine ⟨91233142816651368070949257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121644190422201824094599009 91233142816651368070949257)
    ·
      refine ⟨68424857112488526053211943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91233142816651368070949257 68424857112488526053211943)
      ·
        refine ⟨102637285668732789079817915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68424857112488526053211943 102637285668732789079817915)
        ·
          refine ⟨153955928503099183619726873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102637285668732789079817915 153955928503099183619726873)
          ·
            refine ⟨115466946377324387714795155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153955928503099183619726873 115466946377324387714795155)
            ·
              refine ⟨173200419565986581572192733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115466946377324387714795155 173200419565986581572192733)
              ·
                refine ⟨64950157337244968089572275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173200419565986581572192733 64950157337244968089572275)
                ·
                  refine ⟨97425236005867452134358413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64950157337244968089572275 97425236005867452134358413)
                  ·
                    refine ⟨36534463502200294550384405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97425236005867452134358413 36534463502200294550384405)
                    ·
                      refine ⟨1712552976665638807049269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36534463502200294550384405 1712552976665638807049269)
                      ·
                        rfl

theorem cell23_3335185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3335185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335185 prefixEnd_3335185 := by exact prefixLift 3335185
  have htrace : WordTrace (prefixWord ++ tailWord_3335185) baseStart_3335185 baseEnd_3335185 := by
    simpa [prefixWord, tailWord_3335185, baseEnd_3335185] using wordTrace_append hprefix tailTrace_3335185
  have hstable : (prefixWord ++ tailWord_3335185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335185).length < 2 ^ (prefixWord ++ tailWord_3335185).sum := by decide
  have hdescent : baseEnd_3335185 < baseStart_3335185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335189 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3335189 : Nat := 118140960795 + 3335189 * 2 ^ 59
def prefixEnd_3335189 : Nat := 4983230072969 + 3 ^ 40 * 3335189 * 2
def baseEnd_3335189 : Nat := 1712555030588256791399251

theorem tailTrace_3335189 : CollatzResearch.WordTrace tailWord_3335189 prefixEnd_3335189 1712555030588256791399251 := by
  unfold tailWord_3335189
  simp only [CollatzResearch.WordTrace]
  refine ⟨121644336314187332777744621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81096224209458221851829747 121644336314187332777744621)
  ·
    refine ⟨45616626117820249791654233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121644336314187332777744621 45616626117820249791654233)
    ·
      refine ⟨34212469588365187343740675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45616626117820249791654233 34212469588365187343740675)
      ·
        refine ⟨51318704382547781015611013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34212469588365187343740675 51318704382547781015611013)
        ·
          refine ⟨9622257071727708940427065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51318704382547781015611013 9622257071727708940427065)
          ·
            refine ⟨7216692803795781705320299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622257071727708940427065 7216692803795781705320299)
            ·
              refine ⟨10825039205693672557980449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216692803795781705320299 10825039205693672557980449)
              ·
                refine ⟨8118779404270254418485337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825039205693672557980449 8118779404270254418485337)
                ·
                  refine ⟨6089084553202690813864003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118779404270254418485337 6089084553202690813864003)
                  ·
                    refine ⟨9133626829804036220796005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089084553202690813864003 9133626829804036220796005)
                    ·
                      refine ⟨1712555030588256791399251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9133626829804036220796005 1712555030588256791399251)
                      ·
                        rfl

theorem cell23_3335189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3335189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335189 prefixEnd_3335189 := by exact prefixLift 3335189
  have htrace : WordTrace (prefixWord ++ tailWord_3335189) baseStart_3335189 baseEnd_3335189 := by
    simpa [prefixWord, tailWord_3335189, baseEnd_3335189] using wordTrace_append hprefix tailTrace_3335189
  have hstable : (prefixWord ++ tailWord_3335189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335189).length < 2 ^ (prefixWord ++ tailWord_3335189).sum := by decide
  have hdescent : baseEnd_3335189 < baseStart_3335189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335199 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 3, 4]
def baseStart_3335199 : Nat := 118140960795 + 3335199 * 2 ^ 59
def prefixEnd_3335199 : Nat := 4983230072969 + 3 ^ 40 * 3335199 * 2
def baseEnd_3335199 : Nat := 570853388464933917424735

theorem tailTrace_3335199 : CollatzResearch.WordTrace tailWord_3335199 prefixEnd_3335199 570853388464933917424735 := by
  unfold tailWord_3335199
  simp only [CollatzResearch.WordTrace]
  refine ⟨121644701044151104485608651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81096467362767402990405767 121644701044151104485608651)
  ·
    refine ⟨182467051566226656728412977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121644701044151104485608651 182467051566226656728412977)
    ·
      refine ⟨136850288674669992546309733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182467051566226656728412977 136850288674669992546309733)
      ·
        refine ⟨25659429126500623602433075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136850288674669992546309733 25659429126500623602433075)
        ·
          refine ⟨38489143689750935403649613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25659429126500623602433075 38489143689750935403649613)
          ·
            refine ⟨14433428883656600776368605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38489143689750935403649613 14433428883656600776368605)
            ·
              refine ⟨5412535831371225291138227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14433428883656600776368605 5412535831371225291138227)
              ·
                refine ⟨8118803747056837936707341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412535831371225291138227 8118803747056837936707341)
                ·
                  refine ⟨3044551405146314226265253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8118803747056837936707341 3044551405146314226265253)
                  ·
                    refine ⟨570853388464933917424735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3044551405146314226265253 570853388464933917424735)
                    ·
                      rfl

theorem cell23_3335199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_3335199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335199 prefixEnd_3335199 := by exact prefixLift 3335199
  have htrace : WordTrace (prefixWord ++ tailWord_3335199) baseStart_3335199 baseEnd_3335199 := by
    simpa [prefixWord, tailWord_3335199, baseEnd_3335199] using wordTrace_append hprefix tailTrace_3335199
  have hstable : (prefixWord ++ tailWord_3335199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335199).length < 2 ^ (prefixWord ++ tailWord_3335199).sum := by decide
  have hdescent : baseEnd_3335199 < baseStart_3335199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335212 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 6]
def baseStart_3335212 : Nat := 118140960795 + 3335212 * 2 ^ 59
def prefixEnd_3335212 : Nat := 4983230072969 + 3 ^ 40 * 3335212 * 2
def baseEnd_3335212 : Nat := 190285204515923355712405

theorem tailTrace_3335212 : CollatzResearch.WordTrace tailWord_3335212 prefixEnd_3335212 190285204515923355712405 := by
  unfold tailWord_3335212
  simp only [CollatzResearch.WordTrace]
  refine ⟨60822587596552003852915945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81096783462069338470554593 60822587596552003852915945)
  ·
    refine ⟨45616940697414002889686959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60822587596552003852915945 45616940697414002889686959)
    ·
      refine ⟨68425411046121004334530439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45616940697414002889686959 68425411046121004334530439)
      ·
        refine ⟨102638116569181506501795659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68425411046121004334530439 102638116569181506501795659)
        ·
          refine ⟨153957174853772259752693489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102638116569181506501795659 153957174853772259752693489)
          ·
            refine ⟨115467881140329194814520117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153957174853772259752693489 115467881140329194814520117)
            ·
              refine ⟨10825113856905862013861261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115467881140329194814520117 10825113856905862013861261)
              ·
                refine ⟨4059417696339698255197973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10825113856905862013861261 4059417696339698255197973)
                ·
                  refine ⟨190285204515923355712405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4059417696339698255197973 190285204515923355712405)
                  ·
                    rfl

theorem cell23_3335212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_3335212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335212 prefixEnd_3335212 := by exact prefixLift 3335212
  have htrace : WordTrace (prefixWord ++ tailWord_3335212) baseStart_3335212 baseEnd_3335212 := by
    simpa [prefixWord, tailWord_3335212, baseEnd_3335212] using wordTrace_append hprefix tailTrace_3335212
  have hstable : (prefixWord ++ tailWord_3335212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335212).length < 2 ^ (prefixWord ++ tailWord_3335212).sum := by decide
  have hdescent : baseEnd_3335212 < baseStart_3335212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335215 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_3335215 : Nat := 118140960795 + 3335215 * 2 ^ 59
def prefixEnd_3335215 : Nat := 4983230072969 + 3 ^ 40 * 3335215 * 2
def baseEnd_3335215 : Nat := 1712568381085273689674131

theorem tailTrace_3335215 : CollatzResearch.WordTrace tailWord_3335215 prefixEnd_3335215 1712568381085273689674131 := by
  unfold tailWord_3335215
  simp only [CollatzResearch.WordTrace]
  refine ⟨121645284612093139218191099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81096856408062092812127399 121645284612093139218191099)
  ·
    refine ⟨182467926918139708827286649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121645284612093139218191099 182467926918139708827286649)
    ·
      refine ⟨136850945188604781620464987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182467926918139708827286649 136850945188604781620464987)
      ·
        refine ⟨205276417782907172430697481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136850945188604781620464987 205276417782907172430697481)
        ·
          refine ⟨153957313337180379323023111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205276417782907172430697481 153957313337180379323023111)
          ·
            refine ⟨230935970005770568984534667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153957313337180379323023111 230935970005770568984534667)
            ·
              refine ⟨346403955008655853476802001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230935970005770568984534667 346403955008655853476802001)
              ·
                refine ⟨259802966256491890107601501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346403955008655853476802001 259802966256491890107601501)
                ·
                  refine ⟨97426112346184458790350563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259802966256491890107601501 97426112346184458790350563)
                  ·
                    refine ⟨146139168519276688185525845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97426112346184458790350563 146139168519276688185525845)
                    ·
                      refine ⟨1712568381085273689674131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146139168519276688185525845 1712568381085273689674131)
                      ·
                        rfl

theorem cell23_3335215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_3335215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335215 prefixEnd_3335215 := by exact prefixLift 3335215
  have htrace : WordTrace (prefixWord ++ tailWord_3335215) baseStart_3335215 baseEnd_3335215 := by
    simpa [prefixWord, tailWord_3335215, baseEnd_3335215] using wordTrace_append hprefix tailTrace_3335215
  have hstable : (prefixWord ++ tailWord_3335215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335215).length < 2 ^ (prefixWord ++ tailWord_3335215).sum := by decide
  have hdescent : baseEnd_3335215 < baseStart_3335215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335250 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3335250 : Nat := 118140960795 + 3335250 * 2 ^ 59
def prefixEnd_3335250 : Nat := 4983230072969 + 3 ^ 40 * 3335250 * 2
def baseEnd_3335250 : Nat := 570862117636060350912157

theorem tailTrace_3335250 : CollatzResearch.WordTrace tailWord_3335250 prefixEnd_3335250 570862117636060350912157 := by
  unfold tailWord_3335250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30411640291741585048928801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81097707444644226797143469 30411640291741585048928801)
  ·
    refine ⟨22808730218806188786696601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30411640291741585048928801 22808730218806188786696601)
    ·
      refine ⟨17106547664104641590022451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22808730218806188786696601 17106547664104641590022451)
      ·
        refine ⟨25659821496156962385033677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17106547664104641590022451 25659821496156962385033677)
        ·
          refine ⟨9622433061058860894387629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25659821496156962385033677 9622433061058860894387629)
          ·
            refine ⟨3608412397897072835395361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9622433061058860894387629 3608412397897072835395361)
            ·
              refine ⟨2706309298422804626546521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608412397897072835395361 2706309298422804626546521)
              ·
                refine ⟨2029731973817103469909891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706309298422804626546521 2029731973817103469909891)
                ·
                  refine ⟨3044597960725655204864837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029731973817103469909891 3044597960725655204864837)
                  ·
                    refine ⟨570862117636060350912157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3044597960725655204864837 570862117636060350912157)
                    ·
                      rfl

theorem cell23_3335250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3335250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335250 prefixEnd_3335250 := by exact prefixLift 3335250
  have htrace : WordTrace (prefixWord ++ tailWord_3335250) baseStart_3335250 baseEnd_3335250 := by
    simpa [prefixWord, tailWord_3335250, baseEnd_3335250] using wordTrace_append hprefix tailTrace_3335250
  have hstable : (prefixWord ++ tailWord_3335250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335250).length < 2 ^ (prefixWord ++ tailWord_3335250).sum := by decide
  have hdescent : baseEnd_3335250 < baseStart_3335250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335279 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_3335279 : Nat := 118140960795 + 3335279 * 2 ^ 59
def prefixEnd_3335279 : Nat := 4983230072969 + 3 ^ 40 * 3335279 * 2
def baseEnd_3335279 : Nat := 1712601243847161439273837

theorem tailTrace_3335279 : CollatzResearch.WordTrace tailWord_3335279 prefixEnd_3335279 1712601243847161439273837 := by
  unfold tailWord_3335279
  simp only [CollatzResearch.WordTrace]
  refine ⟨121647618883861278148520891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81098412589240852099013927 121647618883861278148520891)
  ·
    refine ⟨182471428325791917222781337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121647618883861278148520891 182471428325791917222781337)
    ·
      refine ⟨136853571244343937917086003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182471428325791917222781337 136853571244343937917086003)
      ·
        refine ⟨205280356866515906875629005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136853571244343937917086003 205280356866515906875629005)
        ·
          refine ⟨76980133824943465078360877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205280356866515906875629005 76980133824943465078360877)
          ·
            refine ⟨28867550184353799404385329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76980133824943465078360877 28867550184353799404385329)
            ·
              refine ⟨21650662638265349553288997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28867550184353799404385329 21650662638265349553288997)
              ·
                refine ⟨4059499244674753041241687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21650662638265349553288997 4059499244674753041241687)
                ·
                  refine ⟨6089248867012129561862531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059499244674753041241687 6089248867012129561862531)
                  ·
                    refine ⟨9133873300518194342793797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089248867012129561862531 9133873300518194342793797)
                    ·
                      refine ⟨1712601243847161439273837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9133873300518194342793797 1712601243847161439273837)
                      ·
                        rfl

theorem cell23_3335279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_3335279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335279 prefixEnd_3335279 := by exact prefixLift 3335279
  have htrace : WordTrace (prefixWord ++ tailWord_3335279) baseStart_3335279 baseEnd_3335279 := by
    simpa [prefixWord, tailWord_3335279, baseEnd_3335279] using wordTrace_append hprefix tailTrace_3335279
  have hstable : (prefixWord ++ tailWord_3335279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335279).length < 2 ^ (prefixWord ++ tailWord_3335279).sum := by decide
  have hdescent : baseEnd_3335279 < baseStart_3335279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335296 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4]
def baseStart_3335296 : Nat := 118140960795 + 3335296 * 2 ^ 59
def prefixEnd_3335296 : Nat := 4983230072969 + 3 ^ 40 * 3335296 * 2
def baseEnd_3335296 : Nat := 1712609973018287872761259

theorem tailTrace_3335296 : CollatzResearch.WordTrace tailWord_3335296 prefixEnd_3335296 1712609973018287872761259 := by
  unfold tailWord_3335296
  simp only [CollatzResearch.WordTrace]
  refine ⟨60824119462399845025944871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81098825949866460034593161 60824119462399845025944871)
  ·
    refine ⟨91236179193599767538917307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60824119462399845025944871 91236179193599767538917307)
    ·
      refine ⟨136854268790399651308375961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91236179193599767538917307 136854268790399651308375961)
      ·
        refine ⟨102640701592799738481281971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136854268790399651308375961 102640701592799738481281971)
        ·
          refine ⟨153961052389199607721922957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102640701592799738481281971 153961052389199607721922957)
          ·
            refine ⟨57735394645949852895721109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153961052389199607721922957 57735394645949852895721109)
            ·
              refine ⟨2706346624028899354486927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57735394645949852895721109 2706346624028899354486927)
              ·
                refine ⟨4059519936043349031730391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706346624028899354486927 4059519936043349031730391)
                ·
                  refine ⟨6089279904065023547595587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059519936043349031730391 6089279904065023547595587)
                  ·
                    refine ⟨9133919856097535321393381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089279904065023547595587 9133919856097535321393381)
                    ·
                      refine ⟨1712609973018287872761259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9133919856097535321393381 1712609973018287872761259)
                      ·
                        rfl

theorem cell23_3335296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_3335296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335296 prefixEnd_3335296 := by exact prefixLift 3335296
  have htrace : WordTrace (prefixWord ++ tailWord_3335296) baseStart_3335296 baseEnd_3335296 := by
    simpa [prefixWord, tailWord_3335296, baseEnd_3335296] using wordTrace_append hprefix tailTrace_3335296
  have hstable : (prefixWord ++ tailWord_3335296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335296).length < 2 ^ (prefixWord ++ tailWord_3335296).sum := by decide
  have hdescent : baseEnd_3335296 < baseStart_3335296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335326 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3335326 : Nat := 118140960795 + 3335326 * 2 ^ 59
def prefixEnd_3335326 : Nat := 4983230072969 + 3 ^ 40 * 3335326 * 2
def baseEnd_3335326 : Nat := 1712625377437922755386121

theorem tailTrace_3335326 : CollatzResearch.WordTrace tailWord_3335326 prefixEnd_3335326 1712625377437922755386121 := by
  unfold tailWord_3335326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206166639336375646935229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81099555409794003450321221 15206166639336375646935229)
  ·
    refine ⟨5702312489751140867600711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15206166639336375646935229 5702312489751140867600711)
    ·
      refine ⟨8553468734626711301401067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702312489751140867600711 8553468734626711301401067)
      ·
        refine ⟨12830203101940066952101601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8553468734626711301401067 12830203101940066952101601)
        ·
          refine ⟨9622652326455050214076201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12830203101940066952101601 9622652326455050214076201)
          ·
            refine ⟨7216989244841287660557151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622652326455050214076201 7216989244841287660557151)
            ·
              refine ⟨10825483867261931490835727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216989244841287660557151 10825483867261931490835727)
              ·
                refine ⟨16238225800892897236253591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10825483867261931490835727 16238225800892897236253591)
                ·
                  refine ⟨24357338701339345854380387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16238225800892897236253591 24357338701339345854380387)
                  ·
                    refine ⟨36536008052009018781570581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24357338701339345854380387 36536008052009018781570581)
                    ·
                      refine ⟨1712625377437922755386121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36536008052009018781570581 1712625377437922755386121)
                      ·
                        rfl

theorem cell23_3335326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3335326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335326 prefixEnd_3335326 := by exact prefixLift 3335326
  have htrace : WordTrace (prefixWord ++ tailWord_3335326) baseStart_3335326 baseEnd_3335326 := by
    simpa [prefixWord, tailWord_3335326, baseEnd_3335326] using wordTrace_append hprefix tailTrace_3335326
  have hstable : (prefixWord ++ tailWord_3335326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335326).length < 2 ^ (prefixWord ++ tailWord_3335326).sum := by decide
  have hdescent : baseEnd_3335326 < baseStart_3335326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335346 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3335346 : Nat := 118140960795 + 3335346 * 2 ^ 59
def prefixEnd_3335346 : Nat := 4983230072969 + 3 ^ 40 * 3335346 * 2
def baseEnd_3335346 : Nat := 1712635647051012677136029

theorem tailTrace_3335346 : CollatzResearch.WordTrace tailWord_3335346 prefixEnd_3335346 1712635647051012677136029 := by
  unfold tailWord_3335346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412515643654637147802473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81100041716412365727473261 30412515643654637147802473)
  ·
    refine ⟨22809386732740977860851855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30412515643654637147802473 22809386732740977860851855)
    ·
      refine ⟨34214080099111466791277783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22809386732740977860851855 34214080099111466791277783)
      ·
        refine ⟨51321120148667200186916675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34214080099111466791277783 51321120148667200186916675)
        ·
          refine ⟨76981680223000800280375013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51321120148667200186916675 76981680223000800280375013)
          ·
            refine ⟨14434065041812650052570315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76981680223000800280375013 14434065041812650052570315)
            ·
              refine ⟨21651097562718975078855473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14434065041812650052570315 21651097562718975078855473)
              ·
                refine ⟨16238323172039231309141605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21651097562718975078855473 16238323172039231309141605)
                ·
                  refine ⟨3044685594757355870464051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16238323172039231309141605 3044685594757355870464051)
                  ·
                    refine ⟨4567028392136033805696077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3044685594757355870464051 4567028392136033805696077)
                    ·
                      refine ⟨1712635647051012677136029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567028392136033805696077 1712635647051012677136029)
                      ·
                        rfl

theorem cell23_3335346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3335346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335346 prefixEnd_3335346 := by exact prefixLift 3335346
  have htrace : WordTrace (prefixWord ++ tailWord_3335346) baseStart_3335346 baseEnd_3335346 := by
    simpa [prefixWord, tailWord_3335346, baseEnd_3335346] using wordTrace_append hprefix tailTrace_3335346
  have hstable : (prefixWord ++ tailWord_3335346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335346).length < 2 ^ (prefixWord ++ tailWord_3335346).sum := by decide
  have hdescent : baseEnd_3335346 < baseStart_3335346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335350 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_3335350 : Nat := 118140960795 + 3335350 * 2 ^ 59
def prefixEnd_3335350 : Nat := 4983230072969 + 3 ^ 40 * 3335350 * 2
def baseEnd_3335350 : Nat := 1712637700973630661486011

theorem tailTrace_3335350 : CollatzResearch.WordTrace tailWord_3335350 prefixEnd_3335350 1712637700973630661486011 := by
  unfold tailWord_3335350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603138029162753579647219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81100138977736038182903669 7603138029162753579647219)
  ·
    refine ⟨11404707043744130369470829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7603138029162753579647219 11404707043744130369470829)
    ·
      refine ⟨4276765141404048888551561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11404707043744130369470829 4276765141404048888551561)
      ·
        refine ⟨3207573856053036666413671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4276765141404048888551561 3207573856053036666413671)
        ·
          refine ⟨4811360784079554999620507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207573856053036666413671 4811360784079554999620507)
          ·
            refine ⟨7217041176119332499430761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811360784079554999620507 7217041176119332499430761)
            ·
              refine ⟨5412780882089499374573071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7217041176119332499430761 5412780882089499374573071)
              ·
                refine ⟨8119171323134249061859607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412780882089499374573071 8119171323134249061859607)
                ·
                  refine ⟨12178756984701373592789411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8119171323134249061859607 12178756984701373592789411)
                  ·
                    refine ⟨18268135477052060389184117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12178756984701373592789411 18268135477052060389184117)
                    ·
                      refine ⟨1712637700973630661486011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18268135477052060389184117 1712637700973630661486011)
                      ·
                        rfl

theorem cell23_3335350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_3335350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335350 prefixEnd_3335350 := by exact prefixLift 3335350
  have htrace : WordTrace (prefixWord ++ tailWord_3335350) baseStart_3335350 baseEnd_3335350 := by
    simpa [prefixWord, tailWord_3335350, baseEnd_3335350] using wordTrace_append hprefix tailTrace_3335350
  have hstable : (prefixWord ++ tailWord_3335350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335350).length < 2 ^ (prefixWord ++ tailWord_3335350).sum := by decide
  have hdescent : baseEnd_3335350 < baseStart_3335350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335364 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_3335364 : Nat := 118140960795 + 3335364 * 2 ^ 59
def prefixEnd_3335364 : Nat := 4983230072969 + 3 ^ 40 * 3335364 * 2
def baseEnd_3335364 : Nat := 1712644889702793606710947

theorem tailTrace_3335364 : CollatzResearch.WordTrace tailWord_3335364 prefixEnd_3335364 1712644889702793606710947 := by
  unfold tailWord_3335364
  simp only [CollatzResearch.WordTrace]
  refine ⟨60825359544276668832682573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81100479392368891776910097 60825359544276668832682573)
  ·
    refine ⟨22809509829103750812255965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60825359544276668832682573 22809509829103750812255965)
    ·
      refine ⟨8553566185913906554595987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22809509829103750812255965 8553566185913906554595987)
      ·
        refine ⟨12830349278870859831893981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8553566185913906554595987 12830349278870859831893981)
        ·
          refine ⟨4811380979576572436960243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12830349278870859831893981 4811380979576572436960243)
          ·
            refine ⟨7217071469364858655440365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811380979576572436960243 7217071469364858655440365)
            ·
              refine ⟨2706401801011821995790137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7217071469364858655440365 2706401801011821995790137)
              ·
                refine ⟨2029801350758866496842603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706401801011821995790137 2029801350758866496842603)
                ·
                  refine ⟨3044702026138299745263905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029801350758866496842603 3044702026138299745263905)
                  ·
                    refine ⟨2283526519603724808947929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3044702026138299745263905 2283526519603724808947929)
                    ·
                      refine ⟨1712644889702793606710947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283526519603724808947929 1712644889702793606710947)
                      ·
                        rfl

theorem cell23_3335364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_3335364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335364 prefixEnd_3335364 := by exact prefixLift 3335364
  have htrace : WordTrace (prefixWord ++ tailWord_3335364) baseStart_3335364 baseEnd_3335364 := by
    simpa [prefixWord, tailWord_3335364, baseEnd_3335364] using wordTrace_append hprefix tailTrace_3335364
  have hstable : (prefixWord ++ tailWord_3335364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335364).length < 2 ^ (prefixWord ++ tailWord_3335364).sum := by decide
  have hdescent : baseEnd_3335364 < baseStart_3335364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335386 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2]
def baseStart_3335386 : Nat := 118140960795 + 3335386 * 2 ^ 59
def prefixEnd_3335386 : Nat := 4983230072969 + 3 ^ 40 * 3335386 * 2
def baseEnd_3335386 : Nat := 1712656186277192520635845

theorem tailTrace_3335386 : CollatzResearch.WordTrace tailWord_3335386 prefixEnd_3335386 1712656186277192520635845 := by
  unfold tailWord_3335386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412880373618408855666503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81101014329649090281777341 30412880373618408855666503)
  ·
    refine ⟨45619320560427613283499755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30412880373618408855666503 45619320560427613283499755)
    ·
      refine ⟨68428980840641419925249633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45619320560427613283499755 68428980840641419925249633)
      ·
        refine ⟨51321735630481064943937225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68428980840641419925249633 51321735630481064943937225)
        ·
          refine ⟨38491301722860798707952919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51321735630481064943937225 38491301722860798707952919)
          ·
            refine ⟨57736952584291198061929379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38491301722860798707952919 57736952584291198061929379)
            ·
              refine ⟨86605428876436797092894069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57736952584291198061929379 86605428876436797092894069)
              ·
                refine ⟨8119258957165949727458819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86605428876436797092894069 8119258957165949727458819)
                ·
                  refine ⟨12178888435748924591188229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8119258957165949727458819 12178888435748924591188229)
                  ·
                    refine ⟨2283541581702923360847793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12178888435748924591188229 2283541581702923360847793)
                    ·
                      refine ⟨1712656186277192520635845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283541581702923360847793 1712656186277192520635845)
                      ·
                        rfl

theorem cell23_3335386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_3335386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335386 prefixEnd_3335386 := by exact prefixLift 3335386
  have htrace : WordTrace (prefixWord ++ tailWord_3335386) baseStart_3335386 baseEnd_3335386 := by
    simpa [prefixWord, tailWord_3335386, baseEnd_3335386] using wordTrace_append hprefix tailTrace_3335386
  have hstable : (prefixWord ++ tailWord_3335386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335386).length < 2 ^ (prefixWord ++ tailWord_3335386).sum := by decide
  have hdescent : baseEnd_3335386 < baseStart_3335386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335436 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3335436 : Nat := 118140960795 + 3335436 * 2 ^ 59
def prefixEnd_3335436 : Nat := 4983230072969 + 3 ^ 40 * 3335436 * 2
def baseEnd_3335436 : Nat := 1712681860309917325010615

theorem tailTrace_3335436 : CollatzResearch.WordTrace tailWord_3335436 prefixEnd_3335436 1712681860309917325010615 := by
  unfold tailWord_3335436
  simp only [CollatzResearch.WordTrace]
  refine ⟨60826672572146246980993081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81102230096194995974657441 60826672572146246980993081)
  ·
    refine ⟨45620004429109685235744811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60826672572146246980993081 45620004429109685235744811)
    ·
      refine ⟨68430006643664527853617217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45620004429109685235744811 68430006643664527853617217)
      ·
        refine ⟨51322504982748395890212913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68430006643664527853617217 51322504982748395890212913)
        ·
          refine ⟨38491878737061296917659685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51322504982748395890212913 38491878737061296917659685)
          ·
            refine ⟨7217227263198993172061191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38491878737061296917659685 7217227263198993172061191)
            ·
              refine ⟨10825840894798489758091787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217227263198993172061191 10825840894798489758091787)
              ·
                refine ⟨16238761342197734637137681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10825840894798489758091787 16238761342197734637137681)
                ·
                  refine ⟨12179071006648300977853261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16238761342197734637137681 12179071006648300977853261)
                  ·
                    refine ⟨4567151627493112866694973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12179071006648300977853261 4567151627493112866694973)
                    ·
                      refine ⟨1712681860309917325010615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567151627493112866694973 1712681860309917325010615)
                      ·
                        rfl

theorem cell23_3335436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3335436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335436 prefixEnd_3335436 := by exact prefixLift 3335436
  have htrace : WordTrace (prefixWord ++ tailWord_3335436) baseStart_3335436 baseEnd_3335436 := by
    simpa [prefixWord, tailWord_3335436, baseEnd_3335436] using wordTrace_append hprefix tailTrace_3335436
  have hstable : (prefixWord ++ tailWord_3335436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335436).length < 2 ^ (prefixWord ++ tailWord_3335436).sum := by decide
  have hdescent : baseEnd_3335436 < baseStart_3335436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335456 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_3335456 : Nat := 118140960795 + 3335456 * 2 ^ 59
def prefixEnd_3335456 : Nat := 4983230072969 + 3 ^ 40 * 3335456 * 2
def baseEnd_3335456 : Nat := 570897376641002415586841

theorem tailTrace_3335456 : CollatzResearch.WordTrace tailWord_3335456 prefixEnd_3335456 570897376641002415586841 := by
  unfold tailWord_3335456
  simp only [CollatzResearch.WordTrace]
  refine ⟨60827037302110018688857111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81102716402813358251809481 60827037302110018688857111)
  ·
    refine ⟨91240555953165028033285667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60827037302110018688857111 91240555953165028033285667)
    ·
      refine ⟨136860833929747542049928501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91240555953165028033285667 136860833929747542049928501)
      ·
        refine ⟨12830703180913832067180797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136860833929747542049928501 12830703180913832067180797)
        ·
          refine ⟨4811513692842687025192799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12830703180913832067180797 4811513692842687025192799)
          ·
            refine ⟨7217270539264030537789199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811513692842687025192799 7217270539264030537789199)
            ·
              refine ⟨10825905808896045806683799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217270539264030537789199 10825905808896045806683799)
              ·
                refine ⟨16238858713344068710025699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10825905808896045806683799 16238858713344068710025699)
                ·
                  refine ⟨24358288070016103065038549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16238858713344068710025699 24358288070016103065038549)
                  ·
                    refine ⟨570897376641002415586841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24358288070016103065038549 570897376641002415586841)
                    ·
                      rfl

theorem cell23_3335456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_3335456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335456 prefixEnd_3335456 := by exact prefixLift 3335456
  have htrace : WordTrace (prefixWord ++ tailWord_3335456) baseStart_3335456 baseEnd_3335456 := by
    simpa [prefixWord, tailWord_3335456, baseEnd_3335456] using wordTrace_append hprefix tailTrace_3335456
  have hstable : (prefixWord ++ tailWord_3335456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335456).length < 2 ^ (prefixWord ++ tailWord_3335456).sum := by decide
  have hdescent : baseEnd_3335456 < baseStart_3335456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335520 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 1, 4]
def baseStart_3335520 : Nat := 118140960795 + 3335520 * 2 ^ 59
def prefixEnd_3335520 : Nat := 4983230072969 + 3 ^ 40 * 3335520 * 2
def baseEnd_3335520 : Nat := 570908330894964998786743

theorem tailTrace_3335520 : CollatzResearch.WordTrace tailWord_3335520 prefixEnd_3335520 570908330894964998786743 := by
  unfold tailWord_3335520
  simp only [CollatzResearch.WordTrace]
  refine ⟨60828204437994088154022007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81104272583992117538696009 60828204437994088154022007)
  ·
    refine ⟨91242306656991132231033011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60828204437994088154022007 91242306656991132231033011)
    ·
      refine ⟨136863459985486698346549517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91242306656991132231033011 136863459985486698346549517)
      ·
        refine ⟨51323797494557511879956069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136863459985486698346549517 51323797494557511879956069)
        ·
          refine ⟨9623212030229533477491763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51323797494557511879956069 9623212030229533477491763)
          ·
            refine ⟨14434818045344300216237645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623212030229533477491763 14434818045344300216237645)
            ·
              refine ⟨5413056767004112581089117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14434818045344300216237645 5413056767004112581089117)
              ·
                refine ⟨2029896287626542217908419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5413056767004112581089117 2029896287626542217908419)
                ·
                  refine ⟨3044844431439813326862629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029896287626542217908419 3044844431439813326862629)
                  ·
                    refine ⟨570908330894964998786743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3044844431439813326862629 570908330894964998786743)
                    ·
                      rfl

theorem cell23_3335520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 4].length) (baseStart_3335520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335520 prefixEnd_3335520 := by exact prefixLift 3335520
  have htrace : WordTrace (prefixWord ++ tailWord_3335520) baseStart_3335520 baseEnd_3335520 := by
    simpa [prefixWord, tailWord_3335520, baseEnd_3335520] using wordTrace_append hprefix tailTrace_3335520
  have hstable : (prefixWord ++ tailWord_3335520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335520).length < 2 ^ (prefixWord ++ tailWord_3335520).sum := by decide
  have hdescent : baseEnd_3335520 < baseStart_3335520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335530 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3335530 : Nat := 118140960795 + 3335530 * 2 ^ 59
def prefixEnd_3335530 : Nat := 4983230072969 + 3 ^ 40 * 3335530 * 2
def baseEnd_3335530 : Nat := 1712730127491439957235183

theorem tailTrace_3335530 : CollatzResearch.WordTrace tailWord_3335530 prefixEnd_3335530 1712730127491439957235183 := by
  unfold tailWord_3335530
  simp only [CollatzResearch.WordTrace]
  refine ⟨30414193401487987003977011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81104515737301298677272029 30414193401487987003977011)
  ·
    refine ⟨45621290102231980505965517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30414193401487987003977011 45621290102231980505965517)
    ·
      refine ⟨17107983788336992689737069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45621290102231980505965517 17107983788336992689737069)
      ·
        refine ⟨6415493920626372258651401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17107983788336992689737069 6415493920626372258651401)
        ·
          refine ⟨4811620440469779193988551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6415493920626372258651401 4811620440469779193988551)
          ·
            refine ⟨7217430660704668790982827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811620440469779193988551 7217430660704668790982827)
            ·
              refine ⟨10826145991057003186474241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217430660704668790982827 10826145991057003186474241)
              ·
                refine ⟨8119609493292752389855681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10826145991057003186474241 8119609493292752389855681)
                ·
                  refine ⟨6089707119969564292391761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8119609493292752389855681 6089707119969564292391761)
                  ·
                    refine ⟨4567280339977173219293821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6089707119969564292391761 4567280339977173219293821)
                    ·
                      refine ⟨1712730127491439957235183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567280339977173219293821 1712730127491439957235183)
                      ·
                        rfl

theorem cell23_3335530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3335530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335530 prefixEnd_3335530 := by exact prefixLift 3335530
  have htrace : WordTrace (prefixWord ++ tailWord_3335530) baseStart_3335530 baseEnd_3335530 := by
    simpa [prefixWord, tailWord_3335530, baseEnd_3335530] using wordTrace_append hprefix tailTrace_3335530
  have hstable : (prefixWord ++ tailWord_3335530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335530).length < 2 ^ (prefixWord ++ tailWord_3335530).sum := by decide
  have hdescent : baseEnd_3335530 < baseStart_3335530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335613 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3335613 : Nat := 118140960795 + 3335613 * 2 ^ 59
def prefixEnd_3335613 : Nat := 4983230072969 + 3 ^ 40 * 3335613 * 2
def baseEnd_3335613 : Nat := 1712772746385763132497301

theorem tailTrace_3335613 : CollatzResearch.WordTrace tailWord_3335613 prefixEnd_3335613 1712772746385763132497301 := by
  unfold tailWord_3335613
  simp only [CollatzResearch.WordTrace]
  refine ⟨121659800864651253191179493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81106533909767502127452995 121659800864651253191179493)
  ·
    refine ⟨22811212662122109973346155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121659800864651253191179493 22811212662122109973346155)
    ·
      refine ⟨34216818993183164960019233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22811212662122109973346155 34216818993183164960019233)
      ·
        refine ⟨25662614244887373720014425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34216818993183164960019233 25662614244887373720014425)
        ·
          refine ⟨19246960683665530290010819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25662614244887373720014425 19246960683665530290010819)
          ·
            refine ⟨28870441025498295435016229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19246960683665530290010819 28870441025498295435016229)
            ·
              refine ⟨5413207692280930394065543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28870441025498295435016229 5413207692280930394065543)
              ·
                refine ⟨8119811538421395591098315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5413207692280930394065543 8119811538421395591098315)
                ·
                  refine ⟨12179717307632093386647473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8119811538421395591098315 12179717307632093386647473)
                  ·
                    refine ⟨9134787980724070039985605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12179717307632093386647473 9134787980724070039985605)
                    ·
                      refine ⟨1712772746385763132497301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9134787980724070039985605 1712772746385763132497301)
                      ·
                        rfl

theorem cell23_3335613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3335613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335613 prefixEnd_3335613 := by exact prefixLift 3335613
  have htrace : WordTrace (prefixWord ++ tailWord_3335613) baseStart_3335613 baseEnd_3335613 := by
    simpa [prefixWord, tailWord_3335613, baseEnd_3335613] using wordTrace_append hprefix tailTrace_3335613
  have hstable : (prefixWord ++ tailWord_3335613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335613).length < 2 ^ (prefixWord ++ tailWord_3335613).sum := by decide
  have hdescent : baseEnd_3335613 < baseStart_3335613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335620 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3335620 : Nat := 118140960795 + 3335620 * 2 ^ 59
def prefixEnd_3335620 : Nat := 4983230072969 + 3 ^ 40 * 3335620 * 2
def baseEnd_3335620 : Nat := 1712776340750344605109769

theorem tailTrace_3335620 : CollatzResearch.WordTrace tailWord_3335620 prefixEnd_3335620 1712776340750344605109769 := by
  unfold tailWord_3335620
  simp only [CollatzResearch.WordTrace]
  refine ⟨60830028087812946693342157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81106704117083928924456209 60830028087812946693342157)
  ·
    refine ⟨22811260532929855010003309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60830028087812946693342157 22811260532929855010003309)
    ·
      refine ⟨8554222699848695628751241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22811260532929855010003309 8554222699848695628751241)
      ·
        refine ⟨6415667024886521721563431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8554222699848695628751241 6415667024886521721563431)
        ·
          refine ⟨9623500537329782582345147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415667024886521721563431 9623500537329782582345147)
          ·
            refine ⟨14435250805994673873517721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623500537329782582345147 14435250805994673873517721)
            ·
              refine ⟨10826438104496005405138291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435250805994673873517721 10826438104496005405138291)
              ·
                refine ⟨16239657156744008107707437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826438104496005405138291 16239657156744008107707437)
                ·
                  refine ⟨6089871433779003040390289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16239657156744008107707437 6089871433779003040390289)
                  ·
                    refine ⟨4567403575334252280292717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6089871433779003040390289 4567403575334252280292717)
                    ·
                      refine ⟨1712776340750344605109769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567403575334252280292717 1712776340750344605109769)
                      ·
                        rfl

theorem cell23_3335620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3335620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335620 prefixEnd_3335620 := by exact prefixLift 3335620
  have htrace : WordTrace (prefixWord ++ tailWord_3335620) baseStart_3335620 baseEnd_3335620 := by
    simpa [prefixWord, tailWord_3335620, baseEnd_3335620] using wordTrace_append hprefix tailTrace_3335620
  have hstable : (prefixWord ++ tailWord_3335620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335620).length < 2 ^ (prefixWord ++ tailWord_3335620).sum := by decide
  have hdescent : baseEnd_3335620 < baseStart_3335620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335677 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_3335677 : Nat := 118140960795 + 3335677 * 2 ^ 59
def prefixEnd_3335677 : Nat := 4983230072969 + 3 ^ 40 * 3335677 * 2
def baseEnd_3335677 : Nat := 1712805609147650882097007

theorem tailTrace_3335677 : CollatzResearch.WordTrace tailWord_3335677 prefixEnd_3335677 1712805609147650882097007 := by
  unfold tailWord_3335677
  simp only [CollatzResearch.WordTrace]
  refine ⟨121662135136419392121509285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81108090090946261414339523 121662135136419392121509285)
  ·
    refine ⟨22811650338078636022782991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121662135136419392121509285 22811650338078636022782991)
    ·
      refine ⟨34217475507117954034174487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22811650338078636022782991 34217475507117954034174487)
      ·
        refine ⟨51326213260676931051261731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34217475507117954034174487 51326213260676931051261731)
        ·
          refine ⟨76989319891015396576892597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51326213260676931051261731 76989319891015396576892597)
          ·
            refine ⟨7217748739782693429083681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76989319891015396576892597 7217748739782693429083681)
            ·
              refine ⟨5413311554837020071812761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7217748739782693429083681 5413311554837020071812761)
              ·
                refine ⟨4059983666127765053859571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5413311554837020071812761 4059983666127765053859571)
                ·
                  refine ⟨6089975499191647580789357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059983666127765053859571 6089975499191647580789357)
                  ·
                    refine ⟨2283740812196867842796009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6089975499191647580789357 2283740812196867842796009)
                    ·
                      refine ⟨1712805609147650882097007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283740812196867842796009 1712805609147650882097007)
                      ·
                        rfl

theorem cell23_3335677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_3335677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335677 prefixEnd_3335677 := by exact prefixLift 3335677
  have htrace : WordTrace (prefixWord ++ tailWord_3335677) baseStart_3335677 baseEnd_3335677 := by
    simpa [prefixWord, tailWord_3335677, baseEnd_3335677] using wordTrace_append hprefix tailTrace_3335677
  have hstable : (prefixWord ++ tailWord_3335677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335677).length < 2 ^ (prefixWord ++ tailWord_3335677).sum := by decide
  have hdescent : baseEnd_3335677 < baseStart_3335677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335706 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_3335706 : Nat := 118140960795 + 3335706 * 2 ^ 59
def prefixEnd_3335706 : Nat := 4983230072969 + 3 ^ 40 * 3335706 * 2
def baseEnd_3335706 : Nat := 1712820500086631268634373

theorem tailTrace_3335706 : CollatzResearch.WordTrace tailWord_3335706 prefixEnd_3335706 1712820500086631268634373 := by
  unfold tailWord_3335706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30415798213328582518578743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81108795235542886716209981 30415798213328582518578743)
  ·
    refine ⟨45623697319992873777868115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30415798213328582518578743 45623697319992873777868115)
    ·
      refine ⟨68435545979989310666802173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45623697319992873777868115 68435545979989310666802173)
      ·
        refine ⟨25663329742495991500050815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68435545979989310666802173 25663329742495991500050815)
        ·
          refine ⟨38494994613743987250076223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25663329742495991500050815 38494994613743987250076223)
          ·
            refine ⟨57742491920615980875114335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38494994613743987250076223 57742491920615980875114335)
            ·
              refine ⟨86613737880923971312671503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57742491920615980875114335 86613737880923971312671503)
              ·
                refine ⟨129920606821385956969007255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86613737880923971312671503 129920606821385956969007255)
                ·
                  refine ⟨194880910232078935453510883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129920606821385956969007255 194880910232078935453510883)
                  ·
                    refine ⟨292321365348118403180266325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194880910232078935453510883 292321365348118403180266325)
                    ·
                      refine ⟨1712820500086631268634373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 292321365348118403180266325 1712820500086631268634373)
                      ·
                        rfl

theorem cell23_3335706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_3335706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335706 prefixEnd_3335706 := by exact prefixLift 3335706
  have htrace : WordTrace (prefixWord ++ tailWord_3335706) baseStart_3335706 baseEnd_3335706 := by
    simpa [prefixWord, tailWord_3335706, baseEnd_3335706] using wordTrace_append hprefix tailTrace_3335706
  have hstable : (prefixWord ++ tailWord_3335706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335706).length < 2 ^ (prefixWord ++ tailWord_3335706).sum := by decide
  have hdescent : baseEnd_3335706 < baseStart_3335706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335713 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 7]
def baseStart_3335713 : Nat := 118140960795 + 3335713 * 2 ^ 59
def prefixEnd_3335713 : Nat := 4983230072969 + 3 ^ 40 * 3335713 * 2
def baseEnd_3335713 : Nat := 190313788272356971249649

theorem tailTrace_3335713 : CollatzResearch.WordTrace tailWord_3335713 prefixEnd_3335713 190313788272356971249649 := by
  unfold tailWord_3335713
  simp only [CollatzResearch.WordTrace]
  refine ⟨121663448164288970269819793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81108965442859313513213195 121663448164288970269819793)
  ·
    refine ⟨91247586123216727702364845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121663448164288970269819793 91247586123216727702364845)
    ·
      refine ⟨34217844796206272888386817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91247586123216727702364845 34217844796206272888386817)
      ·
        refine ⟨25663383597154704666290113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34217844796206272888386817 25663383597154704666290113)
        ·
          refine ⟨19247537697866028499717585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25663383597154704666290113 19247537697866028499717585)
          ·
            refine ⟨14435653273399521374788189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19247537697866028499717585 14435653273399521374788189)
            ·
              refine ⟨5413369977524820515545571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14435653273399521374788189 5413369977524820515545571)
              ·
                refine ⟨8120054966287230773318357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5413369977524820515545571 8120054966287230773318357)
                ·
                  refine ⟨190313788272356971249649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8120054966287230773318357 190313788272356971249649)
                  ·
                    rfl

theorem cell23_3335713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_3335713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335713 prefixEnd_3335713 := by exact prefixLift 3335713
  have htrace : WordTrace (prefixWord ++ tailWord_3335713) baseStart_3335713 baseEnd_3335713 := by
    simpa [prefixWord, tailWord_3335713, baseEnd_3335713] using wordTrace_append hprefix tailTrace_3335713
  have hstable : (prefixWord ++ tailWord_3335713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335713).length < 2 ^ (prefixWord ++ tailWord_3335713).sum := by decide
  have hdescent : baseEnd_3335713 < baseStart_3335713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335743 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 2, 5]
def baseStart_3335743 : Nat := 118140960795 + 3335743 * 2 ^ 59
def prefixEnd_3335743 : Nat := 4983230072969 + 3 ^ 40 * 3335743 * 2
def baseEnd_3335743 : Nat := 570946499623615874623901

theorem tailTrace_3335743 : CollatzResearch.WordTrace tailWord_3335743 prefixEnd_3335743 570946499623615874623901 := by
  unfold tailWord_3335743
  simp only [CollatzResearch.WordTrace]
  refine ⟨121664542354180285393411883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81109694902786856928941255 121664542354180285393411883)
  ·
    refine ⟨182496813531270428090117825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121664542354180285393411883 182496813531270428090117825)
    ·
      refine ⟨136872610148452821067588369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182496813531270428090117825 136872610148452821067588369)
      ·
        refine ⟨102654457611339615800691277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136872610148452821067588369 102654457611339615800691277)
        ·
          refine ⟨38495421604252355925259229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102654457611339615800691277 38495421604252355925259229)
          ·
            refine ⟨14435783101594633471972211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38495421604252355925259229 14435783101594633471972211)
            ·
              refine ⟨21653674652391950207958317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435783101594633471972211 21653674652391950207958317)
              ·
                refine ⟨8120127994646981327984369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21653674652391950207958317 8120127994646981327984369)
                ·
                  refine ⟨6090095995985235995988277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8120127994646981327984369 6090095995985235995988277)
                  ·
                    refine ⟨570946499623615874623901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6090095995985235995988277 570946499623615874623901)
                    ·
                      rfl

theorem cell23_3335743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_3335743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335743 prefixEnd_3335743 := by exact prefixLift 3335743
  have htrace : WordTrace (prefixWord ++ tailWord_3335743) baseStart_3335743 baseEnd_3335743 := by
    simpa [prefixWord, tailWord_3335743, baseEnd_3335743] using wordTrace_append hprefix tailTrace_3335743
  have hstable : (prefixWord ++ tailWord_3335743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335743).length < 2 ^ (prefixWord ++ tailWord_3335743).sum := by decide
  have hdescent : baseEnd_3335743 < baseStart_3335743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335780 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_3335780 : Nat := 118140960795 + 3335780 * 2 ^ 59
def prefixEnd_3335780 : Nat := 4983230072969 + 3 ^ 40 * 3335780 * 2
def baseEnd_3335780 : Nat := 1712858497655063979109033

theorem tailTrace_3335780 : CollatzResearch.WordTrace tailWord_3335780 prefixEnd_3335780 1712858497655063979109033 := by
  unfold tailWord_3335780
  simp only [CollatzResearch.WordTrace]
  refine ⟨60832945927523120356254397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81110594570030827141672529 60832945927523120356254397)
  ·
    refine ⟨22812354722821170133595399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60832945927523120356254397 22812354722821170133595399)
    ·
      refine ⟨34218532084231755200393099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22812354722821170133595399 34218532084231755200393099)
      ·
        refine ⟨51327798126347632800589649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34218532084231755200393099 51327798126347632800589649)
        ·
          refine ⟨38495848594760724600442237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51327798126347632800589649 38495848594760724600442237)
          ·
            refine ⟨14435943223035271725165839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38495848594760724600442237 14435943223035271725165839)
            ·
              refine ⟨21653914834552907587748759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435943223035271725165839 21653914834552907587748759)
              ·
                refine ⟨32480872251829361381623139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21653914834552907587748759 32480872251829361381623139)
                ·
                  refine ⟨48721308377744042072434709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32480872251829361381623139 48721308377744042072434709)
                  ·
                    refine ⟨2283811330206751972145377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48721308377744042072434709 2283811330206751972145377)
                    ·
                      refine ⟨1712858497655063979109033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283811330206751972145377 1712858497655063979109033)
                      ·
                        rfl

theorem cell23_3335780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_3335780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335780 prefixEnd_3335780 := by exact prefixLift 3335780
  have htrace : WordTrace (prefixWord ++ tailWord_3335780) baseStart_3335780 baseEnd_3335780 := by
    simpa [prefixWord, tailWord_3335780, baseEnd_3335780] using wordTrace_append hprefix tailTrace_3335780
  have hstable : (prefixWord ++ tailWord_3335780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335780).length < 2 ^ (prefixWord ++ tailWord_3335780).sum := by decide
  have hdescent : baseEnd_3335780 < baseStart_3335780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335797 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3335797 : Nat := 118140960795 + 3335797 * 2 ^ 59
def prefixEnd_3335797 : Nat := 4983230072969 + 3 ^ 40 * 3335797 * 2
def baseEnd_3335797 : Nat := 1712867226826190412596455

theorem tailTrace_3335797 : CollatzResearch.WordTrace tailWord_3335797 prefixEnd_3335797 1712867226826190412596455 := by
  unfold tailWord_3335797
  simp only [CollatzResearch.WordTrace]
  refine ⟨121666511895984652615877645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81111007930656435077251763 121666511895984652615877645)
  ·
    refine ⟨45624941960994244730954117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121666511895984652615877645 45624941960994244730954117)
    ·
      refine ⟨8554676617686420887053897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45624941960994244730954117 8554676617686420887053897)
      ·
        refine ⟨6416007463264815665290423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8554676617686420887053897 6416007463264815665290423)
        ·
          refine ⟨9624011194897223497935635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416007463264815665290423 9624011194897223497935635)
          ·
            refine ⟨14436016792345835246903453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624011194897223497935635 14436016792345835246903453)
            ·
              refine ⟨5413506297129688217588795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14436016792345835246903453 5413506297129688217588795)
              ·
                refine ⟨8120259445694532326383193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5413506297129688217588795 8120259445694532326383193)
                ·
                  refine ⟨6090194584270899244787395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8120259445694532326383193 6090194584270899244787395)
                  ·
                    refine ⟨9135291876406348867181093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6090194584270899244787395 9135291876406348867181093)
                    ·
                      refine ⟨1712867226826190412596455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9135291876406348867181093 1712867226826190412596455)
                      ·
                        rfl

theorem cell23_3335797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3335797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335797 prefixEnd_3335797 := by exact prefixLift 3335797
  have htrace : WordTrace (prefixWord ++ tailWord_3335797) baseStart_3335797 baseEnd_3335797 := by
    simpa [prefixWord, tailWord_3335797, baseEnd_3335797] using wordTrace_append hprefix tailTrace_3335797
  have hstable : (prefixWord ++ tailWord_3335797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335797).length < 2 ^ (prefixWord ++ tailWord_3335797).sum := by decide
  have hdescent : baseEnd_3335797 < baseStart_3335797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335833 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_3335833 : Nat := 118140960795 + 3335833 * 2 ^ 59
def prefixEnd_3335833 : Nat := 4983230072969 + 3 ^ 40 * 3335833 * 2
def baseEnd_3335833 : Nat := 570961904043250757248763

theorem tailTrace_3335833 : CollatzResearch.WordTrace tailWord_3335833 prefixEnd_3335833 570961904043250757248763 := by
  unfold tailWord_3335833
  simp only [CollatzResearch.WordTrace]
  refine ⟨121667824923854230764188153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81111883282569487176125435 121667824923854230764188153)
  ·
    refine ⟨91250868692890673073141115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121667824923854230764188153 91250868692890673073141115)
    ·
      refine ⟨136876303039336009609711673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91250868692890673073141115 136876303039336009609711673)
      ·
        refine ⟨102657227279502007207283755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136876303039336009609711673 102657227279502007207283755)
        ·
          refine ⟨153985840919253010810925633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102657227279502007207283755 153985840919253010810925633)
          ·
            refine ⟨115489380689439758108194225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153985840919253010810925633 115489380689439758108194225)
            ·
              refine ⟨86617035517079818581145669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115489380689439758108194225 86617035517079818581145669)
              ·
                refine ⟨16240694159452465983964813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86617035517079818581145669 16240694159452465983964813)
                ·
                  refine ⟨6090260309794674743986805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16240694159452465983964813 6090260309794674743986805)
                  ·
                    refine ⟨570961904043250757248763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6090260309794674743986805 570961904043250757248763)
                    ·
                      rfl

theorem cell23_3335833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_3335833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335833 prefixEnd_3335833 := by exact prefixLift 3335833
  have htrace : WordTrace (prefixWord ++ tailWord_3335833) baseStart_3335833 baseEnd_3335833 := by
    simpa [prefixWord, tailWord_3335833, baseEnd_3335833] using wordTrace_append hprefix tailTrace_3335833
  have hstable : (prefixWord ++ tailWord_3335833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335833).length < 2 ^ (prefixWord ++ tailWord_3335833).sum := by decide
  have hdescent : baseEnd_3335833 < baseStart_3335833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335880 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 4, 4]
def baseStart_3335880 : Nat := 118140960795 + 3335880 * 2 ^ 59
def prefixEnd_3335880 : Nat := 4983230072969 + 3 ^ 40 * 3335880 * 2
def baseEnd_3335880 : Nat := 570969948573504529286191

theorem tailTrace_3335880 : CollatzResearch.WordTrace tailWord_3335880 prefixEnd_3335880 570969948573504529286191 := by
  unfold tailWord_3335880
  simp only [CollatzResearch.WordTrace]
  refine ⟨60834769577341978895574547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81113026103122638527432729 60834769577341978895574547)
  ·
    refine ⟨91252154366012968343361821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60834769577341978895574547 91252154366012968343361821)
    ·
      refine ⟨34219557887254863128760683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91252154366012968343361821 34219557887254863128760683)
      ·
        refine ⟨51329336830882294693141025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34219557887254863128760683 51329336830882294693141025)
        ·
          refine ⟨38497002623161721019855769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51329336830882294693141025 38497002623161721019855769)
          ·
            refine ⟨28872751967371290764891827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38497002623161721019855769 28872751967371290764891827)
            ·
              refine ⟨43309127951056936147337741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28872751967371290764891827 43309127951056936147337741)
              ·
                refine ⟨16240922981646351055251653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43309127951056936147337741 16240922981646351055251653)
                ·
                  refine ⟨3045173059058690822859685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16240922981646351055251653 3045173059058690822859685)
                  ·
                    refine ⟨570969948573504529286191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045173059058690822859685 570969948573504529286191)
                    ·
                      rfl

theorem cell23_3335880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_3335880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335880 prefixEnd_3335880 := by exact prefixLift 3335880
  have htrace : WordTrace (prefixWord ++ tailWord_3335880) baseStart_3335880 baseEnd_3335880 := by
    simpa [prefixWord, tailWord_3335880, baseEnd_3335880] using wordTrace_append hprefix tailTrace_3335880
  have hstable : (prefixWord ++ tailWord_3335880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335880).length < 2 ^ (prefixWord ++ tailWord_3335880).sum := by decide
  have hdescent : baseEnd_3335880 < baseStart_3335880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335897 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_3335897 : Nat := 118140960795 + 3335897 * 2 ^ 59
def prefixEnd_3335897 : Nat := 4983230072969 + 3 ^ 40 * 3335897 * 2
def baseEnd_3335897 : Nat := 570972858297213340448665

theorem tailTrace_3335897 : CollatzResearch.WordTrace tailWord_3335897 prefixEnd_3335897 570972858297213340448665 := by
  unfold tailWord_3335897
  simp only [CollatzResearch.WordTrace]
  refine ⟨121670159195622369694517945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81113439463748246463011963 121670159195622369694517945)
  ·
    refine ⟨91252619396716777270888459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121670159195622369694517945 91252619396716777270888459)
    ·
      refine ⟨136878929095075165906332689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91252619396716777270888459 136878929095075165906332689)
      ·
        refine ⟨102659196821306374429749517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136878929095075165906332689 102659196821306374429749517)
        ·
          refine ⟨38497198807989890411156069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102659196821306374429749517 38497198807989890411156069)
          ·
            refine ⟨7218224776498104452091763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38497198807989890411156069 7218224776498104452091763)
            ·
              refine ⟨10827337164747156678137645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218224776498104452091763 10827337164747156678137645)
              ·
                refine ⟨4060251436780183754301617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10827337164747156678137645 4060251436780183754301617)
                ·
                  refine ⟨3045188577585137815726213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060251436780183754301617 3045188577585137815726213)
                  ·
                    refine ⟨570972858297213340448665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045188577585137815726213 570972858297213340448665)
                    ·
                      rfl

theorem cell23_3335897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_3335897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335897 prefixEnd_3335897 := by exact prefixLift 3335897
  have htrace : WordTrace (prefixWord ++ tailWord_3335897) baseStart_3335897 baseEnd_3335897 := by
    simpa [prefixWord, tailWord_3335897, baseEnd_3335897] using wordTrace_append hprefix tailTrace_3335897
  have hstable : (prefixWord ++ tailWord_3335897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335897).length < 2 ^ (prefixWord ++ tailWord_3335897).sum := by decide
  have hdescent : baseEnd_3335897 < baseStart_3335897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335901 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3335901 : Nat := 118140960795 + 3335901 * 2 ^ 59
def prefixEnd_3335901 : Nat := 4983230072969 + 3 ^ 40 * 3335901 * 2
def baseEnd_3335901 : Nat := 570973542938086001898659

theorem tailTrace_3335901 : CollatzResearch.WordTrace tailWord_3335901 prefixEnd_3335901 570973542938086001898659 := by
  unfold tailWord_3335901
  simp only [CollatzResearch.WordTrace]
  refine ⟨121670305087607878377663557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81113536725071918918442371 121670305087607878377663557)
  ·
    refine ⟨22813182203926477195811917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121670305087607878377663557 22813182203926477195811917)
    ·
      refine ⟨8554943326472428948429469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22813182203926477195811917 8554943326472428948429469)
      ·
        refine ⟨3208103747427160855661051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8554943326472428948429469 3208103747427160855661051)
        ·
          refine ⟨4812155621140741283491577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208103747427160855661051 4812155621140741283491577)
          ·
            refine ⟨3609116715855555962618683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812155621140741283491577 3609116715855555962618683)
            ·
              refine ⟨5413675073783333943928025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609116715855555962618683 5413675073783333943928025)
              ·
                refine ⟨4060256305337500457946019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5413675073783333943928025 4060256305337500457946019)
                ·
                  refine ⟨6090384458006250686919029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4060256305337500457946019 6090384458006250686919029)
                  ·
                    refine ⟨570973542938086001898659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6090384458006250686919029 570973542938086001898659)
                    ·
                      rfl

theorem cell23_3335901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3335901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335901 prefixEnd_3335901 := by exact prefixLift 3335901
  have htrace : WordTrace (prefixWord ++ tailWord_3335901) baseStart_3335901 baseEnd_3335901 := by
    simpa [prefixWord, tailWord_3335901, baseEnd_3335901] using wordTrace_append hprefix tailTrace_3335901
  have hstable : (prefixWord ++ tailWord_3335901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335901).length < 2 ^ (prefixWord ++ tailWord_3335901).sum := by decide
  have hdescent : baseEnd_3335901 < baseStart_3335901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335917 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3335917 : Nat := 118140960795 + 3335917 * 2 ^ 59
def prefixEnd_3335917 : Nat := 4983230072969 + 3 ^ 40 * 3335917 * 2
def baseEnd_3335917 : Nat := 1712928844504729943095903

theorem tailTrace_3335917 : CollatzResearch.WordTrace tailWord_3335917 prefixEnd_3335917 1712928844504729943095903 := by
  unfold tailWord_3335917
  simp only [CollatzResearch.WordTrace]
  refine ⟨121670888655549913110246005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81113925770366608740164003 121670888655549913110246005)
  ·
    refine ⟨11406645811457804354085563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121670888655549913110246005 11406645811457804354085563)
    ·
      refine ⟨17109968717186706531128345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406645811457804354085563 17109968717186706531128345)
      ·
        refine ⟨12832476537890029898346259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17109968717186706531128345 12832476537890029898346259)
        ·
          refine ⟨19248714806835044847519389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832476537890029898346259 19248714806835044847519389)
          ·
            refine ⟨7218268052563141817819771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19248714806835044847519389 7218268052563141817819771)
            ·
              refine ⟨10827402078844712726729657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218268052563141817819771 10827402078844712726729657)
              ·
                refine ⟨8120551559133534545047243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10827402078844712726729657 8120551559133534545047243)
                ·
                  refine ⟨12180827338700301817570865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120551559133534545047243 12180827338700301817570865)
                  ·
                    refine ⟨9135620504025226363178149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12180827338700301817570865 9135620504025226363178149)
                    ·
                      refine ⟨1712928844504729943095903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9135620504025226363178149 1712928844504729943095903)
                      ·
                        rfl

theorem cell23_3335917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3335917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335917 prefixEnd_3335917 := by exact prefixLift 3335917
  have htrace : WordTrace (prefixWord ++ tailWord_3335917) baseStart_3335917 baseEnd_3335917 := by
    simpa [prefixWord, tailWord_3335917, baseEnd_3335917] using wordTrace_append hprefix tailTrace_3335917
  have hstable : (prefixWord ++ tailWord_3335917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335917).length < 2 ^ (prefixWord ++ tailWord_3335917).sum := by decide
  have hdescent : baseEnd_3335917 < baseStart_3335917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335937 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3335937 : Nat := 118140960795 + 3335937 * 2 ^ 59
def prefixEnd_3335937 : Nat := 4983230072969 + 3 ^ 40 * 3335937 * 2
def baseEnd_3335937 : Nat := 1712939114117819864845811

theorem tailTrace_3335937 : CollatzResearch.WordTrace tailWord_3335937 prefixEnd_3335937 1712939114117819864845811 := by
  unfold tailWord_3335937
  simp only [CollatzResearch.WordTrace]
  refine ⟨121671618115477456525974065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81114412076984971017316043 121671618115477456525974065)
  ·
    refine ⟨91253713586608092394480549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121671618115477456525974065 91253713586608092394480549)
    ·
      refine ⟨17110071297489017323965103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91253713586608092394480549 17110071297489017323965103)
      ·
        refine ⟨25665106946233525985947655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17110071297489017323965103 25665106946233525985947655)
        ·
          refine ⟨38497660419350288978921483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25665106946233525985947655 38497660419350288978921483)
          ·
            refine ⟨57746490629025433468382225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38497660419350288978921483 57746490629025433468382225)
            ·
              refine ⟨43309867971769075101286669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57746490629025433468382225 43309867971769075101286669)
              ·
                refine ⟨16241200489413403162982501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43309867971769075101286669 16241200489413403162982501)
                ·
                  refine ⟨3045225091765013093059219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16241200489413403162982501 3045225091765013093059219)
                  ·
                    refine ⟨4567837637647519639588829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3045225091765013093059219 4567837637647519639588829)
                    ·
                      refine ⟨1712939114117819864845811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567837637647519639588829 1712939114117819864845811)
                      ·
                        rfl

theorem cell23_3335937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3335937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335937 prefixEnd_3335937 := by exact prefixLift 3335937
  have htrace : WordTrace (prefixWord ++ tailWord_3335937) baseStart_3335937 baseEnd_3335937 := by
    simpa [prefixWord, tailWord_3335937, baseEnd_3335937] using wordTrace_append hprefix tailTrace_3335937
  have hstable : (prefixWord ++ tailWord_3335937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335937).length < 2 ^ (prefixWord ++ tailWord_3335937).sum := by decide
  have hdescent : baseEnd_3335937 < baseStart_3335937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335938 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_3335938 : Nat := 118140960795 + 3335938 * 2 ^ 59
def prefixEnd_3335938 : Nat := 4983230072969 + 3 ^ 40 * 3335938 * 2
def baseEnd_3335938 : Nat := 1712939627598474360933307

theorem tailTrace_3335938 : CollatzResearch.WordTrace tailWord_3335938 prefixEnd_3335938 1712939627598474360933307 := by
  unfold tailWord_3335938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30417913647118458424190117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81114436392315889131173645 30417913647118458424190117)
  ·
    refine ⟨5703358808834710954535647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30417913647118458424190117 5703358808834710954535647)
    ·
      refine ⟨8555038213252066431803471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703358808834710954535647 8555038213252066431803471)
      ·
        refine ⟨12832557319878099647705207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555038213252066431803471 12832557319878099647705207)
        ·
          refine ⟨19248835979817149471557811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832557319878099647705207 19248835979817149471557811)
          ·
            refine ⟨28873253969725724207336717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19248835979817149471557811 28873253969725724207336717)
            ·
              refine ⟨10827470238647146577751269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28873253969725724207336717 10827470238647146577751269)
              ·
                refine ⟨2030150669746339983328363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10827470238647146577751269 2030150669746339983328363)
                ·
                  refine ⟨3045226004619509974992545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030150669746339983328363 3045226004619509974992545)
                  ·
                    refine ⟨2283919503464632481244409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045226004619509974992545 2283919503464632481244409)
                    ·
                      refine ⟨1712939627598474360933307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283919503464632481244409 1712939627598474360933307)
                      ·
                        rfl

theorem cell23_3335938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_3335938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335938 prefixEnd_3335938 := by exact prefixLift 3335938
  have htrace : WordTrace (prefixWord ++ tailWord_3335938) baseStart_3335938 baseEnd_3335938 := by
    simpa [prefixWord, tailWord_3335938, baseEnd_3335938] using wordTrace_append hprefix tailTrace_3335938
  have hstable : (prefixWord ++ tailWord_3335938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335938).length < 2 ^ (prefixWord ++ tailWord_3335938).sum := by decide
  have hdescent : baseEnd_3335938 < baseStart_3335938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335940 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3335940 : Nat := 118140960795 + 3335940 * 2 ^ 59
def prefixEnd_3335940 : Nat := 4983230072969 + 3 ^ 40 * 3335940 * 2
def baseEnd_3335940 : Nat := 570980218186594451036099

theorem tailTrace_3335940 : CollatzResearch.WordTrace tailWord_3335940 prefixEnd_3335940 570980218186594451036099 := by
  unfold tailWord_3335940
  simp only [CollatzResearch.WordTrace]
  refine ⟨60835863767233294019166637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81114485022977725358888849 60835863767233294019166637)
  ·
    refine ⟨22813448912712485257187489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60835863767233294019166637 22813448912712485257187489)
    ·
      refine ⟨17110086684534363942890617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22813448912712485257187489 17110086684534363942890617)
      ·
        refine ⟨12832565013400772957167963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17110086684534363942890617 12832565013400772957167963)
        ·
          refine ⟨19248847520101159435751945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832565013400772957167963 19248847520101159435751945)
          ·
            refine ⟨14436635640075869576813959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19248847520101159435751945 14436635640075869576813959)
            ·
              refine ⟨21654953460113804365220939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14436635640075869576813959 21654953460113804365220939)
              ·
                refine ⟨32482430190170706547831409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21654953460113804365220939 32482430190170706547831409)
                ·
                  refine ⟨24361822642628029910873557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32482430190170706547831409 24361822642628029910873557)
                  ·
                    refine ⟨570980218186594451036099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24361822642628029910873557 570980218186594451036099)
                    ·
                      rfl

theorem cell23_3335940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3335940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335940 prefixEnd_3335940 := by exact prefixLift 3335940
  have htrace : WordTrace (prefixWord ++ tailWord_3335940) baseStart_3335940 baseEnd_3335940 := by
    simpa [prefixWord, tailWord_3335940, baseEnd_3335940] using wordTrace_append hprefix tailTrace_3335940
  have hstable : (prefixWord ++ tailWord_3335940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335940).length < 2 ^ (prefixWord ++ tailWord_3335940).sum := by decide
  have hdescent : baseEnd_3335940 < baseStart_3335940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335947 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 3, 3, 2]
def baseStart_3335947 : Nat := 118140960795 + 3335947 * 2 ^ 59
def prefixEnd_3335947 : Nat := 4983230072969 + 3 ^ 40 * 3335947 * 2
def baseEnd_3335947 : Nat := 1712944248924364825720765

theorem tailTrace_3335947 : CollatzResearch.WordTrace tailWord_3335947 prefixEnd_3335947 1712944248924364825720765 := by
  unfold tailWord_3335947
  simp only [CollatzResearch.WordTrace]
  refine ⟨121671982845441228233838095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81114655230294152155892063 121671982845441228233838095)
  ·
    refine ⟨182507974268161842350757143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121671982845441228233838095 182507974268161842350757143)
    ·
      refine ⟨273761961402242763526135715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182507974268161842350757143 273761961402242763526135715)
      ·
        refine ⟨410642942103364145289203573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273761961402242763526135715 410642942103364145289203573)
        ·
          refine ⟨38497775822190388620862835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 410642942103364145289203573 38497775822190388620862835)
          ·
            refine ⟨57746663733285582931294253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38497775822190388620862835 57746663733285582931294253)
            ·
              refine ⟨21654998899982093599235345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57746663733285582931294253 21654998899982093599235345)
              ·
                refine ⟨16241249174986570199426509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21654998899982093599235345 16241249174986570199426509)
                ·
                  refine ⟨6090468440619963824784941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16241249174986570199426509 6090468440619963824784941)
                  ·
                    refine ⟨2283925665232486434294353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6090468440619963824784941 2283925665232486434294353)
                    ·
                      refine ⟨1712944248924364825720765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283925665232486434294353 1712944248924364825720765)
                      ·
                        rfl

theorem cell23_3335947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 3, 2].length) (baseStart_3335947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335947 prefixEnd_3335947 := by exact prefixLift 3335947
  have htrace : WordTrace (prefixWord ++ tailWord_3335947) baseStart_3335947 baseEnd_3335947 := by
    simpa [prefixWord, tailWord_3335947, baseEnd_3335947] using wordTrace_append hprefix tailTrace_3335947
  have hstable : (prefixWord ++ tailWord_3335947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335947).length < 2 ^ (prefixWord ++ tailWord_3335947).sum := by decide
  have hdescent : baseEnd_3335947 < baseStart_3335947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335954 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3335954 : Nat := 118140960795 + 3335954 * 2 ^ 59
def prefixEnd_3335954 : Nat := 4983230072969 + 3 ^ 40 * 3335954 * 2
def baseEnd_3335954 : Nat := 1712947843288946298333233

theorem tailTrace_3335954 : CollatzResearch.WordTrace tailWord_3335954 prefixEnd_3335954 1712947843288946298333233 := by
  unfold tailWord_3335954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30418059539103967107335729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81114825437610578952895277 30418059539103967107335729)
  ·
    refine ⟨22813544654327975330501797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30418059539103967107335729 22813544654327975330501797)
    ·
      refine ⟨4277539622686495374469087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22813544654327975330501797 4277539622686495374469087)
      ·
        refine ⟨6416309434029743061703631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277539622686495374469087 6416309434029743061703631)
        ·
          refine ⟨9624464151044614592555447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416309434029743061703631 9624464151044614592555447)
          ·
            refine ⟨14436696226566921888833171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624464151044614592555447 14436696226566921888833171)
            ·
              refine ⟨21655044339850382833249757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14436696226566921888833171 21655044339850382833249757)
              ·
                refine ⟨8120641627443893562468659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21655044339850382833249757 8120641627443893562468659)
                ·
                  refine ⟨12180962441165840343702989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120641627443893562468659 12180962441165840343702989)
                  ·
                    refine ⟨4567860915437190128888621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12180962441165840343702989 4567860915437190128888621)
                    ·
                      refine ⟨1712947843288946298333233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567860915437190128888621 1712947843288946298333233)
                      ·
                        rfl

theorem cell23_3335954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3335954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335954 prefixEnd_3335954 := by exact prefixLift 3335954
  have htrace : WordTrace (prefixWord ++ tailWord_3335954) baseStart_3335954 baseEnd_3335954 := by
    simpa [prefixWord, tailWord_3335954, baseEnd_3335954] using wordTrace_append hprefix tailTrace_3335954
  have hstable : (prefixWord ++ tailWord_3335954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335954).length < 2 ^ (prefixWord ++ tailWord_3335954).sum := by decide
  have hdescent : baseEnd_3335954 < baseStart_3335954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335964 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_3335964 : Nat := 118140960795 + 3335964 * 2 ^ 59
def prefixEnd_3335964 : Nat := 4983230072969 + 3 ^ 40 * 3335964 * 2
def baseEnd_3335964 : Nat := 1712952978095491259208187

theorem tailTrace_3335964 : CollatzResearch.WordTrace tailWord_3335964 prefixEnd_3335964 1712952978095491259208187 := by
  unfold tailWord_3335964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60836301443189820068603473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81115068590919760091471297 60836301443189820068603473)
  ·
    refine ⟨45627226082392365051452605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60836301443189820068603473 45627226082392365051452605)
    ·
      refine ⟨17110209780897136894294727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45627226082392365051452605 17110209780897136894294727)
      ·
        refine ⟨25665314671345705341442091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17110209780897136894294727 25665314671345705341442091)
        ·
          refine ⟨38497972007018558012163137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25665314671345705341442091 38497972007018558012163137)
          ·
            refine ⟨28873479005263918509122353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38497972007018558012163137 28873479005263918509122353)
            ·
              refine ⟨21655109253947938881841765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28873479005263918509122353 21655109253947938881841765)
              ·
                refine ⟨4060332985115238540345331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21655109253947938881841765 4060332985115238540345331)
                ·
                  refine ⟨6090499477672857810517997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4060332985115238540345331 6090499477672857810517997)
                  ·
                    refine ⟨2283937304127321678944249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6090499477672857810517997 2283937304127321678944249)
                    ·
                      refine ⟨1712952978095491259208187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283937304127321678944249 1712952978095491259208187)
                      ·
                        rfl

theorem cell23_3335964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_3335964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335964 prefixEnd_3335964 := by exact prefixLift 3335964
  have htrace : WordTrace (prefixWord ++ tailWord_3335964) baseStart_3335964 baseEnd_3335964 := by
    simpa [prefixWord, tailWord_3335964, baseEnd_3335964] using wordTrace_append hprefix tailTrace_3335964
  have hstable : (prefixWord ++ tailWord_3335964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335964).length < 2 ^ (prefixWord ++ tailWord_3335964).sum := by decide
  have hdescent : baseEnd_3335964 < baseStart_3335964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335970 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_3335970 : Nat := 118140960795 + 3335970 * 2 ^ 59
def prefixEnd_3335970 : Nat := 4983230072969 + 3 ^ 40 * 3335970 * 2
def baseEnd_3335970 : Nat := 570985352993139411911053

theorem tailTrace_3335970 : CollatzResearch.WordTrace tailWord_3335970 prefixEnd_3335970 570985352993139411911053 := by
  unfold tailWord_3335970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30418205431089475790481341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81115214482905268774616909 30418205431089475790481341)
  ·
    refine ⟨11406827036658553421430503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30418205431089475790481341 11406827036658553421430503)
    ·
      refine ⟨17110240554987830132145755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406827036658553421430503 17110240554987830132145755)
      ·
        refine ⟨25665360832481745198218633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17110240554987830132145755 25665360832481745198218633)
        ·
          refine ⟨19249020624361308898663975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25665360832481745198218633 19249020624361308898663975)
          ·
            refine ⟨28873530936541963347995963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19249020624361308898663975 28873530936541963347995963)
            ·
              refine ⟨43310296404812945021993945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28873530936541963347995963 43310296404812945021993945)
              ·
                refine ⟨32482722303609708766495459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43310296404812945021993945 32482722303609708766495459)
                ·
                  refine ⟨48724083455414563149743189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32482722303609708766495459 48724083455414563149743189)
                  ·
                    refine ⟨570985352993139411911053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48724083455414563149743189 570985352993139411911053)
                    ·
                      rfl

theorem cell23_3335970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_3335970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335970 prefixEnd_3335970 := by exact prefixLift 3335970
  have htrace : WordTrace (prefixWord ++ tailWord_3335970) baseStart_3335970 baseEnd_3335970 := by
    simpa [prefixWord, tailWord_3335970, baseEnd_3335970] using wordTrace_append hprefix tailTrace_3335970
  have hstable : (prefixWord ++ tailWord_3335970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335970).length < 2 ^ (prefixWord ++ tailWord_3335970).sum := by decide
  have hdescent : baseEnd_3335970 < baseStart_3335970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3335988 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_3335988 : Nat := 118140960795 + 3335988 * 2 ^ 59
def prefixEnd_3335988 : Nat := 4983230072969 + 3 ^ 40 * 3335988 * 2
def baseEnd_3335988 : Nat := 1712965301631199165308077

theorem tailTrace_3335988 : CollatzResearch.WordTrace tailWord_3335988 prefixEnd_3335988 1712965301631199165308077 := by
  unfold tailWord_3335988
  simp only [CollatzResearch.WordTrace]
  refine ⟨60836739119146346118040309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81115652158861794824053745 60836739119146346118040309)
  ·
    refine ⟨5703444292419969948566279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60836739119146346118040309 5703444292419969948566279)
    ·
      refine ⟨8555166438629954922849419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703444292419969948566279 8555166438629954922849419)
      ·
        refine ⟨12832749657944932384274129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555166438629954922849419 12832749657944932384274129)
        ·
          refine ⟨9624562243458699288205597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12832749657944932384274129 9624562243458699288205597)
          ·
            refine ⟨3609210841297012233077099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9624562243458699288205597 3609210841297012233077099)
            ·
              refine ⟨5413816261945518349615649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609210841297012233077099 5413816261945518349615649)
              ·
                refine ⟨4060362196459138762211737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5413816261945518349615649 4060362196459138762211737)
                ·
                  refine ⟨3045271647344354071658803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060362196459138762211737 3045271647344354071658803)
                  ·
                    refine ⟨4567907471016531107488205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3045271647344354071658803 4567907471016531107488205)
                    ·
                      refine ⟨1712965301631199165308077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4567907471016531107488205 1712965301631199165308077)
                      ·
                        rfl

theorem cell23_3335988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_3335988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3335988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3335988 prefixEnd_3335988 := by exact prefixLift 3335988
  have htrace : WordTrace (prefixWord ++ tailWord_3335988) baseStart_3335988 baseEnd_3335988 := by
    simpa [prefixWord, tailWord_3335988, baseEnd_3335988] using wordTrace_append hprefix tailTrace_3335988
  have hstable : (prefixWord ++ tailWord_3335988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3335988).length < 2 ^ (prefixWord ++ tailWord_3335988).sum := by decide
  have hdescent : baseEnd_3335988 < baseStart_3335988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3335988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336037 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 7, 2]
def baseStart_3336037 : Nat := 118140960795 + 3336037 * 2 ^ 59
def prefixEnd_3336037 : Nat := 4983230072969 + 3 ^ 40 * 3336037 * 2
def baseEnd_3336037 : Nat := 1712990462183269473595351

theorem tailTrace_3336037 : CollatzResearch.WordTrace tailWord_3336037 prefixEnd_3336037 1712990462183269473595351 := by
  unfold tailWord_3336037
  simp only [CollatzResearch.WordTrace]
  refine ⟨121675265415115173604614365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81116843610076782403076243 121675265415115173604614365)
  ·
    refine ⟨45628224530668190101730387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121675265415115173604614365 45628224530668190101730387)
    ·
      refine ⟨68442336796002285152595581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45628224530668190101730387 68442336796002285152595581)
      ·
        refine ⟨25665876298500856932223343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68442336796002285152595581 25665876298500856932223343)
        ·
          refine ⟨38498814447751285398335015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25665876298500856932223343 38498814447751285398335015)
          ·
            refine ⟨57748221671626928097502523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38498814447751285398335015 57748221671626928097502523)
            ·
              refine ⟨86622332507440392146253785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57748221671626928097502523 86622332507440392146253785)
              ·
                refine ⟨64966749380580294109690339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86622332507440392146253785 64966749380580294109690339)
                ·
                  refine ⟨97450124070870441164535509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64966749380580294109690339 97450124070870441164535509)
                  ·
                    refine ⟨2283987282911025964793801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 97450124070870441164535509 2283987282911025964793801)
                    ·
                      refine ⟨1712990462183269473595351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2283987282911025964793801 1712990462183269473595351)
                      ·
                        rfl

theorem cell23_3336037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_3336037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336037 prefixEnd_3336037 := by exact prefixLift 3336037
  have htrace : WordTrace (prefixWord ++ tailWord_3336037) baseStart_3336037 baseEnd_3336037 := by
    simpa [prefixWord, tailWord_3336037, baseEnd_3336037] using wordTrace_append hprefix tailTrace_3336037
  have hstable : (prefixWord ++ tailWord_3336037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336037).length < 2 ^ (prefixWord ++ tailWord_3336037).sum := by decide
  have hdescent : baseEnd_3336037 < baseStart_3336037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336062 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3336062 : Nat := 118140960795 + 3336062 * 2 ^ 59
def prefixEnd_3336062 : Nat := 4983230072969 + 3 ^ 40 * 3336062 * 2
def baseEnd_3336062 : Nat := 1713003299199631875782737

theorem tailTrace_3336062 : CollatzResearch.WordTrace tailWord_3336062 prefixEnd_3336062 1713003299199631875782737 := by
  unfold tailWord_3336062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15209522155003075359284305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81117451493349735249516293 15209522155003075359284305)
  ·
    refine ⟨11407141616252306519463229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15209522155003075359284305 11407141616252306519463229)
    ·
      refine ⟨4277678106094614944798711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11407141616252306519463229 4277678106094614944798711)
      ·
        refine ⟨6416517159141922417198067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277678106094614944798711 6416517159141922417198067)
        ·
          refine ⟨9624775738712883625797101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416517159141922417198067 9624775738712883625797101)
          ·
            refine ⟨3609290902017331359673913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9624775738712883625797101 3609290902017331359673913)
            ·
              refine ⟨2706968176512998519755435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609290902017331359673913 2706968176512998519755435)
              ·
                refine ⟨4060452264769497779633153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706968176512998519755435 4060452264769497779633153)
                ·
                  refine ⟨3045339198577123334724865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060452264769497779633153 3045339198577123334724865)
                  ·
                    refine ⟨2284004398932842501043649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045339198577123334724865 2284004398932842501043649)
                    ·
                      refine ⟨1713003299199631875782737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284004398932842501043649 1713003299199631875782737)
                      ·
                        rfl

theorem cell23_3336062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3336062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336062 prefixEnd_3336062 := by exact prefixLift 3336062
  have htrace : WordTrace (prefixWord ++ tailWord_3336062) baseStart_3336062 baseEnd_3336062 := by
    simpa [prefixWord, tailWord_3336062, baseEnd_3336062] using wordTrace_append hprefix tailTrace_3336062
  have hstable : (prefixWord ++ tailWord_3336062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336062).length < 2 ^ (prefixWord ++ tailWord_3336062).sum := by decide
  have hdescent : baseEnd_3336062 < baseStart_3336062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336080 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_3336080 : Nat := 118140960795 + 3336080 * 2 ^ 59
def prefixEnd_3336080 : Nat := 4983230072969 + 3 ^ 40 * 3336080 * 2
def baseEnd_3336080 : Nat := 1713012541851412805357653

theorem tailTrace_3336080 : CollatzResearch.WordTrace tailWord_3336080 prefixEnd_3336080 1713012541851412805357653 := by
  unfold tailWord_3336080
  simp only [CollatzResearch.WordTrace]
  refine ⟨60838416876979695974214847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81117889169306261298953129 60838416876979695974214847)
  ·
    refine ⟨91257625315469543961322271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60838416876979695974214847 91257625315469543961322271)
    ·
      refine ⟨136886437973204315941983407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91257625315469543961322271 136886437973204315941983407)
      ·
        refine ⟨205329656959806473912975111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136886437973204315941983407 205329656959806473912975111)
        ·
          refine ⟨307994485439709710869462667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205329656959806473912975111 307994485439709710869462667)
          ·
            refine ⟨461991728159564566304194001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307994485439709710869462667 461991728159564566304194001)
            ·
              refine ⟨346493796119673424728145501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461991728159564566304194001 346493796119673424728145501)
              ·
                refine ⟨129935173544877534273054563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346493796119673424728145501 129935173544877534273054563)
                ·
                  refine ⟨194902760317316301409581845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129935173544877534273054563 194902760317316301409581845)
                  ·
                    refine ⟨9136066889874201628574149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194902760317316301409581845 9136066889874201628574149)
                    ·
                      refine ⟨1713012541851412805357653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9136066889874201628574149 1713012541851412805357653)
                      ·
                        rfl

theorem cell23_3336080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_3336080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336080 prefixEnd_3336080 := by exact prefixLift 3336080
  have htrace : WordTrace (prefixWord ++ tailWord_3336080) baseStart_3336080 baseEnd_3336080 := by
    simpa [prefixWord, tailWord_3336080, baseEnd_3336080] using wordTrace_append hprefix tailTrace_3336080
  have hstable : (prefixWord ++ tailWord_3336080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336080).length < 2 ^ (prefixWord ++ tailWord_3336080).sum := by decide
  have hdescent : baseEnd_3336080 < baseStart_3336080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336084 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3336084 : Nat := 118140960795 + 3336084 * 2 ^ 59
def prefixEnd_3336084 : Nat := 4983230072969 + 3 ^ 40 * 3336084 * 2
def baseEnd_3336084 : Nat := 1713014595774030789707635

theorem tailTrace_3336084 : CollatzResearch.WordTrace tailWord_3336084 prefixEnd_3336084 1713014595774030789707635 := by
  unfold tailWord_3336084
  simp only [CollatzResearch.WordTrace]
  refine ⟨60838489822972450315787653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81117986430629933754383537 60838489822972450315787653)
  ·
    refine ⟨11407216841807334434210185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60838489822972450315787653 11407216841807334434210185)
    ·
      refine ⟨8555412631355500825657639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11407216841807334434210185 8555412631355500825657639)
      ·
        refine ⟨12833118947033251238486459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555412631355500825657639 12833118947033251238486459)
        ·
          refine ⟨19249678420549876857729689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12833118947033251238486459 19249678420549876857729689)
          ·
            refine ⟨14437258815412407643297267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19249678420549876857729689 14437258815412407643297267)
            ·
              refine ⟨21655888223118611464945901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14437258815412407643297267 21655888223118611464945901)
              ·
                refine ⟨8120958083669479299354713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21655888223118611464945901 8120958083669479299354713)
                ·
                  refine ⟨6090718562752109474516035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8120958083669479299354713 6090718562752109474516035)
                  ·
                    refine ⟨9136077844128164211774053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6090718562752109474516035 9136077844128164211774053)
                    ·
                      refine ⟨1713014595774030789707635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9136077844128164211774053 1713014595774030789707635)
                      ·
                        rfl

theorem cell23_3336084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3336084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336084 prefixEnd_3336084 := by exact prefixLift 3336084
  have htrace : WordTrace (prefixWord ++ tailWord_3336084) baseStart_3336084 baseEnd_3336084 := by
    simpa [prefixWord, tailWord_3336084, baseEnd_3336084] using wordTrace_append hprefix tailTrace_3336084
  have hstable : (prefixWord ++ tailWord_3336084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336084).length < 2 ^ (prefixWord ++ tailWord_3336084).sum := by decide
  have hdescent : baseEnd_3336084 < baseStart_3336084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336184 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 2, 4]
def baseStart_3336184 : Nat := 118140960795 + 3336184 * 2 ^ 59
def prefixEnd_3336184 : Nat := 4983230072969 + 3 ^ 40 * 3336184 * 2
def baseEnd_3336184 : Nat := 571021981279826799485725

theorem tailTrace_3336184 : CollatzResearch.WordTrace tailWord_3336184 prefixEnd_3336184 571021981279826799485725 := by
  unfold tailWord_3336184
  simp only [CollatzResearch.WordTrace]
  refine ⟨60840313472791308855107803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81120417963721745140143737 60840313472791308855107803)
  ·
    refine ⟨91260470209186963282661705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60840313472791308855107803 91260470209186963282661705)
    ·
      refine ⟨68445352656890222461996279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91260470209186963282661705 68445352656890222461996279)
      ·
        refine ⟨102668028985335333692994419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68445352656890222461996279 102668028985335333692994419)
        ·
          refine ⟨154002043478003000539491629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102668028985335333692994419 154002043478003000539491629)
          ·
            refine ⟨57750766304251125202309361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154002043478003000539491629 57750766304251125202309361)
            ·
              refine ⟨43313074728188343901732021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57750766304251125202309361 43313074728188343901732021)
              ·
                refine ⟨4060600755767657240787377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43313074728188343901732021 4060600755767657240787377)
                ·
                  refine ⟨3045450566825742930590533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060600755767657240787377 3045450566825742930590533)
                  ·
                    refine ⟨571021981279826799485725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045450566825742930590533 571021981279826799485725)
                    ·
                      rfl

theorem cell23_3336184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_3336184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336184 prefixEnd_3336184 := by exact prefixLift 3336184
  have htrace : WordTrace (prefixWord ++ tailWord_3336184) baseStart_3336184 baseEnd_3336184 := by
    simpa [prefixWord, tailWord_3336184, baseEnd_3336184] using wordTrace_append hprefix tailTrace_3336184
  have hstable : (prefixWord ++ tailWord_3336184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336184).length < 2 ^ (prefixWord ++ tailWord_3336184).sum := by decide
  have hdescent : baseEnd_3336184 < baseStart_3336184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336197 : List Nat := [1, 3, 1, 1, 2, 5, 1, 9]
def baseStart_3336197 : Nat := 118140960795 + 3336197 * 2 ^ 59
def prefixEnd_3336197 : Nat := 4983230072969 + 3 ^ 40 * 3336197 * 2
def baseEnd_3336197 : Nat := 63447134040295883244245

theorem tailTrace_3336197 : CollatzResearch.WordTrace tailWord_3336197 prefixEnd_3336197 63447134040295883244245 := by
  unfold tailWord_3336197
  simp only [CollatzResearch.WordTrace]
  refine ⟨121681101094535520930438845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81120734063023680620292563 121681101094535520930438845)
  ·
    refine ⟨45630412910450820348914567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121681101094535520930438845 45630412910450820348914567)
    ·
      refine ⟨68445619365676230523371851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45630412910450820348914567 68445619365676230523371851)
      ·
        refine ⟨102668429048514345785057777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68445619365676230523371851 102668429048514345785057777)
        ·
          refine ⟨77001321786385759338793333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102668429048514345785057777 77001321786385759338793333)
          ·
            refine ⟨7218873917473664938011875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77001321786385759338793333 7218873917473664938011875)
            ·
              refine ⟨10828310876210497407017813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218873917473664938011875 10828310876210497407017813)
              ·
                refine ⟨63447134040295883244245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10828310876210497407017813 63447134040295883244245)
                ·
                  rfl

theorem cell23_3336197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 9].length) (baseStart_3336197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336197 prefixEnd_3336197 := by exact prefixLift 3336197
  have htrace : WordTrace (prefixWord ++ tailWord_3336197) baseStart_3336197 baseEnd_3336197 := by
    simpa [prefixWord, tailWord_3336197, baseEnd_3336197] using wordTrace_append hprefix tailTrace_3336197
  have hstable : (prefixWord ++ tailWord_3336197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336197).length < 2 ^ (prefixWord ++ tailWord_3336197).sum := by decide
  have hdescent : baseEnd_3336197 < baseStart_3336197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336202 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3]
def baseStart_3336202 : Nat := 118140960795 + 3336202 * 2 ^ 59
def prefixEnd_3336202 : Nat := 4983230072969 + 3 ^ 40 * 3336202 * 2
def baseEnd_3336202 : Nat := 1713075186491261328032093

theorem tailTrace_3336202 : CollatzResearch.WordTrace tailWord_3336202 prefixEnd_3336202 1713075186491261328032093 := by
  unfold tailWord_3336202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420320864879351696092715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81120855639678271189580573 30420320864879351696092715)
  ·
    refine ⟨45630481297319027544139073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30420320864879351696092715 45630481297319027544139073)
    ·
      refine ⟨34222860972989270658104305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45630481297319027544139073 34222860972989270658104305)
      ·
        refine ⟨25667145729741952993578229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34222860972989270658104305 25667145729741952993578229)
        ·
          refine ⟨2406294912163308093147959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25667145729741952993578229 2406294912163308093147959)
          ·
            refine ⟨3609442368244962139721939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406294912163308093147959 3609442368244962139721939)
            ·
              refine ⟨5414163552367443209582909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609442368244962139721939 5414163552367443209582909)
              ·
                refine ⟨2030311332137791203593591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5414163552367443209582909 2030311332137791203593591)
                ·
                  refine ⟨3045466998206686805390387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030311332137791203593591 3045466998206686805390387)
                  ·
                    refine ⟨4568200497310030208085581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3045466998206686805390387 4568200497310030208085581)
                    ·
                      refine ⟨1713075186491261328032093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4568200497310030208085581 1713075186491261328032093)
                      ·
                        rfl

theorem cell23_3336202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_3336202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336202 prefixEnd_3336202 := by exact prefixLift 3336202
  have htrace : WordTrace (prefixWord ++ tailWord_3336202) baseStart_3336202 baseEnd_3336202 := by
    simpa [prefixWord, tailWord_3336202, baseEnd_3336202] using wordTrace_append hprefix tailTrace_3336202
  have hstable : (prefixWord ++ tailWord_3336202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336202).length < 2 ^ (prefixWord ++ tailWord_3336202).sum := by decide
  have hdescent : baseEnd_3336202 < baseStart_3336202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336225 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 3, 2, 2]
def baseStart_3336225 : Nat := 118140960795 + 3336225 * 2 ^ 59
def prefixEnd_3336225 : Nat := 4983230072969 + 3 ^ 40 * 3336225 * 2
def baseEnd_3336225 : Nat := 1713086996546314738044487

theorem tailTrace_3336225 : CollatzResearch.WordTrace tailWord_3336225 prefixEnd_3336225 1713086996546314738044487 := by
  unfold tailWord_3336225
  simp only [CollatzResearch.WordTrace]
  refine ⟨121682122338434081712458129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81121414892289387808305419 121682122338434081712458129)
  ·
    refine ⟨91261591753825561284343597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121682122338434081712458129 91261591753825561284343597)
    ·
      refine ⟨34223096907684585481628849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91261591753825561284343597 34223096907684585481628849)
      ·
        refine ⟨25667322680763439111221637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34223096907684585481628849 25667322680763439111221637)
        ·
          refine ⟨4812623002643144833354057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25667322680763439111221637 4812623002643144833354057)
          ·
            refine ⟨3609467251982358625015543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812623002643144833354057 3609467251982358625015543)
            ·
              refine ⟨5414200877973537937523315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609467251982358625015543 5414200877973537937523315)
              ·
                refine ⟨8121301316960306906284973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414200877973537937523315 8121301316960306906284973)
                ·
                  refine ⟨3045487993860115089856865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8121301316960306906284973 3045487993860115089856865)
                  ·
                    refine ⟨2284115995395086317392649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045487993860115089856865 2284115995395086317392649)
                    ·
                      refine ⟨1713086996546314738044487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284115995395086317392649 1713086996546314738044487)
                      ·
                        rfl

theorem cell23_3336225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_3336225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336225 prefixEnd_3336225 := by exact prefixLift 3336225
  have htrace : WordTrace (prefixWord ++ tailWord_3336225) baseStart_3336225 baseEnd_3336225 := by
    simpa [prefixWord, tailWord_3336225, baseEnd_3336225] using wordTrace_append hprefix tailTrace_3336225
  have hstable : (prefixWord ++ tailWord_3336225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336225).length < 2 ^ (prefixWord ++ tailWord_3336225).sum := by decide
  have hdescent : baseEnd_3336225 < baseStart_3336225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336227 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 7]
def baseStart_3336227 : Nat := 118140960795 + 3336227 * 2 ^ 59
def prefixEnd_3336227 : Nat := 4983230072969 + 3 ^ 40 * 3336227 * 2
def baseEnd_3336227 : Nat := 571029341169207910073159

theorem tailTrace_3336227 : CollatzResearch.WordTrace tailWord_3336227 prefixEnd_3336227 571029341169207910073159 := by
  unfold tailWord_3336227
  simp only [CollatzResearch.WordTrace]
  refine ⟨121682195284426836054030935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81121463522951224036020623 121682195284426836054030935)
  ·
    refine ⟨182523292926640254081046403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121682195284426836054030935 182523292926640254081046403)
    ·
      refine ⟨273784939389960381121569605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182523292926640254081046403 273784939389960381121569605)
      ·
        refine ⟨51334676135617571460294301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273784939389960381121569605 51334676135617571460294301)
        ·
          refine ⟨19250503550856589297610363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51334676135617571460294301 19250503550856589297610363)
          ·
            refine ⟨28875755326284883946415545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19250503550856589297610363 28875755326284883946415545)
            ·
              refine ⟨21656816494713662959811659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28875755326284883946415545 21656816494713662959811659)
              ·
                refine ⟨32485224742070494439717489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21656816494713662959811659 32485224742070494439717489)
                ·
                  refine ⟨24363918556552870829788117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32485224742070494439717489 24363918556552870829788117)
                  ·
                    refine ⟨571029341169207910073159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24363918556552870829788117 571029341169207910073159)
                    ·
                      rfl

theorem cell23_3336227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_3336227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336227 prefixEnd_3336227 := by exact prefixLift 3336227
  have htrace : WordTrace (prefixWord ++ tailWord_3336227) baseStart_3336227 baseEnd_3336227 := by
    simpa [prefixWord, tailWord_3336227, baseEnd_3336227] using wordTrace_append hprefix tailTrace_3336227
  have hstable : (prefixWord ++ tailWord_3336227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336227).length < 2 ^ (prefixWord ++ tailWord_3336227).sum := by decide
  have hdescent : baseEnd_3336227 < baseStart_3336227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336231 : List Nat := [1, 1, 7, 1, 2, 1, 2, 8]
def baseStart_3336231 : Nat := 118140960795 + 3336231 * 2 ^ 59
def prefixEnd_3336231 : Nat := 4983230072969 + 3 ^ 40 * 3336231 * 2
def baseEnd_3336231 : Nat := 63447780645564507947017

theorem tailTrace_3336231 : CollatzResearch.WordTrace tailWord_3336231 prefixEnd_3336231 63447780645564507947017 := by
  unfold tailWord_3336231
  simp only [CollatzResearch.WordTrace]
  refine ⟨121682341176412344737176547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81121560784274896491451031 121682341176412344737176547)
  ·
    refine ⟨182523511764618517105764821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121682341176412344737176547 182523511764618517105764821)
    ·
      refine ⟨4277894806983246494666363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 182523511764618517105764821 4277894806983246494666363)
      ·
        refine ⟨6416842210474869741999545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277894806983246494666363 6416842210474869741999545)
        ·
          refine ⟨4812631657856152306499659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6416842210474869741999545 4812631657856152306499659)
          ·
            refine ⟨7218947486784228459749489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812631657856152306499659 7218947486784228459749489)
            ·
              refine ⟨5414210615088171344812117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7218947486784228459749489 5414210615088171344812117)
              ·
                refine ⟨63447780645564507947017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5414210615088171344812117 63447780645564507947017)
                ·
                  rfl

theorem cell23_3336231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 8].length) (baseStart_3336231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336231 prefixEnd_3336231 := by exact prefixLift 3336231
  have htrace : WordTrace (prefixWord ++ tailWord_3336231) baseStart_3336231 baseEnd_3336231 := by
    simpa [prefixWord, tailWord_3336231, baseEnd_3336231] using wordTrace_append hprefix tailTrace_3336231
  have hstable : (prefixWord ++ tailWord_3336231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336231).length < 2 ^ (prefixWord ++ tailWord_3336231).sum := by decide
  have hdescent : baseEnd_3336231 < baseStart_3336231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336304 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 7]
def baseStart_3336304 : Nat := 118140960795 + 3336304 * 2 ^ 59
def prefixEnd_3336304 : Nat := 4983230072969 + 3 ^ 40 * 3336304 * 2
def baseEnd_3336304 : Nat := 190347506835335547661847

theorem tailTrace_3336304 : CollatzResearch.WordTrace tailWord_3336304 prefixEnd_3336304 190347506835335547661847 := by
  unfold tailWord_3336304
  simp only [CollatzResearch.WordTrace]
  refine ⟨60842501852573939102291983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81123335803431918803055977 60842501852573939102291983)
  ·
    refine ⟨91263752778860908653437975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60842501852573939102291983 91263752778860908653437975)
    ·
      refine ⟨136895629168291362980156963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91263752778860908653437975 136895629168291362980156963)
      ·
        refine ⟨205343443752437044470235445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136895629168291362980156963 205343443752437044470235445)
        ·
          refine ⟨19250947851790972919084573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205343443752437044470235445 19250947851790972919084573)
          ·
            refine ⟨7219105444421614844656715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19250947851790972919084573 7219105444421614844656715)
            ·
              refine ⟨10828658166632422266985073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219105444421614844656715 10828658166632422266985073)
              ·
                refine ⟨8121493624974316700238805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828658166632422266985073 8121493624974316700238805)
                ·
                  refine ⟨190347506835335547661847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8121493624974316700238805 190347506835335547661847)
                  ·
                    rfl

theorem cell23_3336304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_3336304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336304 prefixEnd_3336304 := by exact prefixLift 3336304
  have htrace : WordTrace (prefixWord ++ tailWord_3336304) baseStart_3336304 baseEnd_3336304 := by
    simpa [prefixWord, tailWord_3336304, baseEnd_3336304] using wordTrace_append hprefix tailTrace_3336304
  have hstable : (prefixWord ++ tailWord_3336304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336304).length < 2 ^ (prefixWord ++ tailWord_3336304).sum := by decide
  have hdescent : baseEnd_3336304 < baseStart_3336304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336388 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3336388 : Nat := 118140960795 + 3336388 * 2 ^ 59
def prefixEnd_3336388 : Nat := 4983230072969 + 3 ^ 40 * 3336388 * 2
def baseEnd_3336388 : Nat := 1713170693892997600306237

theorem tailTrace_3336388 : CollatzResearch.WordTrace tailWord_3336388 prefixEnd_3336388 1713170693892997600306237 := by
  unfold tailWord_3336388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60844033718421780275320909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81125378291229040367094545 60844033718421780275320909)
  ·
    refine ⟨22816512644408167603245341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60844033718421780275320909 22816512644408167603245341)
    ·
      refine ⟨8556192241653062851217003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22816512644408167603245341 8556192241653062851217003)
      ·
        refine ⟨12834288362479594276825505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556192241653062851217003 12834288362479594276825505)
        ·
          refine ⟨9625716271859695707619129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12834288362479594276825505 9625716271859695707619129)
          ·
            refine ⟨7219287203894771780714347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9625716271859695707619129 7219287203894771780714347)
            ·
              refine ⟨10828930805842157671071521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219287203894771780714347 10828930805842157671071521)
              ·
                refine ⟨8121698104381618253303641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828930805842157671071521 8121698104381618253303641)
                ·
                  refine ⟨6091273578286213689977731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121698104381618253303641 6091273578286213689977731)
                  ·
                    refine ⟨9136910367429320534966597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6091273578286213689977731 9136910367429320534966597)
                    ·
                      refine ⟨1713170693892997600306237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9136910367429320534966597 1713170693892997600306237)
                      ·
                        rfl

theorem cell23_3336388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3336388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336388 prefixEnd_3336388 := by exact prefixLift 3336388
  have htrace : WordTrace (prefixWord ++ tailWord_3336388) baseStart_3336388 baseEnd_3336388 := by
    simpa [prefixWord, tailWord_3336388, baseEnd_3336388] using wordTrace_append hprefix tailTrace_3336388
  have hstable : (prefixWord ++ tailWord_3336388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336388).length < 2 ^ (prefixWord ++ tailWord_3336388).sum := by decide
  have hdescent : baseEnd_3336388 < baseStart_3336388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336394 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 8]
def baseStart_3336394 : Nat := 118140960795 + 3336394 * 2 ^ 59
def prefixEnd_3336394 : Nat := 4983230072969 + 3 ^ 40 * 3336394 * 2
def baseEnd_3336394 : Nat := 190352641641880508536801

theorem tailTrace_3336394 : CollatzResearch.WordTrace tailWord_3336394 prefixEnd_3336394 190352641641880508536801 := by
  unfold tailWord_3336394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422071568705455893840059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81125524183214549050240157 30422071568705455893840059)
  ·
    refine ⟨45633107353058183840760089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30422071568705455893840059 45633107353058183840760089)
    ·
      refine ⟨34224830514793637880570067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45633107353058183840760089 34224830514793637880570067)
      ·
        refine ⟨51337245772190456820855101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34224830514793637880570067 51337245772190456820855101)
        ·
          refine ⟨19251467164571421307820663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51337245772190456820855101 19251467164571421307820663)
          ·
            refine ⟨28877200746857131961730995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19251467164571421307820663 28877200746857131961730995)
            ·
              refine ⟨43315801120285697942596493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28877200746857131961730995 43315801120285697942596493)
              ·
                refine ⟨16243425420107136728473685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43315801120285697942596493 16243425420107136728473685)
                ·
                  refine ⟨190352641641880508536801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16243425420107136728473685 190352641641880508536801)
                  ·
                    rfl

theorem cell23_3336394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 8].length) (baseStart_3336394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336394 prefixEnd_3336394 := by exact prefixLift 3336394
  have htrace : WordTrace (prefixWord ++ tailWord_3336394) baseStart_3336394 baseEnd_3336394 := by
    simpa [prefixWord, tailWord_3336394, baseEnd_3336394] using wordTrace_append hprefix tailTrace_3336394
  have hstable : (prefixWord ++ tailWord_3336394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336394).length < 2 ^ (prefixWord ++ tailWord_3336394).sum := by decide
  have hdescent : baseEnd_3336394 < baseStart_3336394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336398 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_3336398 : Nat := 118140960795 + 3336398 * 2 ^ 59
def prefixEnd_3336398 : Nat := 4983230072969 + 3 ^ 40 * 3336398 * 2
def baseEnd_3336398 : Nat := 571058609566514187060397

theorem tailTrace_3336398 : CollatzResearch.WordTrace tailWord_3336398 prefixEnd_3336398 571058609566514187060397 := by
  unfold tailWord_3336398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15211054020850916532313231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81125621444538221505670565 15211054020850916532313231)
  ·
    refine ⟨22816581031276374798469847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15211054020850916532313231 22816581031276374798469847)
    ·
      refine ⟨34224871546914562197704771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22816581031276374798469847 34224871546914562197704771)
      ·
        refine ⟨51337307320371843296557157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34224871546914562197704771 51337307320371843296557157)
        ·
          refine ⟨9625745122569720618104467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51337307320371843296557157 9625745122569720618104467)
          ·
            refine ⟨14438617683854580927156701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9625745122569720618104467 14438617683854580927156701)
            ·
              refine ⟨5414481631445467847683763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14438617683854580927156701 5414481631445467847683763)
              ·
                refine ⟨8121722447168201771525645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414481631445467847683763 8121722447168201771525645)
                ·
                  refine ⟨3045645917688075664322117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8121722447168201771525645 3045645917688075664322117)
                  ·
                    refine ⟨571058609566514187060397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045645917688075664322117 571058609566514187060397)
                    ·
                      rfl

theorem cell23_3336398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_3336398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336398 prefixEnd_3336398 := by exact prefixLift 3336398
  have htrace : WordTrace (prefixWord ++ tailWord_3336398) baseStart_3336398 baseEnd_3336398 := by
    simpa [prefixWord, tailWord_3336398, baseEnd_3336398] using wordTrace_append hprefix tailTrace_3336398
  have hstable : (prefixWord ++ tailWord_3336398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336398).length < 2 ^ (prefixWord ++ tailWord_3336398).sum := by decide
  have hdescent : baseEnd_3336398 < baseStart_3336398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336448 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2]
def baseStart_3336448 : Nat := 118140960795 + 3336448 * 2 ^ 59
def prefixEnd_3336448 : Nat := 4983230072969 + 3 ^ 40 * 3336448 * 2
def baseEnd_3336448 : Nat := 1713201502732267365555961

theorem tailTrace_3336448 : CollatzResearch.WordTrace tailWord_3336448 prefixEnd_3336448 1713201502732267365555961 := by
  unfold tailWord_3336448
  simp only [CollatzResearch.WordTrace]
  refine ⟨60845127908313095398912999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81126837211084127198550665 60845127908313095398912999)
  ·
    refine ⟨91267691862469643098369499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60845127908313095398912999 91267691862469643098369499)
    ·
      refine ⟨136901537793704464647554249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91267691862469643098369499 136901537793704464647554249)
      ·
        refine ⟨102676153345278348485665687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136901537793704464647554249 102676153345278348485665687)
        ·
          refine ⟨154014230017917522728498531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102676153345278348485665687 154014230017917522728498531)
          ·
            refine ⟨231021345026876284092747797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154014230017917522728498531 231021345026876284092747797)
            ·
              refine ⟨10829125548134825816847553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231021345026876284092747797 10829125548134825816847553)
              ·
                refine ⟨8121844161101119362635665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829125548134825816847553 8121844161101119362635665)
                ·
                  refine ⟨6091383120825839521976749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121844161101119362635665 6091383120825839521976749)
                  ·
                    refine ⟨2284268670309689820741281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6091383120825839521976749 2284268670309689820741281)
                    ·
                      refine ⟨1713201502732267365555961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284268670309689820741281 1713201502732267365555961)
                      ·
                        rfl

theorem cell23_3336448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_3336448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336448 prefixEnd_3336448 := by exact prefixLift 3336448
  have htrace : WordTrace (prefixWord ++ tailWord_3336448) baseStart_3336448 baseEnd_3336448 := by
    simpa [prefixWord, tailWord_3336448, baseEnd_3336448] using wordTrace_append hprefix tailTrace_3336448
  have hstable : (prefixWord ++ tailWord_3336448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336448).length < 2 ^ (prefixWord ++ tailWord_3336448).sum := by decide
  have hdescent : baseEnd_3336448 < baseStart_3336448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336471 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 1, 6]
def baseStart_3336471 : Nat := 118140960795 + 3336471 * 2 ^ 59
def prefixEnd_3336471 : Nat := 4983230072969 + 3 ^ 40 * 3336471 * 2
def baseEnd_3336471 : Nat := 571071104262440258522785

theorem tailTrace_3336471 : CollatzResearch.WordTrace tailWord_3336471 prefixEnd_3336471 571071104262440258522785 := by
  unfold tailWord_3336471
  simp only [CollatzResearch.WordTrace]
  refine ⟨121691094695542865725913267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81127396463695243817275511 121691094695542865725913267)
  ·
    refine ⟨182536642043314298588869901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121691094695542865725913267 182536642043314298588869901)
    ·
      refine ⟨68451240766242861970826213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182536642043314298588869901 68451240766242861970826213)
      ·
        refine ⟨12834607643670536619529915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68451240766242861970826213 12834607643670536619529915)
        ·
          refine ⟨19251911465505804929294873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12834607643670536619529915 19251911465505804929294873)
          ·
            refine ⟨14438933599129353696971155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19251911465505804929294873 14438933599129353696971155)
            ·
              refine ⟨21658400398694030545456733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14438933599129353696971155 21658400398694030545456733)
              ·
                refine ⟨8121900149510261454546275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21658400398694030545456733 8121900149510261454546275)
                ·
                  refine ⟨12182850224265392181819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8121900149510261454546275 12182850224265392181819413)
                  ·
                    refine ⟨571071104262440258522785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12182850224265392181819413 571071104262440258522785)
                    ·
                      rfl

theorem cell23_3336471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_3336471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336471 prefixEnd_3336471 := by exact prefixLift 3336471
  have htrace : WordTrace (prefixWord ++ tailWord_3336471) baseStart_3336471 baseEnd_3336471 := by
    simpa [prefixWord, tailWord_3336471, baseEnd_3336471] using wordTrace_append hprefix tailTrace_3336471
  have hstable : (prefixWord ++ tailWord_3336471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336471).length < 2 ^ (prefixWord ++ tailWord_3336471).sum := by decide
  have hdescent : baseEnd_3336471 < baseStart_3336471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336482 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_3336482 : Nat := 118140960795 + 3336482 * 2 ^ 59
def prefixEnd_3336482 : Nat := 4983230072969 + 3 ^ 40 * 3336482 * 2
def baseEnd_3336482 : Nat := 1713218961074520232530805

theorem tailTrace_3336482 : CollatzResearch.WordTrace tailWord_3336482 prefixEnd_3336482 1713218961074520232530805 := by
  unfold tailWord_3336482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422873974625753651140925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81127663932335343069709133 30422873974625753651140925)
  ·
    refine ⟨11408577740484657619177847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30422873974625753651140925 11408577740484657619177847)
    ·
      refine ⟨17112866610726986428766771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11408577740484657619177847 17112866610726986428766771)
      ·
        refine ⟨25669299916090479643150157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17112866610726986428766771 25669299916090479643150157)
        ·
          refine ⟨9625987468533929866181309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25669299916090479643150157 9625987468533929866181309)
          ·
            refine ⟨3609745300700223699817991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9625987468533929866181309 3609745300700223699817991)
            ·
              refine ⟨5414617951050335549726987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609745300700223699817991 5414617951050335549726987)
              ·
                refine ⟨8121926926575503324590481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414617951050335549726987 8121926926575503324590481)
                ·
                  refine ⟨6091445194931627493442861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121926926575503324590481 6091445194931627493442861)
                  ·
                    refine ⟨2284291948099360310041073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6091445194931627493442861 2284291948099360310041073)
                    ·
                      refine ⟨1713218961074520232530805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284291948099360310041073 1713218961074520232530805)
                      ·
                        rfl

theorem cell23_3336482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_3336482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336482 prefixEnd_3336482 := by exact prefixLift 3336482
  have htrace : WordTrace (prefixWord ++ tailWord_3336482) baseStart_3336482 baseEnd_3336482 := by
    simpa [prefixWord, tailWord_3336482, baseEnd_3336482] using wordTrace_append hprefix tailTrace_3336482
  have hstable : (prefixWord ++ tailWord_3336482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336482).length < 2 ^ (prefixWord ++ tailWord_3336482).sum := by decide
  have hdescent : baseEnd_3336482 < baseStart_3336482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336505 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_3336505 : Nat := 118140960795 + 3336505 * 2 ^ 59
def prefixEnd_3336505 : Nat := 4983230072969 + 3 ^ 40 * 3336505 * 2
def baseEnd_3336505 : Nat := 571076923709857880847733

theorem tailTrace_3336505 : CollatzResearch.WordTrace tailWord_3336505 prefixEnd_3336505 571076923709857880847733 := by
  unfold tailWord_3336505
  simp only [CollatzResearch.WordTrace]
  refine ⟨121692334777419689532650969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81128223184946459688433979 121692334777419689532650969)
  ·
    refine ⟨91269251083064767149488227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121692334777419689532650969 91269251083064767149488227)
    ·
      refine ⟨136903876624597150724232341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91269251083064767149488227 136903876624597150724232341)
      ·
        refine ⟨6417369216777991440198391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136903876624597150724232341 6417369216777991440198391)
        ·
          refine ⟨9626053825166987160297587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6417369216777991440198391 9626053825166987160297587)
          ·
            refine ⟨14439080737750480740446381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9626053825166987160297587 14439080737750480740446381)
            ·
              refine ⟨5414655276656430277667393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14439080737750480740446381 5414655276656430277667393)
              ·
                refine ⟨4060991457492322708250545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5414655276656430277667393 4060991457492322708250545)
                ·
                  refine ⟨3045743593119242031187909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060991457492322708250545 3045743593119242031187909)
                  ·
                    refine ⟨571076923709857880847733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045743593119242031187909 571076923709857880847733)
                    ·
                      rfl

theorem cell23_3336505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_3336505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336505 prefixEnd_3336505 := by exact prefixLift 3336505
  have htrace : WordTrace (prefixWord ++ tailWord_3336505) baseStart_3336505 baseEnd_3336505 := by
    simpa [prefixWord, tailWord_3336505, baseEnd_3336505] using wordTrace_append hprefix tailTrace_3336505
  have hstable : (prefixWord ++ tailWord_3336505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336505).length < 2 ^ (prefixWord ++ tailWord_3336505).sum := by decide
  have hdescent : baseEnd_3336505 < baseStart_3336505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336528 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3]
def baseStart_3336528 : Nat := 118140960795 + 3336528 * 2 ^ 59
def prefixEnd_3336528 : Nat := 4983230072969 + 3 ^ 40 * 3336528 * 2
def baseEnd_3336528 : Nat := 1713242581184627052555593

theorem tailTrace_3336528 : CollatzResearch.WordTrace tailWord_3336528 prefixEnd_3336528 1713242581184627052555593 := by
  unfold tailWord_3336528
  simp only [CollatzResearch.WordTrace]
  refine ⟨60846586828168182230369119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81128782437557576307158825 60846586828168182230369119)
  ·
    refine ⟨91269880242252273345553679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60846586828168182230369119 91269880242252273345553679)
    ·
      refine ⟨136904820363378410018330519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91269880242252273345553679 136904820363378410018330519)
      ·
        refine ⟨205357230545067615027495779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136904820363378410018330519 205357230545067615027495779)
        ·
          refine ⟨308035845817601422541243669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205357230545067615027495779 308035845817601422541243669)
          ·
            refine ⟨14439180272700066681620797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308035845817601422541243669 14439180272700066681620797)
            ·
              refine ⟨5414692602262525005607799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14439180272700066681620797 5414692602262525005607799)
              ·
                refine ⟨8122038903393787508411699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414692602262525005607799 8122038903393787508411699)
                ·
                  refine ⟨12183058355090681262617549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122038903393787508411699 12183058355090681262617549)
                  ·
                    refine ⟨4568646883159005473481581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12183058355090681262617549 4568646883159005473481581)
                    ·
                      refine ⟨1713242581184627052555593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4568646883159005473481581 1713242581184627052555593)
                      ·
                        rfl

theorem cell23_3336528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_3336528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336528 prefixEnd_3336528 := by exact prefixLift 3336528
  have htrace : WordTrace (prefixWord ++ tailWord_3336528) baseStart_3336528 baseEnd_3336528 := by
    simpa [prefixWord, tailWord_3336528, baseEnd_3336528] using wordTrace_append hprefix tailTrace_3336528
  have hstable : (prefixWord ++ tailWord_3336528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336528).length < 2 ^ (prefixWord ++ tailWord_3336528).sum := by decide
  have hdescent : baseEnd_3336528 < baseStart_3336528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336546 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3336546 : Nat := 118140960795 + 3336546 * 2 ^ 59
def prefixEnd_3336546 : Nat := 4983230072969 + 3 ^ 40 * 3336546 * 2
def baseEnd_3336546 : Nat := 1713251823836407982130511

theorem tailTrace_3336546 : CollatzResearch.WordTrace tailWord_3336546 prefixEnd_3336546 1713251823836407982130511 := by
  unfold tailWord_3336546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30423457542567788383723373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81129220113514102356595661 30423457542567788383723373)
  ·
    refine ⟨11408796578462920643896265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30423457542567788383723373 11408796578462920643896265)
    ·
      refine ⟨8556597433847190482922199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11408796578462920643896265 8556597433847190482922199)
      ·
        refine ⟨12834896150770785724383299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556597433847190482922199 12834896150770785724383299)
        ·
          refine ⟨19252344226156178586574949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12834896150770785724383299 19252344226156178586574949)
          ·
            refine ⟨3609814542404283484982803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19252344226156178586574949 3609814542404283484982803)
            ·
              refine ⟨5414721813606425227474205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609814542404283484982803 5414721813606425227474205)
              ·
                refine ⟨2030520680102409460302827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5414721813606425227474205 2030520680102409460302827)
                ·
                  refine ⟨3045781020153614190454241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030520680102409460302827 3045781020153614190454241)
                  ·
                    refine ⟨2284335765115210642840681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3045781020153614190454241 2284335765115210642840681)
                    ·
                      refine ⟨1713251823836407982130511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284335765115210642840681 1713251823836407982130511)
                      ·
                        rfl

theorem cell23_3336546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3336546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336546 prefixEnd_3336546 := by exact prefixLift 3336546
  have htrace : WordTrace (prefixWord ++ tailWord_3336546) baseStart_3336546 baseEnd_3336546 := by
    simpa [prefixWord, tailWord_3336546, baseEnd_3336546] using wordTrace_append hprefix tailTrace_3336546
  have hstable : (prefixWord ++ tailWord_3336546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336546).length < 2 ^ (prefixWord ++ tailWord_3336546).sum := by decide
  have hdescent : baseEnd_3336546 < baseStart_3336546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336579 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 2, 1, 3]
def baseStart_3336579 : Nat := 118140960795 + 3336579 * 2 ^ 59
def prefixEnd_3336579 : Nat := 4983230072969 + 3 ^ 40 * 3336579 * 2
def baseEnd_3336579 : Nat := 1713268768698006353017859

theorem tailTrace_3336579 : CollatzResearch.WordTrace tailWord_3336579 prefixEnd_3336579 1713268768698006353017859 := by
  unfold tailWord_3336579
  simp only [CollatzResearch.WordTrace]
  refine ⟨121695033779151600170844791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81130022519434400113896527 121695033779151600170844791)
  ·
    refine ⟨182542550668727400256267187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121695033779151600170844791 182542550668727400256267187)
    ·
      refine ⟨273813826003091100384400781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182542550668727400256267187 273813826003091100384400781)
      ·
        refine ⟨102680184751159162644150293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273813826003091100384400781 102680184751159162644150293)
        ·
          refine ⟨4813133660210585748944545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102680184751159162644150293 4813133660210585748944545)
          ·
            refine ⟨3609850245157939311708409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813133660210585748944545 3609850245157939311708409)
            ·
              refine ⟨2707387683868454483781307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609850245157939311708409 2707387683868454483781307)
              ·
                refine ⟨4061081525802681725671961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707387683868454483781307 4061081525802681725671961)
                ·
                  refine ⟨3045811144352011294253971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4061081525802681725671961 3045811144352011294253971)
                  ·
                    refine ⟨4568716716528016941380957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3045811144352011294253971 4568716716528016941380957)
                    ·
                      refine ⟨1713268768698006353017859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4568716716528016941380957 1713268768698006353017859)
                      ·
                        rfl

theorem cell23_3336579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_3336579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336579 prefixEnd_3336579 := by exact prefixLift 3336579
  have htrace : WordTrace (prefixWord ++ tailWord_3336579) baseStart_3336579 baseEnd_3336579 := by
    simpa [prefixWord, tailWord_3336579, baseEnd_3336579] using wordTrace_append hprefix tailTrace_3336579
  have hstable : (prefixWord ++ tailWord_3336579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336579).length < 2 ^ (prefixWord ++ tailWord_3336579).sum := by decide
  have hdescent : baseEnd_3336579 < baseStart_3336579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336581 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_3336581 : Nat := 118140960795 + 3336581 * 2 ^ 59
def prefixEnd_3336581 : Nat := 4983230072969 + 3 ^ 40 * 3336581 * 2
def baseEnd_3336581 : Nat := 1713269795659315345192849

theorem tailTrace_3336581 : CollatzResearch.WordTrace tailWord_3336581 prefixEnd_3336581 1713269795659315345192849 := by
  unfold tailWord_3336581
  simp only [CollatzResearch.WordTrace]
  refine ⟨121695106725144354512417597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81130071150096236341611731 121695106725144354512417597)
  ·
    refine ⟨45635665021929132942156599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121695106725144354512417597 45635665021929132942156599)
    ·
      refine ⟨68453497532893699413234899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45635665021929132942156599 68453497532893699413234899)
      ·
        refine ⟨102680246299340549119852349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68453497532893699413234899 102680246299340549119852349)
        ·
          refine ⟨38505092362252705919944631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102680246299340549119852349 38505092362252705919944631)
          ·
            refine ⟨57757638543379058879916947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38505092362252705919944631 57757638543379058879916947)
            ·
              refine ⟨86636457815068588319875421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57757638543379058879916947 86636457815068588319875421)
              ·
                refine ⟨32488671680650720619953283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86636457815068588319875421 32488671680650720619953283)
                ·
                  refine ⟨48733007520976080929929925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32488671680650720619953283 48733007520976080929929925)
                  ·
                    refine ⟨9137438910183015174361861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48733007520976080929929925 9137438910183015174361861)
                    ·
                      refine ⟨1713269795659315345192849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9137438910183015174361861 1713269795659315345192849)
                      ·
                        rfl

theorem cell23_3336581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_3336581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336581 prefixEnd_3336581 := by exact prefixLift 3336581
  have htrace : WordTrace (prefixWord ++ tailWord_3336581) baseStart_3336581 baseEnd_3336581 := by
    simpa [prefixWord, tailWord_3336581, baseEnd_3336581] using wordTrace_append hprefix tailTrace_3336581
  have hstable : (prefixWord ++ tailWord_3336581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336581).length < 2 ^ (prefixWord ++ tailWord_3336581).sum := by decide
  have hdescent : baseEnd_3336581 < baseStart_3336581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336606 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3336606 : Nat := 118140960795 + 3336606 * 2 ^ 59
def prefixEnd_3336606 : Nat := 4983230072969 + 3 ^ 40 * 3336606 * 2
def baseEnd_3336606 : Nat := 1713282632675677747380235

theorem tailTrace_3336606 : CollatzResearch.WordTrace tailWord_3336606 prefixEnd_3336606 1713282632675677747380235 := by
  unfold tailWord_3336606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212002318756722972759709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81130679033369189188051781 15212002318756722972759709)
  ·
    refine ⟨5704500869533771114784891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15212002318756722972759709 5704500869533771114784891)
    ·
      refine ⟨8556751304300656672177337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704500869533771114784891 8556751304300656672177337)
      ·
        refine ⟨6417563478225492504133003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8556751304300656672177337 6417563478225492504133003)
        ·
          refine ⟨9626345217338238756199505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6417563478225492504133003 9626345217338238756199505)
          ·
            refine ⟨7219758913003679067149629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9626345217338238756199505 7219758913003679067149629)
            ·
              refine ⟨2707409592376379650181111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7219758913003679067149629 2707409592376379650181111)
              ·
                refine ⟨4061114388564569475271667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707409592376379650181111 4061114388564569475271667)
                ·
                  refine ⟨6091671582846854212907501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061114388564569475271667 6091671582846854212907501)
                  ·
                    refine ⟨2284376843567570329840313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6091671582846854212907501 2284376843567570329840313)
                    ·
                      refine ⟨1713282632675677747380235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284376843567570329840313 1713282632675677747380235)
                      ·
                        rfl

theorem cell23_3336606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3336606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336606 prefixEnd_3336606 := by exact prefixLift 3336606
  have htrace : WordTrace (prefixWord ++ tailWord_3336606) baseStart_3336606 baseEnd_3336606 := by
    simpa [prefixWord, tailWord_3336606, baseEnd_3336606] using wordTrace_append hprefix tailTrace_3336606
  have hstable : (prefixWord ++ tailWord_3336606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336606).length < 2 ^ (prefixWord ++ tailWord_3336606).sum := by decide
  have hdescent : baseEnd_3336606 < baseStart_3336606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336625 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 5]
def baseStart_3336625 : Nat := 118140960795 + 3336625 * 2 ^ 59
def prefixEnd_3336625 : Nat := 4983230072969 + 3 ^ 40 * 3336625 * 2
def baseEnd_3336625 : Nat := 190365820978679241449183

theorem tailTrace_3336625 : CollatzResearch.WordTrace tailWord_3336625 prefixEnd_3336625 190365820978679241449183 := by
  unfold tailWord_3336625
  simp only [CollatzResearch.WordTrace]
  refine ⟨121696711536984950027019329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81131141024656633351346219 121696711536984950027019329)
  ·
    refine ⟨91272533652738712520264497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121696711536984950027019329 91272533652738712520264497)
    ·
      refine ⟨68454400239554034390198373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91272533652738712520264497 68454400239554034390198373)
      ·
        refine ⟨12835200044916381448162195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68454400239554034390198373 12835200044916381448162195)
        ·
          refine ⟨19252800067374572172243293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12835200044916381448162195 19252800067374572172243293)
          ·
            refine ⟨7219800025265464564591235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19252800067374572172243293 7219800025265464564591235)
            ·
              refine ⟨10829700037898196846886853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219800025265464564591235 10829700037898196846886853)
              ·
                refine ⟨2030568757105911908791285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10829700037898196846886853 2030568757105911908791285)
                ·
                  refine ⟨190365820978679241449183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2030568757105911908791285 190365820978679241449183)
                  ·
                    rfl

theorem cell23_3336625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 5].length) (baseStart_3336625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336625 prefixEnd_3336625 := by exact prefixLift 3336625
  have htrace : WordTrace (prefixWord ++ tailWord_3336625) baseStart_3336625 baseEnd_3336625 := by
    simpa [prefixWord, tailWord_3336625, baseEnd_3336625] using wordTrace_append hprefix tailTrace_3336625
  have hstable : (prefixWord ++ tailWord_3336625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336625).length < 2 ^ (prefixWord ++ tailWord_3336625).sum := by decide
  have hdescent : baseEnd_3336625 < baseStart_3336625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336638 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_3336638 : Nat := 118140960795 + 3336638 * 2 ^ 59
def prefixEnd_3336638 : Nat := 4983230072969 + 3 ^ 40 * 3336638 * 2
def baseEnd_3336638 : Nat := 571099688018873874060029

theorem tailTrace_3336638 : CollatzResearch.WordTrace tailWord_3336638 prefixEnd_3336638 571099688018873874060029 := by
  unfold tailWord_3336638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212148210742231655905321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81131457123958568831495045 15212148210742231655905321)
  ·
    refine ⟨11409111158056673741928991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15212148210742231655905321 11409111158056673741928991)
    ·
      refine ⟨17113666737085010612893487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409111158056673741928991 17113666737085010612893487)
      ·
        refine ⟨25670500105627515919340231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17113666737085010612893487 25670500105627515919340231)
        ·
          refine ⟨38505750158441273879010347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25670500105627515919340231 38505750158441273879010347)
          ·
            refine ⟨57758625237661910818515521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38505750158441273879010347 57758625237661910818515521)
            ·
              refine ⟨43318968928246433113886641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57758625237661910818515521 43318968928246433113886641)
              ·
                refine ⟨32489226696184824835414981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43318968928246433113886641 32489226696184824835414981)
                ·
                  refine ⟨6091730005534654656640309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32489226696184824835414981 6091730005534654656640309)
                  ·
                    refine ⟨571099688018873874060029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6091730005534654656640309 571099688018873874060029)
                    ·
                      rfl

theorem cell23_3336638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_3336638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336638 prefixEnd_3336638 := by exact prefixLift 3336638
  have htrace : WordTrace (prefixWord ++ tailWord_3336638) baseStart_3336638 baseEnd_3336638 := by
    simpa [prefixWord, tailWord_3336638, baseEnd_3336638] using wordTrace_append hprefix tailTrace_3336638
  have hstable : (prefixWord ++ tailWord_3336638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336638).length < 2 ^ (prefixWord ++ tailWord_3336638).sum := by decide
  have hdescent : baseEnd_3336638 < baseStart_3336638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336736 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 1, 4]
def baseStart_3336736 : Nat := 118140960795 + 3336736 * 2 ^ 59
def prefixEnd_3336736 : Nat := 4983230072969 + 3 ^ 40 * 3336736 * 2
def baseEnd_3336736 : Nat := 571116461720254079584879

theorem tailTrace_3336736 : CollatzResearch.WordTrace tailWord_3336736 prefixEnd_3336736 571116461720254079584879 := by
  unfold tailWord_3336736
  simp only [CollatzResearch.WordTrace]
  refine ⟨60850380019791407992155031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81133840026388543989540041 60850380019791407992155031)
  ·
    refine ⟨91275570029687111988232547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60850380019791407992155031 91275570029687111988232547)
    ·
      refine ⟨136913355044530667982348821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91275570029687111988232547 136913355044530667982348821)
      ·
        refine ⟨6417813517712375061672601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136913355044530667982348821 6417813517712375061672601)
        ·
          refine ⟨4813360138284281296254451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6417813517712375061672601 4813360138284281296254451)
          ·
            refine ⟨7220040207426421944381677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813360138284281296254451 7220040207426421944381677)
            ·
              refine ⟨2707515077784908229143129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7220040207426421944381677 2707515077784908229143129)
              ·
                refine ⟨2030636308338681171857347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2707515077784908229143129 2030636308338681171857347)
                ·
                  refine ⟨3045954462508021757786021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030636308338681171857347 3045954462508021757786021)
                  ·
                    refine ⟨571116461720254079584879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045954462508021757786021 571116461720254079584879)
                    ·
                      rfl

theorem cell23_3336736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 4].length) (baseStart_3336736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336736 prefixEnd_3336736 := by exact prefixLift 3336736
  have htrace : WordTrace (prefixWord ++ tailWord_3336736) baseStart_3336736 baseEnd_3336736 := by
    simpa [prefixWord, tailWord_3336736, baseEnd_3336736] using wordTrace_append hprefix tailTrace_3336736
  have hstable : (prefixWord ++ tailWord_3336736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336736).length < 2 ^ (prefixWord ++ tailWord_3336736).sum := by decide
  have hdescent : baseEnd_3336736 < baseStart_3336736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336738 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3336738 : Nat := 118140960795 + 3336738 * 2 ^ 59
def prefixEnd_3336738 : Nat := 4983230072969 + 3 ^ 40 * 3336738 * 2
def baseEnd_3336738 : Nat := 1713350412122071230929627

theorem tailTrace_3336738 : CollatzResearch.WordTrace tailWord_3336738 prefixEnd_3336738 1713350412122071230929627 := by
  unfold tailWord_3336738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30425208246393892581470717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81133888657050380217255245 30425208246393892581470717)
  ·
    refine ⟨11409453092397709718051519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30425208246393892581470717 11409453092397709718051519)
    ·
      refine ⟨17114179638596564577077279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409453092397709718051519 17114179638596564577077279)
      ·
        refine ⟨25671269457894846865615919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17114179638596564577077279 25671269457894846865615919)
        ·
          refine ⟨38506904186842270298423879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25671269457894846865615919 38506904186842270298423879)
          ·
            refine ⟨57760356280263405447635819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38506904186842270298423879 57760356280263405447635819)
            ·
              refine ⟨86640534420395108171453729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57760356280263405447635819 86640534420395108171453729)
              ·
                refine ⟨64980400815296331128590297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86640534420395108171453729 64980400815296331128590297)
                ·
                  refine ⟨48735300611472248346442723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64980400815296331128590297 48735300611472248346442723)
                  ·
                    refine ⟨73102950917208372519664085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48735300611472248346442723 73102950917208372519664085)
                    ·
                      refine ⟨1713350412122071230929627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73102950917208372519664085 1713350412122071230929627)
                      ·
                        rfl

theorem cell23_3336738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3336738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336738 prefixEnd_3336738 := by exact prefixLift 3336738
  have htrace : WordTrace (prefixWord ++ tailWord_3336738) baseStart_3336738 baseEnd_3336738 := by
    simpa [prefixWord, tailWord_3336738, baseEnd_3336738] using wordTrace_append hprefix tailTrace_3336738
  have hstable : (prefixWord ++ tailWord_3336738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336738).length < 2 ^ (prefixWord ++ tailWord_3336738).sum := by decide
  have hdescent : baseEnd_3336738 < baseStart_3336738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336762 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_3336762 : Nat := 118140960795 + 3336762 * 2 ^ 59
def prefixEnd_3336762 : Nat := 4983230072969 + 3 ^ 40 * 3336762 * 2
def baseEnd_3336762 : Nat := 571120911885926379009839

theorem tailTrace_3336762 : CollatzResearch.WordTrace tailWord_3336762 prefixEnd_3336762 571120911885926379009839 := by
  unfold tailWord_3336762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30425427084372155606189135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81134472224992414949837693 30425427084372155606189135)
  ·
    refine ⟨45638140626558233409283703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30425427084372155606189135 45638140626558233409283703)
    ·
      refine ⟨68457210939837350113925555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45638140626558233409283703 68457210939837350113925555)
      ·
        refine ⟨102685816409756025170888333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68457210939837350113925555 102685816409756025170888333)
        ·
          refine ⟨38507181153658509439083125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102685816409756025170888333 38507181153658509439083125)
          ·
            refine ⟨3610048233155485259914043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38507181153658509439083125 3610048233155485259914043)
            ·
              refine ⟨5415072349733227889871065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610048233155485259914043 5415072349733227889871065)
              ·
                refine ⟨4061304262299920917403299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415072349733227889871065 4061304262299920917403299)
                ·
                  refine ⟨6091956393449881376104949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061304262299920917403299 6091956393449881376104949)
                  ·
                    refine ⟨571120911885926379009839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6091956393449881376104949 571120911885926379009839)
                    ·
                      rfl

theorem cell23_3336762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_3336762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336762 prefixEnd_3336762 := by exact prefixLift 3336762
  have htrace : WordTrace (prefixWord ++ tailWord_3336762) baseStart_3336762 baseEnd_3336762 := by
    simpa [prefixWord, tailWord_3336762, baseEnd_3336762] using wordTrace_append hprefix tailTrace_3336762
  have hstable : (prefixWord ++ tailWord_3336762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336762).length < 2 ^ (prefixWord ++ tailWord_3336762).sum := by decide
  have hdescent : baseEnd_3336762 < baseStart_3336762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336768 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_3336768 : Nat := 118140960795 + 3336768 * 2 ^ 59
def prefixEnd_3336768 : Nat := 4983230072969 + 3 ^ 40 * 3336768 * 2
def baseEnd_3336768 : Nat := 1713365816541706113554489

theorem tailTrace_3336768 : CollatzResearch.WordTrace tailWord_3336768 prefixEnd_3336768 1713365816541706113554489 := by
  unfold tailWord_3336768
  simp only [CollatzResearch.WordTrace]
  refine ⟨60850963587733442724737479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81134618116977923632983305 60850963587733442724737479)
  ·
    refine ⟨91276445381600164087106219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60850963587733442724737479 91276445381600164087106219)
    ·
      refine ⟨136914668072400246130659329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91276445381600164087106219 136914668072400246130659329)
      ·
        refine ⟨102686001054300184597994497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136914668072400246130659329 102686001054300184597994497)
        ·
          refine ⟨77014500790725138448495873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102686001054300184597994497 77014500790725138448495873)
          ·
            refine ⟨57760875593043853836371905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77014500790725138448495873 57760875593043853836371905)
            ·
              refine ⟨43320656694782890377278929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57760875593043853836371905 43320656694782890377278929)
              ·
                refine ⟨32490492521087167782959197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43320656694782890377278929 32490492521087167782959197)
                ·
                  refine ⟨12183934695407687918609699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32490492521087167782959197 12183934695407687918609699)
                  ·
                    refine ⟨18275902043111531877914549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12183934695407687918609699 18275902043111531877914549)
                    ·
                      refine ⟨1713365816541706113554489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18275902043111531877914549 1713365816541706113554489)
                      ·
                        rfl

theorem cell23_3336768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_3336768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336768 prefixEnd_3336768 := by exact prefixLift 3336768
  have htrace : WordTrace (prefixWord ++ tailWord_3336768) baseStart_3336768 baseEnd_3336768 := by
    simpa [prefixWord, tailWord_3336768, baseEnd_3336768] using wordTrace_append hprefix tailTrace_3336768
  have hstable : (prefixWord ++ tailWord_3336768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336768).length < 2 ^ (prefixWord ++ tailWord_3336768).sum := by decide
  have hdescent : baseEnd_3336768 < baseStart_3336768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336769 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3336769 : Nat := 118140960795 + 3336769 * 2 ^ 59
def prefixEnd_3336769 : Nat := 4983230072969 + 3 ^ 40 * 3336769 * 2
def baseEnd_3336769 : Nat := 1713366330022360609641985

theorem tailTrace_3336769 : CollatzResearch.WordTrace tailWord_3336769 prefixEnd_3336769 1713366330022360609641985 := by
  unfold tailWord_3336769
  simp only [CollatzResearch.WordTrace]
  refine ⟨121701963648463262620261361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81134642432308841746840907 121701963648463262620261361)
  ·
    refine ⟨91276472736347446965196021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121701963648463262620261361 91276472736347446965196021)
    ·
      refine ⟨8557169319032573152987127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91276472736347446965196021 8557169319032573152987127)
      ·
        refine ⟨12835753978548859729480691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557169319032573152987127 12835753978548859729480691)
        ·
          refine ⟨19253630967823289594221037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12835753978548859729480691 19253630967823289594221037)
          ·
            refine ⟨7220111612933733597832889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19253630967823289594221037 7220111612933733597832889)
            ·
              refine ⟨5415083709700300198374667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220111612933733597832889 5415083709700300198374667)
              ·
                refine ⟨8122625564550450297562001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415083709700300198374667 8122625564550450297562001)
                ·
                  refine ⟨6091969173412837723171501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8122625564550450297562001 6091969173412837723171501)
                  ·
                    refine ⟨2284488440029814146189313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6091969173412837723171501 2284488440029814146189313)
                    ·
                      refine ⟨1713366330022360609641985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284488440029814146189313 1713366330022360609641985)
                      ·
                        rfl

theorem cell23_3336769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3336769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336769 prefixEnd_3336769 := by exact prefixLift 3336769
  have htrace : WordTrace (prefixWord ++ tailWord_3336769) baseStart_3336769 baseEnd_3336769 := by
    simpa [prefixWord, tailWord_3336769, baseEnd_3336769] using wordTrace_append hprefix tailTrace_3336769
  have hstable : (prefixWord ++ tailWord_3336769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336769).length < 2 ^ (prefixWord ++ tailWord_3336769).sum := by decide
  have hdescent : baseEnd_3336769 < baseStart_3336769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336775 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3336775 : Nat := 118140960795 + 3336775 * 2 ^ 59
def prefixEnd_3336775 : Nat := 4983230072969 + 3 ^ 40 * 3336775 * 2
def baseEnd_3336775 : Nat := 571123136968762528722319

theorem tailTrace_3336775 : CollatzResearch.WordTrace tailWord_3336775 prefixEnd_3336775 571123136968762528722319 := by
  unfold tailWord_3336775
  simp only [CollatzResearch.WordTrace]
  refine ⟨121702182486441525644979779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81134788324294350429986519 121702182486441525644979779)
  ·
    refine ⟨182553273729662288467469669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121702182486441525644979779 182553273729662288467469669)
    ·
      refine ⟨34228738824311679087650563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182553273729662288467469669 34228738824311679087650563)
      ·
        refine ⟨51343108236467518631475845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34228738824311679087650563 51343108236467518631475845)
        ·
          refine ⟨9626832794337659743401721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51343108236467518631475845 9626832794337659743401721)
          ·
            refine ⟨7220124595753244807551291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9626832794337659743401721 7220124595753244807551291)
            ·
              refine ⟨10830186893629867211326937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220124595753244807551291 10830186893629867211326937)
              ·
                refine ⟨8122640170222400408495203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10830186893629867211326937 8122640170222400408495203)
                ·
                  refine ⟨12183960255333600612742805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122640170222400408495203 12183960255333600612742805)
                  ·
                    refine ⟨571123136968762528722319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12183960255333600612742805 571123136968762528722319)
                    ·
                      rfl

theorem cell23_3336775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3336775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336775 prefixEnd_3336775 := by exact prefixLift 3336775
  have htrace : WordTrace (prefixWord ++ tailWord_3336775) baseStart_3336775 baseEnd_3336775 := by
    simpa [prefixWord, tailWord_3336775, baseEnd_3336775] using wordTrace_append hprefix tailTrace_3336775
  have hstable : (prefixWord ++ tailWord_3336775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336775).length < 2 ^ (prefixWord ++ tailWord_3336775).sum := by decide
  have hdescent : baseEnd_3336775 < baseStart_3336775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336785 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_3336785 : Nat := 118140960795 + 3336785 * 2 ^ 59
def prefixEnd_3336785 : Nat := 4983230072969 + 3 ^ 40 * 3336785 * 2
def baseEnd_3336785 : Nat := 1713374545712832547041911

theorem tailTrace_3336785 : CollatzResearch.WordTrace tailWord_3336785 prefixEnd_3336785 1713374545712832547041911 := by
  unfold tailWord_3336785
  simp only [CollatzResearch.WordTrace]
  refine ⟨121702547216405297352843809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81135031477603531568562539 121702547216405297352843809)
  ·
    refine ⟨91276910412303973014632857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121702547216405297352843809 91276910412303973014632857)
    ·
      refine ⟨68457682809227979760974643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91276910412303973014632857 68457682809227979760974643)
      ·
        refine ⟨102686524213841969641461965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68457682809227979760974643 102686524213841969641461965)
        ·
          refine ⟨38507446580190738615548237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102686524213841969641461965 38507446580190738615548237)
          ·
            refine ⟨14440292467571526980830589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38507446580190738615548237 14440292467571526980830589)
            ·
              refine ⟨5415109675339322617811471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14440292467571526980830589 5415109675339322617811471)
              ·
                refine ⟨8122664513008983926717207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415109675339322617811471 8122664513008983926717207)
                ·
                  refine ⟨12183996769513475890075811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122664513008983926717207 12183996769513475890075811)
                  ·
                    refine ⟨18275995154270213835113717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12183996769513475890075811 18275995154270213835113717)
                    ·
                      refine ⟨1713374545712832547041911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18275995154270213835113717 1713374545712832547041911)
                      ·
                        rfl

theorem cell23_3336785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_3336785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336785 prefixEnd_3336785 := by exact prefixLift 3336785
  have htrace : WordTrace (prefixWord ++ tailWord_3336785) baseStart_3336785 baseEnd_3336785 := by
    simpa [prefixWord, tailWord_3336785, baseEnd_3336785] using wordTrace_append hprefix tailTrace_3336785
  have hstable : (prefixWord ++ tailWord_3336785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336785).length < 2 ^ (prefixWord ++ tailWord_3336785).sum := by decide
  have hdescent : baseEnd_3336785 < baseStart_3336785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336788 : List Nat := [2, 4, 1, 1, 1, 14]
def baseStart_3336788 : Nat := 118140960795 + 3336788 * 2 ^ 59
def prefixEnd_3336788 : Nat := 4983230072969 + 3 ^ 40 * 3336788 * 2
def baseEnd_3336788 : Nat := 7050930395698749116479

theorem tailTrace_3336788 : CollatzResearch.WordTrace tailWord_3336788 prefixEnd_3336788 7050930395698749116479 := by
  unfold tailWord_3336788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60851328317697214432601509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81135104423596285910135345 60851328317697214432601509)
  ·
    refine ⟨11409624059568227706112783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60851328317697214432601509 11409624059568227706112783)
    ·
      refine ⟨17114436089352341559169175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409624059568227706112783 17114436089352341559169175)
      ·
        refine ⟨25671654134028512338753763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17114436089352341559169175 25671654134028512338753763)
        ·
          refine ⟨38507481201042768508130645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25671654134028512338753763 38507481201042768508130645)
          ·
            refine ⟨7050930395698749116479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 38507481201042768508130645 7050930395698749116479)
            ·
              rfl

theorem cell23_3336788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 14].length) (baseStart_3336788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336788 prefixEnd_3336788 := by exact prefixLift 3336788
  have htrace : WordTrace (prefixWord ++ tailWord_3336788) baseStart_3336788 baseEnd_3336788 := by
    simpa [prefixWord, tailWord_3336788, baseEnd_3336788] using wordTrace_append hprefix tailTrace_3336788
  have hstable : (prefixWord ++ tailWord_3336788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336788).length < 2 ^ (prefixWord ++ tailWord_3336788).sum := by decide
  have hdescent : baseEnd_3336788 < baseStart_3336788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336815 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_3336815 : Nat := 118140960795 + 3336815 * 2 ^ 59
def prefixEnd_3336815 : Nat := 4983230072969 + 3 ^ 40 * 3336815 * 2
def baseEnd_3336815 : Nat := 1713389950132467429666773

theorem tailTrace_3336815 : CollatzResearch.WordTrace tailWord_3336815 prefixEnd_3336815 1713389950132467429666773 := by
  unfold tailWord_3336815
  simp only [CollatzResearch.WordTrace]
  refine ⟨121703641406296612476435899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81135760937531074984290599 121703641406296612476435899)
  ·
    refine ⟨182555462109444918714653849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121703641406296612476435899 182555462109444918714653849)
    ·
      refine ⟨136916596582083689035990387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182555462109444918714653849 136916596582083689035990387)
      ·
        refine ⟨205374894873125533553985581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136916596582083689035990387 205374894873125533553985581)
        ·
          refine ⟨77015585577422075082744593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205374894873125533553985581 77015585577422075082744593)
          ·
            refine ⟨57761689183066556312058445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77015585577422075082744593 57761689183066556312058445)
            ·
              refine ⟨21660633443649958617021917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57761689183066556312058445 21660633443649958617021917)
              ·
                refine ⟨8122737541368734481383219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21660633443649958617021917 8122737541368734481383219)
                ·
                  refine ⟨12184106312053101722074829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122737541368734481383219 12184106312053101722074829)
                  ·
                    refine ⟨4569039867019913145778061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12184106312053101722074829 4569039867019913145778061)
                    ·
                      refine ⟨1713389950132467429666773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569039867019913145778061 1713389950132467429666773)
                      ·
                        rfl

theorem cell23_3336815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_3336815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336815 prefixEnd_3336815 := by exact prefixLift 3336815
  have htrace : WordTrace (prefixWord ++ tailWord_3336815) baseStart_3336815 baseEnd_3336815 := by
    simpa [prefixWord, tailWord_3336815, baseEnd_3336815] using wordTrace_append hprefix tailTrace_3336815
  have hstable : (prefixWord ++ tailWord_3336815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336815).length < 2 ^ (prefixWord ++ tailWord_3336815).sum := by decide
  have hdescent : baseEnd_3336815 < baseStart_3336815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336836 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_3336836 : Nat := 118140960795 + 3336836 * 2 ^ 59
def prefixEnd_3336836 : Nat := 4983230072969 + 3 ^ 40 * 3336836 * 2
def baseEnd_3336836 : Nat := 1713400733226211847504177

theorem tailTrace_3336836 : CollatzResearch.WordTrace tailWord_3336836 prefixEnd_3336836 1713400733226211847504177 := by
  unfold tailWord_3336836
  simp only [CollatzResearch.WordTrace]
  refine ⟨60852203669610266531475181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81136271559480355375300241 60852203669610266531475181)
  ·
    refine ⟨22819576376103849949303193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60852203669610266531475181 22819576376103849949303193)
    ·
      refine ⟨17114682282077887461977395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22819576376103849949303193 17114682282077887461977395)
      ·
        refine ⟨25672023423116831192966093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17114682282077887461977395 25672023423116831192966093)
        ·
          refine ⟨9627008783668811697362285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25672023423116831192966093 9627008783668811697362285)
          ·
            refine ⟨3610128293875804386510857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9627008783668811697362285 3610128293875804386510857)
            ·
              refine ⟨2707596220406853289883143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3610128293875804386510857 2707596220406853289883143)
              ·
                refine ⟨4061394330610279934824715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707596220406853289883143 4061394330610279934824715)
                ·
                  refine ⟨6092091495915419902237073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061394330610279934824715 6092091495915419902237073)
                  ·
                    refine ⟨4569068621936564926677805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092091495915419902237073 4569068621936564926677805)
                    ·
                      refine ⟨1713400733226211847504177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569068621936564926677805 1713400733226211847504177)
                      ·
                        rfl

theorem cell23_3336836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_3336836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336836 prefixEnd_3336836 := by exact prefixLift 3336836
  have htrace : WordTrace (prefixWord ++ tailWord_3336836) baseStart_3336836 baseEnd_3336836 := by
    simpa [prefixWord, tailWord_3336836, baseEnd_3336836] using wordTrace_append hprefix tailTrace_3336836
  have hstable : (prefixWord ++ tailWord_3336836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336836).length < 2 ^ (prefixWord ++ tailWord_3336836).sum := by decide
  have hdescent : baseEnd_3336836 < baseStart_3336836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336942 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3336942 : Nat := 118140960795 + 3336942 * 2 ^ 59
def prefixEnd_3336942 : Nat := 4983230072969 + 3 ^ 40 * 3336942 * 2
def baseEnd_3336942 : Nat := 571151720725196144259563

theorem tailTrace_3336942 : CollatzResearch.WordTrace tailWord_3336942 prefixEnd_3336942 571151720725196144259563 := by
  unfold tailWord_3336942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213534184604564145788635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81138848984557675444206053 15213534184604564145788635)
  ·
    refine ⟨22820301276906846218682953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15213534184604564145788635 22820301276906846218682953)
    ·
      refine ⟨17115225957680134664012215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22820301276906846218682953 17115225957680134664012215)
      ·
        refine ⟨25672838936520201996018323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17115225957680134664012215 25672838936520201996018323)
        ·
          refine ⟨38509258404780302994027485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25672838936520201996018323 38509258404780302994027485)
          ·
            refine ⟨14440971901792613622760307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38509258404780302994027485 14440971901792613622760307)
            ·
              refine ⟨21661457852688920434140461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14440971901792613622760307 21661457852688920434140461)
              ·
                refine ⟨8123046694758345162802673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21661457852688920434140461 8123046694758345162802673)
                ·
                  refine ⟨6092285021068758872102005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123046694758345162802673 6092285021068758872102005)
                  ·
                    refine ⟨571151720725196144259563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6092285021068758872102005 571151720725196144259563)
                    ·
                      rfl

theorem cell23_3336942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3336942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336942 prefixEnd_3336942 := by exact prefixLift 3336942
  have htrace : WordTrace (prefixWord ++ tailWord_3336942) baseStart_3336942 baseEnd_3336942 := by
    simpa [prefixWord, tailWord_3336942, baseEnd_3336942] using wordTrace_append hprefix tailTrace_3336942
  have hstable : (prefixWord ++ tailWord_3336942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336942).length < 2 ^ (prefixWord ++ tailWord_3336942).sum := by decide
  have hdescent : baseEnd_3336942 < baseStart_3336942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336972 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_3336972 : Nat := 118140960795 + 3336972 * 2 ^ 59
def prefixEnd_3336972 : Nat := 4983230072969 + 3 ^ 40 * 3336972 * 2
def baseEnd_3336972 : Nat := 571156855531741105134517

theorem tailTrace_3336972 : CollatzResearch.WordTrace tailWord_3336972 prefixEnd_3336972 571156855531741105134517 := by
  unfold tailWord_3336972
  simp only [CollatzResearch.WordTrace]
  refine ⟨60854683833363914144950585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81139578444485218859934113 60854683833363914144950585)
  ·
    refine ⟨45641012875022935608712939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60854683833363914144950585 45641012875022935608712939)
    ·
      refine ⟨68461519312534403413069409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45641012875022935608712939 68461519312534403413069409)
      ·
        refine ⟨51346139484400802559802057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68461519312534403413069409 51346139484400802559802057)
        ·
          refine ⟨38509604613300601919851543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51346139484400802559802057 38509604613300601919851543)
          ·
            refine ⟨57764406919950902879777315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38509604613300601919851543 57764406919950902879777315)
            ·
              refine ⟨86646610379926354319665973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57764406919950902879777315 86646610379926354319665973)
              ·
                refine ⟨8123119723118095717468685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86646610379926354319665973 8123119723118095717468685)
                ·
                  refine ⟨3046169896169285894050757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8123119723118095717468685 3046169896169285894050757)
                  ·
                    refine ⟨571156855531741105134517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3046169896169285894050757 571156855531741105134517)
                    ·
                      rfl

theorem cell23_3336972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_3336972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336972 prefixEnd_3336972 := by exact prefixLift 3336972
  have htrace : WordTrace (prefixWord ++ tailWord_3336972) baseStart_3336972 baseEnd_3336972 := by
    simpa [prefixWord, tailWord_3336972, baseEnd_3336972] using wordTrace_append hprefix tailTrace_3336972
  have hstable : (prefixWord ++ tailWord_3336972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336972).length < 2 ^ (prefixWord ++ tailWord_3336972).sum := by decide
  have hdescent : baseEnd_3336972 < baseStart_3336972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3336996 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_3336996 : Nat := 118140960795 + 3336996 * 2 ^ 59
def prefixEnd_3336996 : Nat := 4983230072969 + 3 ^ 40 * 3336996 * 2
def baseEnd_3336996 : Nat := 1713482890130931221503441

theorem tailTrace_3336996 : CollatzResearch.WordTrace tailWord_3336996 prefixEnd_3336996 1713482890130931221503441 := by
  unfold tailWord_3336996
  simp only [CollatzResearch.WordTrace]
  refine ⟨60855121509320440194387421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81140162012427253592516561 60855121509320440194387421)
  ·
    refine ⟨22820670565995165072895283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60855121509320440194387421 22820670565995165072895283)
    ·
      refine ⟨34231005848992747609342925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22820670565995165072895283 34231005848992747609342925)
      ·
        refine ⟨12836627193372280353503597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34231005848992747609342925 12836627193372280353503597)
        ·
          refine ⟨4813735197514605132563849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12836627193372280353503597 4813735197514605132563849)
          ·
            refine ⟨3610301398135953849422887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813735197514605132563849 3610301398135953849422887)
            ·
              refine ⟨5415452097203930774134331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610301398135953849422887 5415452097203930774134331)
              ·
                refine ⟨8123178145805896161201497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415452097203930774134331 8123178145805896161201497)
                ·
                  refine ⟨6092383609354422120901123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123178145805896161201497 6092383609354422120901123)
                  ·
                    refine ⟨9138575414031633181351685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6092383609354422120901123 9138575414031633181351685)
                    ·
                      refine ⟨1713482890130931221503441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9138575414031633181351685 1713482890130931221503441)
                      ·
                        rfl

theorem cell23_3336996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_3336996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3336996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3336996 prefixEnd_3336996 := by exact prefixLift 3336996
  have htrace : WordTrace (prefixWord ++ tailWord_3336996) baseStart_3336996 baseEnd_3336996 := by
    simpa [prefixWord, tailWord_3336996, baseEnd_3336996] using wordTrace_append hprefix tailTrace_3336996
  have hstable : (prefixWord ++ tailWord_3336996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3336996).length < 2 ^ (prefixWord ++ tailWord_3336996).sum := by decide
  have hdescent : baseEnd_3336996 < baseStart_3336996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3336996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337049 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_3337049 : Nat := 118140960795 + 3337049 * 2 ^ 59
def prefixEnd_3337049 : Nat := 4983230072969 + 3 ^ 40 * 3337049 * 2
def baseEnd_3337049 : Nat := 571170034868539838046899

theorem tailTrace_3337049 : CollatzResearch.WordTrace tailWord_3337049 prefixEnd_3337049 571170034868539838046899 := by
  unfold tailWord_3337049
  simp only [CollatzResearch.WordTrace]
  refine ⟨121712176087448870440454201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81141450724965913626969467 121712176087448870440454201)
  ·
    refine ⟨91284132065586652830340651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121712176087448870440454201 91284132065586652830340651)
    ·
      refine ⟨136926198098379979245510977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91284132065586652830340651 136926198098379979245510977)
      ·
        refine ⟨102694648573784984434133233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136926198098379979245510977 102694648573784984434133233)
        ·
          refine ⟨77020986430338738325599925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102694648573784984434133233 77020986430338738325599925)
          ·
            refine ⟨7220717477844256718024993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77020986430338738325599925 7220717477844256718024993)
            ·
              refine ⟨5415538108383192538518745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220717477844256718024993 5415538108383192538518745)
              ·
                refine ⟨4061653581287394403889059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415538108383192538518745 4061653581287394403889059)
                ·
                  refine ⟨6092480371931091605833589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061653581287394403889059 6092480371931091605833589)
                  ·
                    refine ⟨571170034868539838046899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6092480371931091605833589 571170034868539838046899)
                    ·
                      rfl

theorem cell23_3337049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_3337049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337049 prefixEnd_3337049 := by exact prefixLift 3337049
  have htrace : WordTrace (prefixWord ++ tailWord_3337049) baseStart_3337049 baseEnd_3337049 := by
    simpa [prefixWord, tailWord_3337049, baseEnd_3337049] using wordTrace_append hprefix tailTrace_3337049
  have hstable : (prefixWord ++ tailWord_3337049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337049).length < 2 ^ (prefixWord ++ tailWord_3337049).sum := by decide
  have hdescent : baseEnd_3337049 < baseStart_3337049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337063 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_3337063 : Nat := 118140960795 + 3337063 * 2 ^ 59
def prefixEnd_3337063 : Nat := 4983230072969 + 3 ^ 40 * 3337063 * 2
def baseEnd_3337063 : Nat := 1713517293334782459365633

theorem tailTrace_3337063 : CollatzResearch.WordTrace tailWord_3337063 prefixEnd_3337063 1713517293334782459365633 := by
  unfold tailWord_3337063
  simp only [CollatzResearch.WordTrace]
  refine ⟨121712686709398150831463843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81141791139598767220975895 121712686709398150831463843)
  ·
    refine ⟨182569030064097226247195765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121712686709398150831463843 182569030064097226247195765)
    ·
      refine ⟨17115846568509114960674603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182569030064097226247195765 17115846568509114960674603)
      ·
        refine ⟨25673769852763672441011905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17115846568509114960674603 25673769852763672441011905)
        ·
          refine ⟨19255327389572754330758929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25673769852763672441011905 19255327389572754330758929)
          ·
            refine ⟨14441495542179565748069197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19255327389572754330758929 14441495542179565748069197)
            ·
              refine ⟨5415560828317337155525949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14441495542179565748069197 5415560828317337155525949)
              ·
                refine ⟨2030835310619001433322231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5415560828317337155525949 2030835310619001433322231)
                ·
                  refine ⟨3046252965928502149983347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030835310619001433322231 3046252965928502149983347)
                  ·
                    refine ⟨4569379448892753224975021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3046252965928502149983347 4569379448892753224975021)
                    ·
                      refine ⟨1713517293334782459365633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569379448892753224975021 1713517293334782459365633)
                      ·
                        rfl

theorem cell23_3337063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_3337063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337063 prefixEnd_3337063 := by exact prefixLift 3337063
  have htrace : WordTrace (prefixWord ++ tailWord_3337063) baseStart_3337063 baseEnd_3337063 := by
    simpa [prefixWord, tailWord_3337063, baseEnd_3337063] using wordTrace_append hprefix tailTrace_3337063
  have hstable : (prefixWord ++ tailWord_3337063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337063).length < 2 ^ (prefixWord ++ tailWord_3337063).sum := by decide
  have hdescent : baseEnd_3337063 < baseStart_3337063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337072 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_3337072 : Nat := 118140960795 + 3337072 * 2 ^ 59
def prefixEnd_3337072 : Nat := 4983230072969 + 3 ^ 40 * 3337072 * 2
def baseEnd_3337072 : Nat := 1713521914660672924153091

theorem tailTrace_3337072 : CollatzResearch.WordTrace tailWord_3337072 prefixEnd_3337072 1713521914660672924153091 := by
  unfold tailWord_3337072
  simp only [CollatzResearch.WordTrace]
  refine ⟨60856507483182772684270735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81142009977577030245694313 60856507483182772684270735)
  ·
    refine ⟨91284761224774159026406103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60856507483182772684270735 91284761224774159026406103)
    ·
      refine ⟨136927141837161238539609155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91284761224774159026406103 136927141837161238539609155)
      ·
        refine ⟨205390712755741857809413733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136927141837161238539609155 205390712755741857809413733)
        ·
          refine ⟨38510758641701598339265075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205390712755741857809413733 38510758641701598339265075)
          ·
            refine ⟨57766137962552397508897613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38510758641701598339265075 57766137962552397508897613)
            ·
              refine ⟨21662301735957149065836605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57766137962552397508897613 21662301735957149065836605)
              ·
                refine ⟨8123363150983930899688727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21662301735957149065836605 8123363150983930899688727)
                ·
                  refine ⟨12185044726475896349533091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123363150983930899688727 12185044726475896349533091)
                  ·
                    refine ⟨18277567089713844524299637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12185044726475896349533091 18277567089713844524299637)
                    ·
                      refine ⟨1713521914660672924153091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18277567089713844524299637 1713521914660672924153091)
                      ·
                        rfl

theorem cell23_3337072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_3337072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337072 prefixEnd_3337072 := by exact prefixLift 3337072
  have htrace : WordTrace (prefixWord ++ tailWord_3337072) baseStart_3337072 baseEnd_3337072 := by
    simpa [prefixWord, tailWord_3337072, baseEnd_3337072] using wordTrace_append hprefix tailTrace_3337072
  have hstable : (prefixWord ++ tailWord_3337072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337072).length < 2 ^ (prefixWord ++ tailWord_3337072).sum := by decide
  have hdescent : baseEnd_3337072 < baseStart_3337072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337075 : List Nat := [1, 1, 1, 2, 2, 1, 15]
def baseStart_3337075 : Nat := 118140960795 + 3337075 * 2 ^ 59
def prefixEnd_3337075 : Nat := 4983230072969 + 3 ^ 40 * 3337075 * 2
def baseEnd_3337075 : Nat := 21154610556822671758217

theorem tailTrace_3337075 : CollatzResearch.WordTrace tailWord_3337075 prefixEnd_3337075 21154610556822671758217 := by
  unfold tailWord_3337075
  simp only [CollatzResearch.WordTrace]
  refine ⟨121713124385354676880900679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81142082923569784587267119 121713124385354676880900679)
  ·
    refine ⟨182569686578032015321351019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121713124385354676880900679 182569686578032015321351019)
    ·
      refine ⟨273854529867048022982026529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182569686578032015321351019 273854529867048022982026529)
      ·
        refine ⟨205390897400286017236519897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273854529867048022982026529 205390897400286017236519897)
        ·
          refine ⟨154043173050214512927389923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205390897400286017236519897 154043173050214512927389923)
          ·
            refine ⟨231064759575321769391084885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154043173050214512927389923 231064759575321769391084885)
            ·
              refine ⟨21154610556822671758217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 231064759575321769391084885 21154610556822671758217)
              ·
                rfl

theorem cell23_3337075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 15].length) (baseStart_3337075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337075 prefixEnd_3337075 := by exact prefixLift 3337075
  have htrace : WordTrace (prefixWord ++ tailWord_3337075) baseStart_3337075 baseEnd_3337075 := by
    simpa [prefixWord, tailWord_3337075, baseEnd_3337075] using wordTrace_append hprefix tailTrace_3337075
  have hstable : (prefixWord ++ tailWord_3337075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337075).length < 2 ^ (prefixWord ++ tailWord_3337075).sum := by decide
  have hdescent : baseEnd_3337075 < baseStart_3337075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337096 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 2, 4]
def baseStart_3337096 : Nat := 118140960795 + 3337096 * 2 ^ 59
def prefixEnd_3337096 : Nat := 4983230072969 + 3 ^ 40 * 3337096 * 2
def baseEnd_3337096 : Nat := 571178079398793610084327

theorem tailTrace_3337096 : CollatzResearch.WordTrace tailWord_3337096 prefixEnd_3337096 571178079398793610084327 := by
  unfold tailWord_3337096
  simp only [CollatzResearch.WordTrace]
  refine ⟨60856945159139298733707571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81142593545519064978276761 60856945159139298733707571)
  ·
    refine ⟨91285417738708948100561357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60856945159139298733707571 91285417738708948100561357)
    ·
      refine ⟨34232031652015855537710509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91285417738708948100561357 34232031652015855537710509)
      ·
        refine ⟨12837011869505945826641441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34232031652015855537710509 12837011869505945826641441)
        ·
          refine ⟨9627758902129459369981081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12837011869505945826641441 9627758902129459369981081)
          ·
            refine ⟨7220819176597094527485811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9627758902129459369981081 7220819176597094527485811)
            ·
              refine ⟨10831228764895641791228717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220819176597094527485811 10831228764895641791228717)
              ·
                refine ⟨4061710786835865671710769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10831228764895641791228717 4061710786835865671710769)
                ·
                  refine ⟨3046283090126899253783077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4061710786835865671710769 3046283090126899253783077)
                  ·
                    refine ⟨571178079398793610084327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3046283090126899253783077 571178079398793610084327)
                    ·
                      rfl

theorem cell23_3337096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_3337096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337096 prefixEnd_3337096 := by exact prefixLift 3337096
  have htrace : WordTrace (prefixWord ++ tailWord_3337096) baseStart_3337096 baseEnd_3337096 := by
    simpa [prefixWord, tailWord_3337096, baseEnd_3337096] using wordTrace_append hprefix tailTrace_3337096
  have hstable : (prefixWord ++ tailWord_3337096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337096).length < 2 ^ (prefixWord ++ tailWord_3337096).sum := by decide
  have hdescent : baseEnd_3337096 < baseStart_3337096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337116 : List Nat := [2, 2, 3, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3337116 : Nat := 118140960795 + 3337116 * 2 ^ 59
def prefixEnd_3337116 : Nat := 4983230072969 + 3 ^ 40 * 3337116 * 2
def baseEnd_3337116 : Nat := 1713544507809470752002889

theorem tailTrace_3337116 : CollatzResearch.WordTrace tailWord_3337116 prefixEnd_3337116 1713544507809470752002889 := by
  unfold tailWord_3337116
  simp only [CollatzResearch.WordTrace]
  refine ⟨60857309889103070441571601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81143079852137427255428801 60857309889103070441571601)
  ·
    refine ⟨45642982416827302831178701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60857309889103070441571601 45642982416827302831178701)
    ·
      refine ⟨17116118406310238561692013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45642982416827302831178701 17116118406310238561692013)
      ·
        refine ⟨6418544402366339460634505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17116118406310238561692013 6418544402366339460634505)
        ·
          refine ⟨4813908301774754595475879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418544402366339460634505 4813908301774754595475879)
          ·
            refine ⟨7220862452662131893213819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813908301774754595475879 7220862452662131893213819)
            ·
              refine ⟨10831293678993197839820729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220862452662131893213819 10831293678993197839820729)
              ·
                refine ⟨8123470259244898379865547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10831293678993197839820729 8123470259244898379865547)
                ·
                  refine ⟨12185205388867347569798321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123470259244898379865547 12185205388867347569798321)
                  ·
                    refine ⟨9138904041650510677348741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12185205388867347569798321 9138904041650510677348741)
                    ·
                      refine ⟨1713544507809470752002889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9138904041650510677348741 1713544507809470752002889)
                      ·
                        rfl

theorem cell23_3337116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3337116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337116 prefixEnd_3337116 := by exact prefixLift 3337116
  have htrace : WordTrace (prefixWord ++ tailWord_3337116) baseStart_3337116 baseEnd_3337116 := by
    simpa [prefixWord, tailWord_3337116, baseEnd_3337116] using wordTrace_append hprefix tailTrace_3337116
  have hstable : (prefixWord ++ tailWord_3337116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337116).length < 2 ^ (prefixWord ++ tailWord_3337116).sum := by decide
  have hdescent : baseEnd_3337116 < baseStart_3337116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337119 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3337119 : Nat := 118140960795 + 3337119 * 2 ^ 59
def prefixEnd_3337119 : Nat := 4983230072969 + 3 ^ 40 * 3337119 * 2
def baseEnd_3337119 : Nat := 1713546048251434240265375

theorem tailTrace_3337119 : CollatzResearch.WordTrace tailWord_3337119 prefixEnd_3337119 1713546048251434240265375 := by
  unfold tailWord_3337119
  simp only [CollatzResearch.WordTrace]
  refine ⟨121714729197195272395502411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81143152798130181597001607 121714729197195272395502411)
  ·
    refine ⟨182572093795792908593253617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121714729197195272395502411 182572093795792908593253617)
    ·
      refine ⟨136929070346844681444940213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182572093795792908593253617 136929070346844681444940213)
      ·
        refine ⟨12837100345016688885463145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136929070346844681444940213 12837100345016688885463145)
        ·
          refine ⟨9627825258762516664097359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12837100345016688885463145 9627825258762516664097359)
          ·
            refine ⟨14441737888143774996146039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627825258762516664097359 14441737888143774996146039)
            ·
              refine ⟨21662606832215662494219059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14441737888143774996146039 21662606832215662494219059)
              ·
                refine ⟨32493910248323493741328589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21662606832215662494219059 32493910248323493741328589)
                ·
                  refine ⟨12185216343121310152998221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32493910248323493741328589 12185216343121310152998221)
                  ·
                    refine ⟨4569456128670491307374333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12185216343121310152998221 4569456128670491307374333)
                    ·
                      refine ⟨1713546048251434240265375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569456128670491307374333 1713546048251434240265375)
                      ·
                        rfl

theorem cell23_3337119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3337119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337119 prefixEnd_3337119 := by exact prefixLift 3337119
  have htrace : WordTrace (prefixWord ++ tailWord_3337119) baseStart_3337119 baseEnd_3337119 := by
    simpa [prefixWord, tailWord_3337119, baseEnd_3337119] using wordTrace_append hprefix tailTrace_3337119
  have hstable : (prefixWord ++ tailWord_3337119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337119).length < 2 ^ (prefixWord ++ tailWord_3337119).sum := by decide
  have hdescent : baseEnd_3337119 < baseStart_3337119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337152 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_3337152 : Nat := 118140960795 + 3337152 * 2 ^ 59
def prefixEnd_3337152 : Nat := 4983230072969 + 3 ^ 40 * 3337152 * 2
def baseEnd_3337152 : Nat := 571187664371010870384241

theorem tailTrace_3337152 : CollatzResearch.WordTrace tailWord_3337152 prefixEnd_3337152 571187664371010870384241 := by
  unfold tailWord_3337152
  simp only [CollatzResearch.WordTrace]
  refine ⟨60857966403037859515726855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81143955204050479354302473 60857966403037859515726855)
  ·
    refine ⟨91286949604556789273590283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60857966403037859515726855 91286949604556789273590283)
    ·
      refine ⟨136930424406835183910385425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91286949604556789273590283 136930424406835183910385425)
      ·
        refine ⟨102697818305126387932789069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136930424406835183910385425 102697818305126387932789069)
        ·
          refine ⟨38511681864422395474795901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102697818305126387932789069 38511681864422395474795901)
          ·
            refine ⟨14441880699158398303048463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38511681864422395474795901 14441880699158398303048463)
            ·
              refine ⟨21662821048737597454572695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14441880699158398303048463 21662821048737597454572695)
              ·
                refine ⟨32494231573106396181859043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21662821048737597454572695 32494231573106396181859043)
                ·
                  refine ⟨48741347359659594272788565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32494231573106396181859043 48741347359659594272788565)
                  ·
                    refine ⟨571187664371010870384241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48741347359659594272788565 571187664371010870384241)
                    ·
                      rfl

theorem cell23_3337152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_3337152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337152 prefixEnd_3337152 := by exact prefixLift 3337152
  have htrace : WordTrace (prefixWord ++ tailWord_3337152) baseStart_3337152 baseEnd_3337152 := by
    simpa [prefixWord, tailWord_3337152, baseEnd_3337152] using wordTrace_append hprefix tailTrace_3337152
  have hstable : (prefixWord ++ tailWord_3337152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337152).length < 2 ^ (prefixWord ++ tailWord_3337152).sum := by decide
  have hdescent : baseEnd_3337152 < baseStart_3337152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337176 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_3337176 : Nat := 118140960795 + 3337176 * 2 ^ 59
def prefixEnd_3337176 : Nat := 4983230072969 + 3 ^ 40 * 3337176 * 2
def baseEnd_3337176 : Nat := 1713575316648740517252613

theorem tailTrace_3337176 : CollatzResearch.WordTrace tailWord_3337176 prefixEnd_3337176 1713575316648740517252613 := by
  unfold tailWord_3337176
  simp only [CollatzResearch.WordTrace]
  refine ⟨60858404078994385565163691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81144538771992514086884921 60858404078994385565163691)
  ·
    refine ⟨91287606118491578347745537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60858404078994385565163691 91287606118491578347745537)
    ·
      refine ⟨68465704588868683760809153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91287606118491578347745537 68465704588868683760809153)
      ·
        refine ⟨51349278441651512820606865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68465704588868683760809153 51349278441651512820606865)
        ·
          refine ⟨38511958831238634615455149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51349278441651512820606865 38511958831238634615455149)
          ·
            refine ⟨14441984561714487980795681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38511958831238634615455149 14441984561714487980795681)
            ·
              refine ⟨10831488421285865985596761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14441984561714487980795681 10831488421285865985596761)
              ·
                refine ⟨8123616315964399489197571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10831488421285865985596761 8123616315964399489197571)
                ·
                  refine ⟨12185424473946599233796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123616315964399489197571 12185424473946599233796357)
                  ·
                    refine ⟨2284767088864987356336817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12185424473946599233796357 2284767088864987356336817)
                    ·
                      refine ⟨1713575316648740517252613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284767088864987356336817 1713575316648740517252613)
                      ·
                        rfl

theorem cell23_3337176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_3337176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337176 prefixEnd_3337176 := by exact prefixLift 3337176
  have htrace : WordTrace (prefixWord ++ tailWord_3337176) baseStart_3337176 baseEnd_3337176 := by
    simpa [prefixWord, tailWord_3337176, baseEnd_3337176] using wordTrace_append hprefix tailTrace_3337176
  have hstable : (prefixWord ++ tailWord_3337176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337176).length < 2 ^ (prefixWord ++ tailWord_3337176).sum := by decide
  have hdescent : baseEnd_3337176 < baseStart_3337176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337186 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3337186 : Nat := 118140960795 + 3337186 * 2 ^ 59
def prefixEnd_3337186 : Nat := 4983230072969 + 3 ^ 40 * 3337186 * 2
def baseEnd_3337186 : Nat := 571193483818428492709189

theorem tailTrace_3337186 : CollatzResearch.WordTrace tailWord_3337186 prefixEnd_3337186 571193483818428492709189 := by
  unfold tailWord_3337186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30429293221988135709547853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81144781925301695225460941 30429293221988135709547853)
  ·
    refine ⟨11410984958245550891080445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30429293221988135709547853 11410984958245550891080445)
    ·
      refine ⟨4279119359342081584155167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11410984958245550891080445 4279119359342081584155167)
      ·
        refine ⟨6418679039013122376232751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279119359342081584155167 6418679039013122376232751)
        ·
          refine ⟨9628018558519683564349127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418679039013122376232751 9628018558519683564349127)
          ·
            refine ⟨14442027837779525346523691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628018558519683564349127 14442027837779525346523691)
            ·
              refine ⟨21663041756669288019785537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442027837779525346523691 21663041756669288019785537)
              ·
                refine ⟨16247281317501966014839153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21663041756669288019785537 16247281317501966014839153)
                ·
                  refine ⟨12185460988126474511129365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16247281317501966014839153 12185460988126474511129365)
                  ·
                    refine ⟨571193483818428492709189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12185460988126474511129365 571193483818428492709189)
                    ·
                      rfl

theorem cell23_3337186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3337186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337186 prefixEnd_3337186 := by exact prefixLift 3337186
  have htrace : WordTrace (prefixWord ++ tailWord_3337186) baseStart_3337186 baseEnd_3337186 := by
    simpa [prefixWord, tailWord_3337186, baseEnd_3337186] using wordTrace_append hprefix tailTrace_3337186
  have hstable : (prefixWord ++ tailWord_3337186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337186).length < 2 ^ (prefixWord ++ tailWord_3337186).sum := by decide
  have hdescent : baseEnd_3337186 < baseStart_3337186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337199 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 7]
def baseStart_3337199 : Nat := 118140960795 + 3337199 * 2 ^ 59
def prefixEnd_3337199 : Nat := 4983230072969 + 3 ^ 40 * 3337199 * 2
def baseEnd_3337199 : Nat := 190398569633754880807223

theorem tailTrace_3337199 : CollatzResearch.WordTrace tailWord_3337199 prefixEnd_3337199 190398569633754880807223 := by
  unfold tailWord_3337199
  simp only [CollatzResearch.WordTrace]
  refine ⟨121717647036905446058414651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81145098024603630705609767 121717647036905446058414651)
  ·
    refine ⟨182576470555358169087621977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121717647036905446058414651 182576470555358169087621977)
    ·
      refine ⟨136932352916518626815716483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182576470555358169087621977 136932352916518626815716483)
      ·
        refine ⟨205398529374777940223574725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136932352916518626815716483 205398529374777940223574725)
        ·
          refine ⟨38512224257770863791920261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205398529374777940223574725 38512224257770863791920261)
          ·
            refine ⟨7221042048332036960985049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38512224257770863791920261 7221042048332036960985049)
            ·
              refine ⟨5415781536249027720738787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221042048332036960985049 5415781536249027720738787)
              ·
                refine ⟨8123672304373541581108181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415781536249027720738787 8123672304373541581108181)
                ·
                  refine ⟨190398569633754880807223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8123672304373541581108181 190398569633754880807223)
                  ·
                    rfl

theorem cell23_3337199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 7].length) (baseStart_3337199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337199 prefixEnd_3337199 := by exact prefixLift 3337199
  have htrace : WordTrace (prefixWord ++ tailWord_3337199) baseStart_3337199 baseEnd_3337199 := by
    simpa [prefixWord, tailWord_3337199, baseEnd_3337199] using wordTrace_append hprefix tailTrace_3337199
  have hstable : (prefixWord ++ tailWord_3337199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337199).length < 2 ^ (prefixWord ++ tailWord_3337199).sum := by decide
  have hdescent : baseEnd_3337199 < baseStart_3337199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337204 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3337204 : Nat := 118140960795 + 3337204 * 2 ^ 59
def prefixEnd_3337204 : Nat := 4983230072969 + 3 ^ 40 * 3337204 * 2
def baseEnd_3337204 : Nat := 1713589694107066407702485

theorem tailTrace_3337204 : CollatzResearch.WordTrace tailWord_3337204 prefixEnd_3337204 1713589694107066407702485 := by
  unfold tailWord_3337204
  simp only [CollatzResearch.WordTrace]
  refine ⟨60858914700943665956173333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81145219601258221274897777 60858914700943665956173333)
  ·
    refine ⟨2852761626606734341695625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60858914700943665956173333 2852761626606734341695625)
    ·
      refine ⟨2139571219955050756271719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2852761626606734341695625 2139571219955050756271719)
      ·
        refine ⟨3209356829932576134407579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139571219955050756271719 3209356829932576134407579)
        ·
          refine ⟨4814035244898864201611369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209356829932576134407579 4814035244898864201611369)
          ·
            refine ⟨3610526433674148151208527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4814035244898864201611369 3610526433674148151208527)
            ·
              refine ⟨5415789650511222226812791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610526433674148151208527 5415789650511222226812791)
              ·
                refine ⟨8123684475766833340219187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415789650511222226812791 8123684475766833340219187)
                ·
                  refine ⟨12185526713650250010328781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123684475766833340219187 12185526713650250010328781)
                  ·
                    refine ⟨4569572517618843753873293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12185526713650250010328781 4569572517618843753873293)
                    ·
                      refine ⟨1713589694107066407702485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569572517618843753873293 1713589694107066407702485)
                      ·
                        rfl

theorem cell23_3337204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3337204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337204 prefixEnd_3337204 := by exact prefixLift 3337204
  have htrace : WordTrace (prefixWord ++ tailWord_3337204) baseStart_3337204 baseEnd_3337204 := by
    simpa [prefixWord, tailWord_3337204, baseEnd_3337204] using wordTrace_append hprefix tailTrace_3337204
  have hstable : (prefixWord ++ tailWord_3337204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337204).length < 2 ^ (prefixWord ++ tailWord_3337204).sum := by decide
  have hdescent : baseEnd_3337204 < baseStart_3337204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337206 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3337206 : Nat := 118140960795 + 3337206 * 2 ^ 59
def prefixEnd_3337206 : Nat := 4983230072969 + 3 ^ 40 * 3337206 * 2
def baseEnd_3337206 : Nat := 1713590721068375399877475

theorem tailTrace_3337206 : CollatzResearch.WordTrace tailWord_3337206 prefixEnd_3337206 1713590721068375399877475 := by
  unfold tailWord_3337206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607368896742505390869967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81145268231920057502612981 7607368896742505390869967)
  ·
    refine ⟨11411053345113758086304951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7607368896742505390869967 11411053345113758086304951)
    ·
      refine ⟨17116580017670637129457427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11411053345113758086304951 17116580017670637129457427)
      ·
        refine ⟨25674870026505955694186141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116580017670637129457427 25674870026505955694186141)
        ·
          refine ⟨9628076259939733385319803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25674870026505955694186141 9628076259939733385319803)
          ·
            refine ⟨14442114389909600077979705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628076259939733385319803 14442114389909600077979705)
            ·
              refine ⟨10831585792432200058484779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14442114389909600077979705 10831585792432200058484779)
              ·
                refine ⟨16247378688648300087727169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831585792432200058484779 16247378688648300087727169)
                ·
                  refine ⟨12185534016486225065795377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16247378688648300087727169 12185534016486225065795377)
                  ·
                    refine ⟨9139150512364668799346533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12185534016486225065795377 9139150512364668799346533)
                    ·
                      refine ⟨1713590721068375399877475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9139150512364668799346533 1713590721068375399877475)
                      ·
                        rfl

theorem cell23_3337206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3337206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337206 prefixEnd_3337206 := by exact prefixLift 3337206
  have htrace : WordTrace (prefixWord ++ tailWord_3337206) baseStart_3337206 baseEnd_3337206 := by
    simpa [prefixWord, tailWord_3337206, baseEnd_3337206] using wordTrace_append hprefix tailTrace_3337206
  have hstable : (prefixWord ++ tailWord_3337206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337206).length < 2 ^ (prefixWord ++ tailWord_3337206).sum := by decide
  have hdescent : baseEnd_3337206 < baseStart_3337206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337209 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3337209 : Nat := 118140960795 + 3337209 * 2 ^ 59
def prefixEnd_3337209 : Nat := 4983230072969 + 3 ^ 40 * 3337209 * 2
def baseEnd_3337209 : Nat := 1713592261510338888139961

theorem tailTrace_3337209 : CollatzResearch.WordTrace tailWord_3337209 prefixEnd_3337209 1713592261510338888139961 := by
  unfold tailWord_3337209
  simp only [CollatzResearch.WordTrace]
  refine ⟨121718011766869217766278681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81145341177912811844185787 121718011766869217766278681)
  ·
    refine ⟨91288508825151913324709011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121718011766869217766278681 91288508825151913324709011)
    ·
      refine ⟨136932763237727869987063517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91288508825151913324709011 136932763237727869987063517)
      ·
        refine ⟨51349786214147951245148819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136932763237727869987063517 51349786214147951245148819)
        ·
          refine ⟨77024679321221926867723229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51349786214147951245148819 77024679321221926867723229)
          ·
            refine ⟨28884254745458222575396211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77024679321221926867723229 28884254745458222575396211)
            ·
              refine ⟨43326382118187333863094317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28884254745458222575396211 43326382118187333863094317)
              ·
                refine ⟨16247393294320250198660369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43326382118187333863094317 16247393294320250198660369)
                ·
                  refine ⟨12185544970740187648995277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16247393294320250198660369 12185544970740187648995277)
                  ·
                    refine ⟨4569579364027570368373229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12185544970740187648995277 4569579364027570368373229)
                    ·
                      refine ⟨1713592261510338888139961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569579364027570368373229 1713592261510338888139961)
                      ·
                        rfl

theorem cell23_3337209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3337209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337209 prefixEnd_3337209 := by exact prefixLift 3337209
  have htrace : WordTrace (prefixWord ++ tailWord_3337209) baseStart_3337209 baseEnd_3337209 := by
    simpa [prefixWord, tailWord_3337209, baseEnd_3337209] using wordTrace_append hprefix tailTrace_3337209
  have hstable : (prefixWord ++ tailWord_3337209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337209).length < 2 ^ (prefixWord ++ tailWord_3337209).sum := by decide
  have hdescent : baseEnd_3337209 < baseStart_3337209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337266 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2]
def baseStart_3337266 : Nat := 118140960795 + 3337266 * 2 ^ 59
def prefixEnd_3337266 : Nat := 4983230072969 + 3 ^ 40 * 3337266 * 2
def baseEnd_3337266 : Nat := 1713621529907645165127199

theorem tailTrace_3337266 : CollatzResearch.WordTrace tailWord_3337266 prefixEnd_3337266 1713621529907645165127199 := by
  unfold tailWord_3337266
  simp only [CollatzResearch.WordTrace]
  refine ⟨30430022681915679125275913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81146727151775144334069101 30430022681915679125275913)
  ·
    refine ⟨22822517011436759343956935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30430022681915679125275913 22822517011436759343956935)
    ·
      refine ⟨34233775517155139015935403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22822517011436759343956935 34233775517155139015935403)
      ·
        refine ⟨51350663275732708523903105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34233775517155139015935403 51350663275732708523903105)
        ·
          refine ⟨38512997456799531392927329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51350663275732708523903105 38512997456799531392927329)
          ·
            refine ⟨28884748092599648544695497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38512997456799531392927329 28884748092599648544695497)
            ·
              refine ⟨21663561069449736408521623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28884748092599648544695497 21663561069449736408521623)
              ·
                refine ⟨32495341604174604612782435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21663561069449736408521623 32495341604174604612782435)
                ·
                  refine ⟨48743012406261906919173653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32495341604174604612782435 48743012406261906919173653)
                  ·
                    refine ⟨2284828706543526886836265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48743012406261906919173653 2284828706543526886836265)
                    ·
                      refine ⟨1713621529907645165127199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284828706543526886836265 1713621529907645165127199)
                      ·
                        rfl

theorem cell23_3337266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_3337266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337266 prefixEnd_3337266 := by exact prefixLift 3337266
  have htrace : WordTrace (prefixWord ++ tailWord_3337266) baseStart_3337266 baseEnd_3337266 := by
    simpa [prefixWord, tailWord_3337266, baseEnd_3337266] using wordTrace_append hprefix tailTrace_3337266
  have hstable : (prefixWord ++ tailWord_3337266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337266).length < 2 ^ (prefixWord ++ tailWord_3337266).sum := by decide
  have hdescent : baseEnd_3337266 < baseStart_3337266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337353 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 1, 5]
def baseStart_3337353 : Nat := 118140960795 + 3337353 * 2 ^ 59
def prefixEnd_3337353 : Nat := 4983230072969 + 3 ^ 40 * 3337353 * 2
def baseEnd_3337353 : Nat := 571222067574862108246433

theorem tailTrace_3337353 : CollatzResearch.WordTrace tailWord_3337353 prefixEnd_3337353 571222067574862108246433 := by
  unfold tailWord_3337353
  simp only [CollatzResearch.WordTrace]
  refine ⟨121723263878347530359520713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81148842585565020239680475 121723263878347530359520713)
  ·
    refine ⟨91292447908760647769640535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121723263878347530359520713 91292447908760647769640535)
    ·
      refine ⟨136938671863140971654460803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91292447908760647769640535 136938671863140971654460803)
      ·
        refine ⟨205408007794711457481691205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136938671863140971654460803 205408007794711457481691205)
        ·
          refine ⟨38514001461508398277817101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205408007794711457481691205 38514001461508398277817101)
          ·
            refine ⟨14442750548065649354181413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38514001461508398277817101 14442750548065649354181413)
            ·
              refine ⟨2708015727762309253909015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14442750548065649354181413 2708015727762309253909015)
              ·
                refine ⟨4062023591643463880863523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708015727762309253909015 4062023591643463880863523)
                ·
                  refine ⟨6093035387465195821295285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062023591643463880863523 6093035387465195821295285)
                  ·
                    refine ⟨571222067574862108246433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6093035387465195821295285 571222067574862108246433)
                    ·
                      rfl

theorem cell23_3337353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_3337353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337353 prefixEnd_3337353 := by exact prefixLift 3337353
  have htrace : WordTrace (prefixWord ++ tailWord_3337353) baseStart_3337353 baseEnd_3337353 := by
    simpa [prefixWord, tailWord_3337353, baseEnd_3337353] using wordTrace_append hprefix tailTrace_3337353
  have hstable : (prefixWord ++ tailWord_3337353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337353).length < 2 ^ (prefixWord ++ tailWord_3337353).sum := by decide
  have hdescent : baseEnd_3337353 < baseStart_3337353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337356 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 8, 2]
def baseStart_3337356 : Nat := 118140960795 + 3337356 * 2 ^ 59
def prefixEnd_3337356 : Nat := 4983230072969 + 3 ^ 40 * 3337356 * 2
def baseEnd_3337356 : Nat := 1713667743166549813001785

theorem tailTrace_3337356 : CollatzResearch.WordTrace tailWord_3337356 prefixEnd_3337356 1713667743166549813001785 := by
  unfold tailWord_3337356
  simp only [CollatzResearch.WordTrace]
  refine ⟨60861686648668330935939961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81148915531557774581253281 60861686648668330935939961)
  ·
    refine ⟨45646264986501248201954971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60861686648668330935939961 45646264986501248201954971)
    ·
      refine ⟨68469397479751872302932457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45646264986501248201954971 68469397479751872302932457)
      ·
        refine ⟨51352048109813904227199343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68469397479751872302932457 51352048109813904227199343)
        ·
          refine ⟨77028072164720856340799015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51352048109813904227199343 77028072164720856340799015)
          ·
            refine ⟨115542108247081284511198523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77028072164720856340799015 115542108247081284511198523)
            ·
              refine ⟨173313162370621926766797785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115542108247081284511198523 173313162370621926766797785)
              ·
                refine ⟨129984871777966445075098339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173313162370621926766797785 129984871777966445075098339)
                ·
                  refine ⟨194977307666949667612647509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129984871777966445075098339 194977307666949667612647509)
                  ·
                    refine ⟨2284890324222066417335713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 194977307666949667612647509 2284890324222066417335713)
                    ·
                      refine ⟨1713667743166549813001785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284890324222066417335713 1713667743166549813001785)
                      ·
                        rfl

theorem cell23_3337356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_3337356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337356 prefixEnd_3337356 := by exact prefixLift 3337356
  have htrace : WordTrace (prefixWord ++ tailWord_3337356) baseStart_3337356 baseEnd_3337356 := by
    simpa [prefixWord, tailWord_3337356, baseEnd_3337356] using wordTrace_append hprefix tailTrace_3337356
  have hstable : (prefixWord ++ tailWord_3337356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337356).length < 2 ^ (prefixWord ++ tailWord_3337356).sum := by decide
  have hdescent : baseEnd_3337356 < baseStart_3337356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337369 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3337369 : Nat := 118140960795 + 3337369 * 2 ^ 59
def prefixEnd_3337369 : Nat := 4983230072969 + 3 ^ 40 * 3337369 * 2
def baseEnd_3337369 : Nat := 1713674418415058262139225

theorem tailTrace_3337369 : CollatzResearch.WordTrace tailWord_3337369 prefixEnd_3337369 1713674418415058262139225 := by
  unfold tailWord_3337369
  simp only [CollatzResearch.WordTrace]
  refine ⟨121723847446289565092103161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81149231630859710061402107 121723847446289565092103161)
  ·
    refine ⟨91292885584717173819077371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121723847446289565092103161 91292885584717173819077371)
    ·
      refine ⟨136939328377075760728616057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91292885584717173819077371 136939328377075760728616057)
      ·
        refine ⟨102704496282806820546462043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136939328377075760728616057 102704496282806820546462043)
        ·
          refine ⟨154056744424210230819693065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102704496282806820546462043 154056744424210230819693065)
          ·
            refine ⟨115542558318157673114769799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154056744424210230819693065 115542558318157673114769799)
            ·
              refine ⟨173313837477236509672154699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115542558318157673114769799 173313837477236509672154699)
              ·
                refine ⟨259970756215854764508232049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173313837477236509672154699 259970756215854764508232049)
                ·
                  refine ⟨194978067161891073381174037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259970756215854764508232049 194978067161891073381174037)
                  ·
                    refine ⟨9139596898213644064742533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194978067161891073381174037 9139596898213644064742533)
                    ·
                      refine ⟨1713674418415058262139225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9139596898213644064742533 1713674418415058262139225)
                      ·
                        rfl

theorem cell23_3337369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3337369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337369 prefixEnd_3337369 := by exact prefixLift 3337369
  have htrace : WordTrace (prefixWord ++ tailWord_3337369) baseStart_3337369 baseEnd_3337369 := by
    simpa [prefixWord, tailWord_3337369, baseEnd_3337369] using wordTrace_append hprefix tailTrace_3337369
  have hstable : (prefixWord ++ tailWord_3337369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337369).length < 2 ^ (prefixWord ++ tailWord_3337369).sum := by decide
  have hdescent : baseEnd_3337369 < baseStart_3337369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337376 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3337376 : Nat := 118140960795 + 3337376 * 2 ^ 59
def prefixEnd_3337376 : Nat := 4983230072969 + 3 ^ 40 * 3337376 * 2
def baseEnd_3337376 : Nat := 1713678012779639734751693

theorem tailTrace_3337376 : CollatzResearch.WordTrace tailWord_3337376 prefixEnd_3337376 1713678012779639734751693 := by
  unfold tailWord_3337376
  simp only [CollatzResearch.WordTrace]
  refine ⟨60862051378632102643803991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81149401838176136858405321 60862051378632102643803991)
  ·
    refine ⟨91293077067948153965705987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60862051378632102643803991 91293077067948153965705987)
    ·
      refine ⟨136939615601922230948558981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91293077067948153965705987 136939615601922230948558981)
      ·
        refine ⟨25676177925360418302854809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136939615601922230948558981 25676177925360418302854809)
        ·
          refine ⟨19257133444020313727141107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25676177925360418302854809 19257133444020313727141107)
          ·
            refine ⟨28885700166030470590711661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19257133444020313727141107 28885700166030470590711661)
            ·
              refine ⟨10832137562261426471516873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28885700166030470590711661 10832137562261426471516873)
              ·
                refine ⟨8124103171696069853637655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10832137562261426471516873 8124103171696069853637655)
                ·
                  refine ⟨12186154757544104780456483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124103171696069853637655 12186154757544104780456483)
                  ·
                    refine ⟨18279232136316157170684725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12186154757544104780456483 18279232136316157170684725)
                    ·
                      refine ⟨1713678012779639734751693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18279232136316157170684725 1713678012779639734751693)
                      ·
                        rfl

theorem cell23_3337376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3337376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337376 prefixEnd_3337376 := by exact prefixLift 3337376
  have htrace : WordTrace (prefixWord ++ tailWord_3337376) baseStart_3337376 baseEnd_3337376 := by
    simpa [prefixWord, tailWord_3337376, baseEnd_3337376] using wordTrace_append hprefix tailTrace_3337376
  have hstable : (prefixWord ++ tailWord_3337376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337376).length < 2 ^ (prefixWord ++ tailWord_3337376).sum := by decide
  have hdescent : baseEnd_3337376 < baseStart_3337376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337383 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3337383 : Nat := 118140960795 + 3337383 * 2 ^ 59
def prefixEnd_3337383 : Nat := 4983230072969 + 3 ^ 40 * 3337383 * 2
def baseEnd_3337383 : Nat := 571227202381407069121387

theorem tailTrace_3337383 : CollatzResearch.WordTrace tailWord_3337383 prefixEnd_3337383 571227202381407069121387 := by
  unfold tailWord_3337383
  simp only [CollatzResearch.WordTrace]
  refine ⟨121724358068238845483112803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81149572045492563655408535 121724358068238845483112803)
  ·
    refine ⟨182586537102358268224669205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121724358068238845483112803 182586537102358268224669205)
    ·
      refine ⟨8558743926673043823031369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182586537102358268224669205 8558743926673043823031369)
      ·
        refine ⟨6419057945004782867273527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8558743926673043823031369 6419057945004782867273527)
        ·
          refine ⟨9628586917507174300910291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419057945004782867273527 9628586917507174300910291)
          ·
            refine ⟨14442880376260761451365437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628586917507174300910291 14442880376260761451365437)
            ·
              refine ⟨5416080141097785544262039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14442880376260761451365437 5416080141097785544262039)
              ·
                refine ⟨8124120211646678316393059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5416080141097785544262039 8124120211646678316393059)
                ·
                  refine ⟨12186180317470017474589589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124120211646678316393059 12186180317470017474589589)
                  ·
                    refine ⟨571227202381407069121387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12186180317470017474589589 571227202381407069121387)
                    ·
                      rfl

theorem cell23_3337383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3337383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337383 prefixEnd_3337383 := by exact prefixLift 3337383
  have htrace : WordTrace (prefixWord ++ tailWord_3337383) baseStart_3337383 baseEnd_3337383 := by
    simpa [prefixWord, tailWord_3337383, baseEnd_3337383] using wordTrace_append hprefix tailTrace_3337383
  have hstable : (prefixWord ++ tailWord_3337383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337383).length < 2 ^ (prefixWord ++ tailWord_3337383).sum := by decide
  have hdescent : baseEnd_3337383 < baseStart_3337383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337407 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 1, 2, 2]
def baseStart_3337407 : Nat := 118140960795 + 3337407 * 2 ^ 59
def prefixEnd_3337407 : Nat := 4983230072969 + 3 ^ 40 * 3337407 * 2
def baseEnd_3337407 : Nat := 1713693930679929113464051

theorem tailTrace_3337407 : CollatzResearch.WordTrace tailWord_3337407 prefixEnd_3337407 1713693930679929113464051 := by
  unfold tailWord_3337407
  simp only [CollatzResearch.WordTrace]
  refine ⟨121725233420151897581986475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81150155613434598387990983 121725233420151897581986475)
  ·
    refine ⟨182587850130227846372979713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121725233420151897581986475 182587850130227846372979713)
    ·
      refine ⟨136940887597670884779734785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182587850130227846372979713 136940887597670884779734785)
      ·
        refine ⟨102705665698253163584801089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136940887597670884779734785 102705665698253163584801089)
        ·
          refine ⟨77029249273689872688600817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102705665698253163584801089 77029249273689872688600817)
          ·
            refine ⟨57771936955267404516450613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77029249273689872688600817 57771936955267404516450613)
            ·
              refine ⟨5416119089556319173417245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57771936955267404516450613 5416119089556319173417245)
              ·
                refine ⟨2031044658583619690031467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5416119089556319173417245 2031044658583619690031467)
                ·
                  refine ⟨3046566987875429535047201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031044658583619690031467 3046566987875429535047201)
                  ·
                    refine ⟨2284925240906572151285401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3046566987875429535047201 2284925240906572151285401)
                    ·
                      refine ⟨1713693930679929113464051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284925240906572151285401 1713693930679929113464051)
                      ·
                        rfl

theorem cell23_3337407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_3337407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337407 prefixEnd_3337407 := by exact prefixLift 3337407
  have htrace : WordTrace (prefixWord ++ tailWord_3337407) baseStart_3337407 baseEnd_3337407 := by
    simpa [prefixWord, tailWord_3337407, baseEnd_3337407] using wordTrace_append hprefix tailTrace_3337407
  have hstable : (prefixWord ++ tailWord_3337407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337407).length < 2 ^ (prefixWord ++ tailWord_3337407).sum := by decide
  have hdescent : baseEnd_3337407 < baseStart_3337407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337426 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3337426 : Nat := 118140960795 + 3337426 * 2 ^ 59
def prefixEnd_3337426 : Nat := 4983230072969 + 3 ^ 40 * 3337426 * 2
def baseEnd_3337426 : Nat := 571234562270788179708821

theorem tailTrace_3337426 : CollatzResearch.WordTrace tailWord_3337426 prefixEnd_3337426 571234562270788179708821 := by
  unfold tailWord_3337426
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431481601770765956732033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81150617604722042551285421 30431481601770765956732033)
  ·
    refine ⟨22823611201328074467549025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30431481601770765956732033 22823611201328074467549025)
    ·
      refine ⟨17117708400996055850661769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22823611201328074467549025 17117708400996055850661769)
      ·
        refine ⟨12838281300747041887996327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17117708400996055850661769 12838281300747041887996327)
        ·
          refine ⟨19257421951120562831994491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12838281300747041887996327 19257421951120562831994491)
          ·
            refine ⟨28886132926680844247991737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19257421951120562831994491 28886132926680844247991737)
            ·
              refine ⟨21664599695010633185993803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28886132926680844247991737 21664599695010633185993803)
              ·
                refine ⟨32496899542515949778990705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21664599695010633185993803 32496899542515949778990705)
                ·
                  refine ⟨24372674656886962334243029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32496899542515949778990705 24372674656886962334243029)
                  ·
                    refine ⟨571234562270788179708821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24372674656886962334243029 571234562270788179708821)
                    ·
                      rfl

theorem cell23_3337426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3337426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337426 prefixEnd_3337426 := by exact prefixLift 3337426
  have htrace : WordTrace (prefixWord ++ tailWord_3337426) baseStart_3337426 baseEnd_3337426 := by
    simpa [prefixWord, tailWord_3337426, baseEnd_3337426] using wordTrace_append hprefix tailTrace_3337426
  have hstable : (prefixWord ++ tailWord_3337426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337426).length < 2 ^ (prefixWord ++ tailWord_3337426).sum := by decide
  have hdescent : baseEnd_3337426 < baseStart_3337426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337430 : List Nat := [5, 2, 1, 2, 2, 1, 2, 8]
def baseStart_3337430 : Nat := 118140960795 + 3337430 * 2 ^ 59
def prefixEnd_3337430 : Nat := 4983230072969 + 3 ^ 40 * 3337430 * 2
def baseEnd_3337430 : Nat := 63470582990184537906535

theorem tailTrace_3337430 : CollatzResearch.WordTrace tailWord_3337430 prefixEnd_3337430 63470582990184537906535 := by
  unfold tailWord_3337430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607879518691785781879609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81150714866045715006715829 7607879518691785781879609)
  ·
    refine ⟨5705909639018839336409707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7607879518691785781879609 5705909639018839336409707)
    ·
      refine ⟨8558864458528259004614561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705909639018839336409707 8558864458528259004614561)
      ·
        refine ⟨6419148343896194253460921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8558864458528259004614561 6419148343896194253460921)
        ·
          refine ⟨4814361257922145690095691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6419148343896194253460921 4814361257922145690095691)
          ·
            refine ⟨7221541886883218535143537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814361257922145690095691 7221541886883218535143537)
            ·
              refine ⟨5416156415162413901357653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221541886883218535143537 5416156415162413901357653)
              ·
                refine ⟨63470582990184537906535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5416156415162413901357653 63470582990184537906535)
                ·
                  rfl

theorem cell23_3337430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_3337430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337430 prefixEnd_3337430 := by exact prefixLift 3337430
  have htrace : WordTrace (prefixWord ++ tailWord_3337430) baseStart_3337430 baseEnd_3337430 := by
    simpa [prefixWord, tailWord_3337430, baseEnd_3337430] using wordTrace_append hprefix tailTrace_3337430
  have hstable : (prefixWord ++ tailWord_3337430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337430).length < 2 ^ (prefixWord ++ tailWord_3337430).sum := by decide
  have hdescent : baseEnd_3337430 < baseStart_3337430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337433 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 3, 3, 2]
def baseStart_3337433 : Nat := 118140960795 + 3337433 * 2 ^ 59
def prefixEnd_3337433 : Nat := 4983230072969 + 3 ^ 40 * 3337433 * 2
def baseEnd_3337433 : Nat := 1713707281176946011738931

theorem tailTrace_3337433 : CollatzResearch.WordTrace tailWord_3337433 prefixEnd_3337433 1713707281176946011738931 := by
  unfold tailWord_3337433
  simp only [CollatzResearch.WordTrace]
  refine ⟨121726181718057704022432953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81150787812038469348288635 121726181718057704022432953)
  ·
    refine ⟨91294636288543278016824715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121726181718057704022432953 91294636288543278016824715)
    ·
      refine ⟨136941954432814917025237073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91294636288543278016824715 136941954432814917025237073)
      ·
        refine ⟨102706465824611187768927805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136941954432814917025237073 102706465824611187768927805)
        ·
          refine ⟨38514924684229195413347927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102706465824611187768927805 38514924684229195413347927)
          ·
            refine ⟨57772387026343793120021891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38514924684229195413347927 57772387026343793120021891)
            ·
              refine ⟨86658580539515689680032837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57772387026343793120021891 86658580539515689680032837)
              ·
                refine ⟨16248483851159191815006157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86658580539515689680032837 16248483851159191815006157)
                ·
                  refine ⟨6093181444184696930627309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16248483851159191815006157 6093181444184696930627309)
                  ·
                    refine ⟨2284943041569261348985241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6093181444184696930627309 2284943041569261348985241)
                    ·
                      refine ⟨1713707281176946011738931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284943041569261348985241 1713707281176946011738931)
                      ·
                        rfl

theorem cell23_3337433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_3337433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337433 prefixEnd_3337433 := by exact prefixLift 3337433
  have htrace : WordTrace (prefixWord ++ tailWord_3337433) baseStart_3337433 baseEnd_3337433 := by
    simpa [prefixWord, tailWord_3337433, baseEnd_3337433] using wordTrace_append hprefix tailTrace_3337433
  have hstable : (prefixWord ++ tailWord_3337433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337433).length < 2 ^ (prefixWord ++ tailWord_3337433).sum := by decide
  have hdescent : baseEnd_3337433 < baseStart_3337433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337440 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3]
def baseStart_3337440 : Nat := 118140960795 + 3337440 * 2 ^ 59
def prefixEnd_3337440 : Nat := 4983230072969 + 3 ^ 40 * 3337440 * 2
def baseEnd_3337440 : Nat := 1713710875541527484351399

theorem tailTrace_3337440 : CollatzResearch.WordTrace tailWord_3337440 prefixEnd_3337440 1713710875541527484351399 := by
  unfold tailWord_3337440
  simp only [CollatzResearch.WordTrace]
  refine ⟨60863218514516172108968887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81150958019354896145291849 60863218514516172108968887)
  ·
    refine ⟨91294827771774258163453331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60863218514516172108968887 91294827771774258163453331)
    ·
      refine ⟨136942241657661387245179997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91294827771774258163453331 136942241657661387245179997)
      ·
        refine ⟨51353340621623020216942499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136942241657661387245179997 51353340621623020216942499)
        ·
          refine ⟨77030010932434530325413749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51353340621623020216942499 77030010932434530325413749)
          ·
            refine ⟨7221563524915737218007539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77030010932434530325413749 7221563524915737218007539)
            ·
              refine ⟨10832345287373605827011309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221563524915737218007539 10832345287373605827011309)
              ·
                refine ⟨4062129482765102185129241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10832345287373605827011309 4062129482765102185129241)
                ·
                  refine ⟨3046597112073826638846931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062129482765102185129241 3046597112073826638846931)
                  ·
                    refine ⟨4569895668110739958270397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3046597112073826638846931 4569895668110739958270397)
                    ·
                      refine ⟨1713710875541527484351399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569895668110739958270397 1713710875541527484351399)
                      ·
                        rfl

theorem cell23_3337440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_3337440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337440 prefixEnd_3337440 := by exact prefixLift 3337440
  have htrace : WordTrace (prefixWord ++ tailWord_3337440) baseStart_3337440 baseEnd_3337440 := by
    simpa [prefixWord, tailWord_3337440, baseEnd_3337440] using wordTrace_append hprefix tailTrace_3337440
  have hstable : (prefixWord ++ tailWord_3337440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337440).length < 2 ^ (prefixWord ++ tailWord_3337440).sum := by decide
  have hdescent : baseEnd_3337440 < baseStart_3337440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337450 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2]
def baseStart_3337450 : Nat := 118140960795 + 3337450 * 2 ^ 59
def prefixEnd_3337450 : Nat := 4983230072969 + 3 ^ 40 * 3337450 * 2
def baseEnd_3337450 : Nat := 1713716010348072445226353

theorem tailTrace_3337450 : CollatzResearch.WordTrace tailWord_3337450 prefixEnd_3337450 1713716010348072445226353 := by
  unfold tailWord_3337450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431700439749028981450451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81151201172664077283867869 30431700439749028981450451)
  ·
    refine ⟨45647550659623543472175677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30431700439749028981450451 45647550659623543472175677)
    ·
      refine ⟨17117831497358828802065879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45647550659623543472175677 17117831497358828802065879)
      ·
        refine ⟨25676747246038243203098819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17117831497358828802065879 25676747246038243203098819)
        ·
          refine ⟨38515120869057364804648229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25676747246038243203098819 38515120869057364804648229)
          ·
            refine ⟨7221585162948255900871543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38515120869057364804648229 7221585162948255900871543)
            ·
              refine ⟨10832377744422383851307315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221585162948255900871543 10832377744422383851307315)
              ·
                refine ⟨16248566616633575776960973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10832377744422383851307315 16248566616633575776960973)
                ·
                  refine ⟨6093212481237590916360365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16248566616633575776960973 6093212481237590916360365)
                  ·
                    refine ⟨2284954680464096593635137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6093212481237590916360365 2284954680464096593635137)
                    ·
                      refine ⟨1713716010348072445226353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284954680464096593635137 1713716010348072445226353)
                      ·
                        rfl

theorem cell23_3337450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_3337450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337450 prefixEnd_3337450 := by exact prefixLift 3337450
  have htrace : WordTrace (prefixWord ++ tailWord_3337450) baseStart_3337450 baseEnd_3337450 := by
    simpa [prefixWord, tailWord_3337450, baseEnd_3337450] using wordTrace_append hprefix tailTrace_3337450
  have hstable : (prefixWord ++ tailWord_3337450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337450).length < 2 ^ (prefixWord ++ tailWord_3337450).sum := by decide
  have hdescent : baseEnd_3337450 < baseStart_3337450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337463 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_3337463 : Nat := 118140960795 + 3337463 * 2 ^ 59
def prefixEnd_3337463 : Nat := 4983230072969 + 3 ^ 40 * 3337463 * 2
def baseEnd_3337463 : Nat := 1713722685596580894363793

theorem tailTrace_3337463 : CollatzResearch.WordTrace tailWord_3337463 prefixEnd_3337463 1713722685596580894363793 := by
  unfold tailWord_3337463
  simp only [CollatzResearch.WordTrace]
  refine ⟨121727275907949019146025043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81151517271966012764016695 121727275907949019146025043)
  ·
    refine ⟨182590913861923528719037565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121727275907949019146025043 182590913861923528719037565)
    ·
      refine ⟨68471592698221323269639087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182590913861923528719037565 68471592698221323269639087)
      ·
        refine ⟨102707389047331984904458631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68471592698221323269639087 102707389047331984904458631)
        ·
          refine ⟨154061083570997977356687947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102707389047331984904458631 154061083570997977356687947)
          ·
            refine ⟨231091625356496966035031921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154061083570997977356687947 231091625356496966035031921)
            ·
              refine ⟨173318719017372724526273941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231091625356496966035031921 173318719017372724526273941)
              ·
                refine ⟨8124314953939346462169091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173318719017372724526273941 8124314953939346462169091)
                ·
                  refine ⟨12186472430909019693253637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124314953939346462169091 12186472430909019693253637)
                  ·
                    refine ⟨2284963580795441192485057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12186472430909019693253637 2284963580795441192485057)
                    ·
                      refine ⟨1713722685596580894363793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2284963580795441192485057 1713722685596580894363793)
                      ·
                        rfl

theorem cell23_3337463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_3337463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337463 prefixEnd_3337463 := by exact prefixLift 3337463
  have htrace : WordTrace (prefixWord ++ tailWord_3337463) baseStart_3337463 baseEnd_3337463 := by
    simpa [prefixWord, tailWord_3337463, baseEnd_3337463] using wordTrace_append hprefix tailTrace_3337463
  have hstable : (prefixWord ++ tailWord_3337463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337463).length < 2 ^ (prefixWord ++ tailWord_3337463).sum := by decide
  have hdescent : baseEnd_3337463 < baseStart_3337463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337466 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_3337466 : Nat := 118140960795 + 3337466 * 2 ^ 59
def prefixEnd_3337466 : Nat := 4983230072969 + 3 ^ 40 * 3337466 * 2
def baseEnd_3337466 : Nat := 1713724226038544382626279

theorem tailTrace_3337466 : CollatzResearch.WordTrace tailWord_3337466 prefixEnd_3337466 1713724226038544382626279 := by
  unfold tailWord_3337466
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431846331734537664596063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81151590217958767105589501 30431846331734537664596063)
  ·
    refine ⟨45647769497601806496894095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30431846331734537664596063 45647769497601806496894095)
    ·
      refine ⟨68471654246402709745341143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45647769497601806496894095 68471654246402709745341143)
      ·
        refine ⟨102707481369604064618011715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68471654246402709745341143 102707481369604064618011715)
        ·
          refine ⟨154061222054406096927017573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102707481369604064618011715 154061222054406096927017573)
          ·
            refine ⟨28886479135201143173815795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154061222054406096927017573 28886479135201143173815795)
            ·
              refine ⟨43329718702801714760723693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28886479135201143173815795 43329718702801714760723693)
              ·
                refine ⟨16248644513550643035271385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43329718702801714760723693 16248644513550643035271385)
                ·
                  refine ⟨12186483385162982276453539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16248644513550643035271385 12186483385162982276453539)
                  ·
                    refine ⟨18279725077744473414680309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12186483385162982276453539 18279725077744473414680309)
                    ·
                      refine ⟨1713724226038544382626279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18279725077744473414680309 1713724226038544382626279)
                      ·
                        rfl

theorem cell23_3337466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_3337466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337466 prefixEnd_3337466 := by exact prefixLift 3337466
  have htrace : WordTrace (prefixWord ++ tailWord_3337466) baseStart_3337466 baseEnd_3337466 := by
    simpa [prefixWord, tailWord_3337466, baseEnd_3337466] using wordTrace_append hprefix tailTrace_3337466
  have hstable : (prefixWord ++ tailWord_3337466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337466).length < 2 ^ (prefixWord ++ tailWord_3337466).sum := by decide
  have hdescent : baseEnd_3337466 < baseStart_3337466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337474 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3337474 : Nat := 118140960795 + 3337474 * 2 ^ 59
def prefixEnd_3337474 : Nat := 4983230072969 + 3 ^ 40 * 3337474 * 2
def baseEnd_3337474 : Nat := 1713728333883780351326243

theorem tailTrace_3337474 : CollatzResearch.WordTrace tailWord_3337474 prefixEnd_3337474 1713728333883780351326243 := by
  unfold tailWord_3337474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30431919277727292006168869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81151784740606112016450317 30431919277727292006168869)
  ·
    refine ⟨5705984864573867251156663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30431919277727292006168869 5705984864573867251156663)
    ·
      refine ⟨8558977296860800876734995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705984864573867251156663 8558977296860800876734995)
      ·
        refine ⟨12838465945291201315102493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8558977296860800876734995 12838465945291201315102493)
        ·
          refine ⟨4814424729484200493163435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12838465945291201315102493 4814424729484200493163435)
          ·
            refine ⟨7221637094226300739745153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814424729484200493163435 7221637094226300739745153)
            ·
              refine ⟨5416227820669725554808865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221637094226300739745153 5416227820669725554808865)
              ·
                refine ⟨4062170865502294166106649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416227820669725554808865 4062170865502294166106649)
                ·
                  refine ⟨3046628149126720624579987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4062170865502294166106649 3046628149126720624579987)
                  ·
                    refine ⟨4569942223690080936869981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3046628149126720624579987 4569942223690080936869981)
                    ·
                      refine ⟨1713728333883780351326243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4569942223690080936869981 1713728333883780351326243)
                      ·
                        rfl

theorem cell23_3337474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3337474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337474 prefixEnd_3337474 := by exact prefixLift 3337474
  have htrace : WordTrace (prefixWord ++ tailWord_3337474) baseStart_3337474 baseEnd_3337474 := by
    simpa [prefixWord, tailWord_3337474, baseEnd_3337474] using wordTrace_append hprefix tailTrace_3337474
  have hstable : (prefixWord ++ tailWord_3337474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337474).length < 2 ^ (prefixWord ++ tailWord_3337474).sum := by decide
  have hdescent : baseEnd_3337474 < baseStart_3337474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337503 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 7]
def baseStart_3337503 : Nat := 118140960795 + 3337503 * 2 ^ 59
def prefixEnd_3337503 : Nat := 4983230072969 + 3 ^ 40 * 3337503 * 2
def baseEnd_3337503 : Nat := 190415913869195637540401

theorem tailTrace_3337503 : CollatzResearch.WordTrace tailWord_3337503 prefixEnd_3337503 190415913869195637540401 := by
  unfold tailWord_3337503
  simp only [CollatzResearch.WordTrace]
  refine ⟨121728734827804105977481163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81152489885202737318320775 121728734827804105977481163)
  ·
    refine ⟨182593102241706158966221745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121728734827804105977481163 182593102241706158966221745)
    ·
      refine ⟨136944826681279619224666309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182593102241706158966221745 136944826681279619224666309)
      ·
        refine ⟨25677155002739928604624933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136944826681279619224666309 25677155002739928604624933)
        ·
          refine ⟨4814466563013736613367175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25677155002739928604624933 4814466563013736613367175)
          ·
            refine ⟨7221699844520604920050763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814466563013736613367175 7221699844520604920050763)
            ·
              refine ⟨10832549766780907380076145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221699844520604920050763 10832549766780907380076145)
              ·
                refine ⟨8124412325085680535057109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10832549766780907380076145 8124412325085680535057109)
                ·
                  refine ⟨190415913869195637540401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8124412325085680535057109 190415913869195637540401)
                  ·
                    rfl

theorem cell23_3337503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 7].length) (baseStart_3337503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337503 prefixEnd_3337503 := by exact prefixLift 3337503
  have htrace : WordTrace (prefixWord ++ tailWord_3337503) baseStart_3337503 baseEnd_3337503 := by
    simpa [prefixWord, tailWord_3337503, baseEnd_3337503] using wordTrace_append hprefix tailTrace_3337503
  have hstable : (prefixWord ++ tailWord_3337503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337503).length < 2 ^ (prefixWord ++ tailWord_3337503).sum := by decide
  have hdescent : baseEnd_3337503 < baseStart_3337503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337570 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3337570 : Nat := 118140960795 + 3337570 * 2 ^ 59
def prefixEnd_3337570 : Nat := 4983230072969 + 3 ^ 40 * 3337570 * 2
def baseEnd_3337570 : Nat := 1713777628026611975725801

theorem tailTrace_3337570 : CollatzResearch.WordTrace tailWord_3337570 prefixEnd_3337570 1713777628026611975725801 := by
  unfold tailWord_3337570
  simp only [CollatzResearch.WordTrace]
  refine ⟨30432794629640344105042541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81154119012374250946780109 30432794629640344105042541)
  ·
    refine ⟨11412297986115129039390953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30432794629640344105042541 11412297986115129039390953)
    ·
      refine ⟨8559223489586346779543215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11412297986115129039390953 8559223489586346779543215)
      ·
        refine ⟨12838835234379520169314823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8559223489586346779543215 12838835234379520169314823)
        ·
          refine ⟨19258252851569280253972235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12838835234379520169314823 19258252851569280253972235)
          ·
            refine ⟨28887379277353920380958353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19258252851569280253972235 28887379277353920380958353)
            ·
              refine ⟨21665534458015440285718765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28887379277353920380958353 21665534458015440285718765)
              ·
                refine ⟨8124575421755790107144537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21665534458015440285718765 8124575421755790107144537)
                ·
                  refine ⟨6093431566316842580358403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8124575421755790107144537 6093431566316842580358403)
                  ·
                    refine ⟨9140147349475263870537605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6093431566316842580358403 9140147349475263870537605)
                    ·
                      refine ⟨1713777628026611975725801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9140147349475263870537605 1713777628026611975725801)
                      ·
                        rfl

theorem cell23_3337570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3337570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337570 prefixEnd_3337570 := by exact prefixLift 3337570
  have htrace : WordTrace (prefixWord ++ tailWord_3337570) baseStart_3337570 baseEnd_3337570 := by
    simpa [prefixWord, tailWord_3337570, baseEnd_3337570] using wordTrace_append hprefix tailTrace_3337570
  have hstable : (prefixWord ++ tailWord_3337570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337570).length < 2 ^ (prefixWord ++ tailWord_3337570).sum := by decide
  have hdescent : baseEnd_3337570 < baseStart_3337570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337573 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3337573 : Nat := 118140960795 + 3337573 * 2 ^ 59
def prefixEnd_3337573 : Nat := 4983230072969 + 3 ^ 40 * 3337573 * 2
def baseEnd_3337573 : Nat := 1713779168468575463988287

theorem tailTrace_3337573 : CollatzResearch.WordTrace tailWord_3337573 prefixEnd_3337573 1713779168468575463988287 := by
  unfold tailWord_3337573
  simp only [CollatzResearch.WordTrace]
  refine ⟨121731287937550507932529373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81154191958367005288352915 121731287937550507932529373)
  ·
    refine ⟨45649232976581440474698515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121731287937550507932529373 45649232976581440474698515)
    ·
      refine ⟨68473849464872160712047773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45649232976581440474698515 68473849464872160712047773)
      ·
        refine ⟨25677693549327060267017915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68473849464872160712047773 25677693549327060267017915)
        ·
          refine ⟨38516540323990590400526873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25677693549327060267017915 38516540323990590400526873)
          ·
            refine ⟨28887405242992942800395155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38516540323990590400526873 28887405242992942800395155)
            ·
              refine ⟨43331107864489414200592733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28887405242992942800395155 43331107864489414200592733)
              ·
                refine ⟨16249165449183530325222275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43331107864489414200592733 16249165449183530325222275)
                ·
                  refine ⟨24373748173775295487833413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16249165449183530325222275 24373748173775295487833413)
                  ·
                    refine ⟨4570077782582867903968765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24373748173775295487833413 4570077782582867903968765)
                    ·
                      refine ⟨1713779168468575463988287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4570077782582867903968765 1713779168468575463988287)
                      ·
                        rfl

theorem cell23_3337573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3337573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337573 prefixEnd_3337573 := by exact prefixLift 3337573
  have htrace : WordTrace (prefixWord ++ tailWord_3337573) baseStart_3337573 baseEnd_3337573 := by
    simpa [prefixWord, tailWord_3337573, baseEnd_3337573] using wordTrace_append hprefix tailTrace_3337573
  have hstable : (prefixWord ++ tailWord_3337573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337573).length < 2 ^ (prefixWord ++ tailWord_3337573).sum := by decide
  have hdescent : baseEnd_3337573 < baseStart_3337573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337663 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_3337663 : Nat := 118140960795 + 3337663 * 2 ^ 59
def prefixEnd_3337663 : Nat := 4983230072969 + 3 ^ 40 * 3337663 * 2
def baseEnd_3337663 : Nat := 1713825381727480111862873

theorem tailTrace_3337663 : CollatzResearch.WordTrace tailWord_3337663 prefixEnd_3337663 1713825381727480111862873 := by
  unfold tailWord_3337663
  simp only [CollatzResearch.WordTrace]
  refine ⟨121734570507224453303305643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81156380338149635535537095 121734570507224453303305643)
  ·
    refine ⟨182601855760836679954958465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121734570507224453303305643 182601855760836679954958465)
    ·
      refine ⟨136951391820627509966218849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182601855760836679954958465 136951391820627509966218849)
      ·
        refine ⟨102713543865470632474664137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136951391820627509966218849 102713543865470632474664137)
        ·
          refine ⟨77035157899102974355998103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102713543865470632474664137 77035157899102974355998103)
          ·
            refine ⟨115552736848654461533997155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77035157899102974355998103 115552736848654461533997155)
            ·
              refine ⟨173329105272981692300995733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115552736848654461533997155 173329105272981692300995733)
              ·
                refine ⟨8124801809671016826609175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173329105272981692300995733 8124801809671016826609175)
                ·
                  refine ⟨12187202714506525239913763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124801809671016826609175 12187202714506525239913763)
                  ·
                    refine ⟨18280804071759787859870645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12187202714506525239913763 18280804071759787859870645)
                    ·
                      refine ⟨1713825381727480111862873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18280804071759787859870645 1713825381727480111862873)
                      ·
                        rfl

theorem cell23_3337663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_3337663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337663 prefixEnd_3337663 := by exact prefixLift 3337663
  have htrace : WordTrace (prefixWord ++ tailWord_3337663) baseStart_3337663 baseEnd_3337663 := by
    simpa [prefixWord, tailWord_3337663, baseEnd_3337663] using wordTrace_append hprefix tailTrace_3337663
  have hstable : (prefixWord ++ tailWord_3337663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337663).length < 2 ^ (prefixWord ++ tailWord_3337663).sum := by decide
  have hdescent : baseEnd_3337663 < baseStart_3337663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337690 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_3337690 : Nat := 118140960795 + 3337690 * 2 ^ 59
def prefixEnd_3337690 : Nat := 4983230072969 + 3 ^ 40 * 3337690 * 2
def baseEnd_3337690 : Nat := 1713839245705151506225249

theorem tailTrace_3337690 : CollatzResearch.WordTrace tailWord_3337690 prefixEnd_3337690 1713839245705151506225249 := by
  unfold tailWord_3337690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30433888819531659228634631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81157036852084424609692349 30433888819531659228634631)
  ·
    refine ⟨45650833229297488842951947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30433888819531659228634631 45650833229297488842951947)
    ·
      refine ⟨68476249843946233264427921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45650833229297488842951947 68476249843946233264427921)
      ·
        refine ⟨51357187382959674948320941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68476249843946233264427921 51357187382959674948320941)
        ·
          refine ⟨19258945268609878105620353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51357187382959674948320941 19258945268609878105620353)
          ·
            refine ⟨14444208951457408579215265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19258945268609878105620353 14444208951457408579215265)
            ·
              refine ⟨10833156713593056434411449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14444208951457408579215265 10833156713593056434411449)
              ·
                refine ⟨8124867535194792325808587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10833156713593056434411449 8124867535194792325808587)
                ·
                  refine ⟨12187301302792188488712881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124867535194792325808587 12187301302792188488712881)
                  ·
                    refine ⟨9140475977094141366534661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12187301302792188488712881 9140475977094141366534661)
                    ·
                      refine ⟨1713839245705151506225249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9140475977094141366534661 1713839245705151506225249)
                      ·
                        rfl

theorem cell23_3337690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_3337690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337690 prefixEnd_3337690 := by exact prefixLift 3337690
  have htrace : WordTrace (prefixWord ++ tailWord_3337690) baseStart_3337690 baseEnd_3337690 := by
    simpa [prefixWord, tailWord_3337690, baseEnd_3337690] using wordTrace_append hprefix tailTrace_3337690
  have hstable : (prefixWord ++ tailWord_3337690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337690).length < 2 ^ (prefixWord ++ tailWord_3337690).sum := by decide
  have hdescent : baseEnd_3337690 < baseStart_3337690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337697 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_3337697 : Nat := 118140960795 + 3337697 * 2 ^ 59
def prefixEnd_3337697 : Nat := 4983230072969 + 3 ^ 40 * 3337697 * 2
def baseEnd_3337697 : Nat := 1713842840069732978837717

theorem tailTrace_3337697 : CollatzResearch.WordTrace tailWord_3337697 prefixEnd_3337697 1713842840069732978837717 := by
  unfold tailWord_3337697
  simp only [CollatzResearch.WordTrace]
  refine ⟨121735810589101277110043345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81157207059400851406695563 121735810589101277110043345)
  ·
    refine ⟨91301857941825957832532509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121735810589101277110043345 91301857941825957832532509)
    ·
      refine ⟨34238196728184734187199691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91301857941825957832532509 34238196728184734187199691)
      ·
        refine ⟨51357295092277101280799537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34238196728184734187199691 51357295092277101280799537)
        ·
          refine ⟨38517971319207825960599653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51357295092277101280799537 38517971319207825960599653)
          ·
            refine ⟨7222119622351467367612435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38517971319207825960599653 7222119622351467367612435)
            ·
              refine ⟨10833179433527201051418653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222119622351467367612435 10833179433527201051418653)
              ·
                refine ⟨4062442287572700394281995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10833179433527201051418653 4062442287572700394281995)
                ·
                  refine ⟨6093663431359050591422993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062442287572700394281995 6093663431359050591422993)
                  ·
                    refine ⟨4570247573519287943567245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6093663431359050591422993 4570247573519287943567245)
                    ·
                      refine ⟨1713842840069732978837717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4570247573519287943567245 1713842840069732978837717)
                      ·
                        rfl

theorem cell23_3337697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_3337697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337697 prefixEnd_3337697 := by exact prefixLift 3337697
  have htrace : WordTrace (prefixWord ++ tailWord_3337697) baseStart_3337697 baseEnd_3337697 := by
    simpa [prefixWord, tailWord_3337697, baseEnd_3337697] using wordTrace_append hprefix tailTrace_3337697
  have hstable : (prefixWord ++ tailWord_3337697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337697).length < 2 ^ (prefixWord ++ tailWord_3337697).sum := by decide
  have hdescent : baseEnd_3337697 < baseStart_3337697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337770 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3337770 : Nat := 118140960795 + 3337770 * 2 ^ 59
def prefixEnd_3337770 : Nat := 4983230072969 + 3 ^ 40 * 3337770 * 2
def baseEnd_3337770 : Nat := 1713880324157511193224881

theorem tailTrace_3337770 : CollatzResearch.WordTrace tailWord_3337770 prefixEnd_3337770 1713880324157511193224881 := by
  unfold tailWord_3337770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30434618279459202644362691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81158982078557873718300509 30434618279459202644362691)
  ·
    refine ⟨45651927419188803966544037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30434618279459202644362691 45651927419188803966544037)
    ·
      refine ⟨8559736391097900743727007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45651927419188803966544037 8559736391097900743727007)
      ·
        refine ⟨12839604586646851115590511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8559736391097900743727007 12839604586646851115590511)
        ·
          refine ⟨19259406879970276673385767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839604586646851115590511 19259406879970276673385767)
          ·
            refine ⟨28889110319955415010078651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19259406879970276673385767 28889110319955415010078651)
            ·
              refine ⟨43333665479933122515117977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28889110319955415010078651 43333665479933122515117977)
              ·
                refine ⟨32500249109949841886338483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43333665479933122515117977 32500249109949841886338483)
                ·
                  refine ⟨48750373664924762829507725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32500249109949841886338483 48750373664924762829507725)
                  ·
                    refine ⟨18281390124346786061065397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48750373664924762829507725 18281390124346786061065397)
                    ·
                      refine ⟨1713880324157511193224881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18281390124346786061065397 1713880324157511193224881)
                      ·
                        rfl

theorem cell23_3337770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3337770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337770 prefixEnd_3337770 := by exact prefixLift 3337770
  have htrace : WordTrace (prefixWord ++ tailWord_3337770) baseStart_3337770 baseEnd_3337770 := by
    simpa [prefixWord, tailWord_3337770, baseEnd_3337770] using wordTrace_append hprefix tailTrace_3337770
  have hstable : (prefixWord ++ tailWord_3337770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337770).length < 2 ^ (prefixWord ++ tailWord_3337770).sum := by decide
  have hdescent : baseEnd_3337770 < baseStart_3337770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337788 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_3337788 : Nat := 118140960795 + 3337788 * 2 ^ 59
def prefixEnd_3337788 : Nat := 4983230072969 + 3 ^ 40 * 3337788 * 2
def baseEnd_3337788 : Nat := 1713889566809292122799799

theorem tailTrace_3337788 : CollatzResearch.WordTrace tailWord_3337788 prefixEnd_3337788 1713889566809292122799799 := by
  unfold tailWord_3337788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60869564815885799825803009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81159419754514399767737345 60869564815885799825803009)
  ·
    refine ⟨45652173611914349869352257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60869564815885799825803009 45652173611914349869352257)
    ·
      refine ⟨34239130208935762402014193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45652173611914349869352257 34239130208935762402014193)
      ·
        refine ⟨25679347656701821801510645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34239130208935762402014193 25679347656701821801510645)
        ·
          refine ⟨2407438842815795793891623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25679347656701821801510645 2407438842815795793891623)
          ·
            refine ⟨3611158264223693690837435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407438842815795793891623 3611158264223693690837435)
            ·
              refine ⟨5416737396335540536256153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611158264223693690837435 5416737396335540536256153)
              ·
                refine ⟨4062553047251655402192115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416737396335540536256153 4062553047251655402192115)
                ·
                  refine ⟨6093829570877483103288173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062553047251655402192115 6093829570877483103288173)
                  ·
                    refine ⟨2285186089079056163733065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6093829570877483103288173 2285186089079056163733065)
                    ·
                      refine ⟨1713889566809292122799799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285186089079056163733065 1713889566809292122799799)
                      ·
                        rfl

theorem cell23_3337788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_3337788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337788 prefixEnd_3337788 := by exact prefixLift 3337788
  have htrace : WordTrace (prefixWord ++ tailWord_3337788) baseStart_3337788 baseEnd_3337788 := by
    simpa [prefixWord, tailWord_3337788, baseEnd_3337788] using wordTrace_append hprefix tailTrace_3337788
  have hstable : (prefixWord ++ tailWord_3337788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337788).length < 2 ^ (prefixWord ++ tailWord_3337788).sum := by decide
  have hdescent : baseEnd_3337788 < baseStart_3337788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337800 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_3337800 : Nat := 118140960795 + 3337800 * 2 ^ 59
def prefixEnd_3337800 : Nat := 4983230072969 + 3 ^ 40 * 3337800 * 2
def baseEnd_3337800 : Nat := 1713895728577146075849743

theorem tailTrace_3337800 : CollatzResearch.WordTrace tailWord_3337800 prefixEnd_3337800 1713895728577146075849743 := by
  unfold tailWord_3337800
  simp only [CollatzResearch.WordTrace]
  refine ⟨60869783653864062850521427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81159711538485417134028569 60869783653864062850521427)
  ·
    refine ⟨91304675480796094275782141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60869783653864062850521427 91304675480796094275782141)
    ·
      refine ⟨34239253305298535353418303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91304675480796094275782141 34239253305298535353418303)
      ·
        refine ⟨51358879957947803030127455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34239253305298535353418303 51358879957947803030127455)
        ·
          refine ⟨77038319936921704545191183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51358879957947803030127455 77038319936921704545191183)
          ·
            refine ⟨115557479905382556817786775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77038319936921704545191183 115557479905382556817786775)
            ·
              refine ⟨173336219858073835226680163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115557479905382556817786775 173336219858073835226680163)
              ·
                refine ⟨260004329787110752840020245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173336219858073835226680163 260004329787110752840020245)
                ·
                  refine ⟨12187702958770816539375949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260004329787110752840020245 12187702958770816539375949)
                  ·
                    refine ⟨4570388609539056202265981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12187702958770816539375949 4570388609539056202265981)
                    ·
                      refine ⟨1713895728577146075849743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4570388609539056202265981 1713895728577146075849743)
                      ·
                        rfl

theorem cell23_3337800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_3337800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337800 prefixEnd_3337800 := by exact prefixLift 3337800
  have htrace : WordTrace (prefixWord ++ tailWord_3337800) baseStart_3337800 baseEnd_3337800 := by
    simpa [prefixWord, tailWord_3337800, baseEnd_3337800] using wordTrace_append hprefix tailTrace_3337800
  have hstable : (prefixWord ++ tailWord_3337800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337800).length < 2 ^ (prefixWord ++ tailWord_3337800).sum := by decide
  have hdescent : baseEnd_3337800 < baseStart_3337800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337827 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 5, 2]
def baseStart_3337827 : Nat := 118140960795 + 3337827 * 2 ^ 59
def prefixEnd_3337827 : Nat := 4983230072969 + 3 ^ 40 * 3337827 * 2
def baseEnd_3337827 : Nat := 1713909592554817470212119

theorem tailTrace_3337827 : CollatzResearch.WordTrace tailWord_3337827 prefixEnd_3337827 1713909592554817470212119 := by
  unfold tailWord_3337827
  simp only [CollatzResearch.WordTrace]
  refine ⟨121740552078630309312275735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81160368052420206208183823 121740552078630309312275735)
  ·
    refine ⟨182610828117945463968413603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121740552078630309312275735 182610828117945463968413603)
    ·
      refine ⟨273916242176918195952620405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182610828117945463968413603 273916242176918195952620405)
      ·
        refine ⟨25679647704086080870558163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273916242176918195952620405 25679647704086080870558163)
        ·
          refine ⟨38519471556129121305837245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25679647704086080870558163 38519471556129121305837245)
          ·
            refine ⟨14444801833548420489688967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38519471556129121305837245 14444801833548420489688967)
            ·
              refine ⟨21667202750322630734533451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14444801833548420489688967 21667202750322630734533451)
              ·
                refine ⟨32500804125483946101800177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21667202750322630734533451 32500804125483946101800177)
                ·
                  refine ⟨24375603094112959576350133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32500804125483946101800177 24375603094112959576350133)
                  ·
                    refine ⟨2285212790073089960282825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24375603094112959576350133 2285212790073089960282825)
                    ·
                      refine ⟨1713909592554817470212119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285212790073089960282825 1713909592554817470212119)
                      ·
                        rfl

theorem cell23_3337827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_3337827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337827 prefixEnd_3337827 := by exact prefixLift 3337827
  have htrace : WordTrace (prefixWord ++ tailWord_3337827) baseStart_3337827 baseEnd_3337827 := by
    simpa [prefixWord, tailWord_3337827, baseEnd_3337827] using wordTrace_append hprefix tailTrace_3337827
  have hstable : (prefixWord ++ tailWord_3337827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337827).length < 2 ^ (prefixWord ++ tailWord_3337827).sum := by decide
  have hdescent : baseEnd_3337827 < baseStart_3337827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337857 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3337857 : Nat := 118140960795 + 3337857 * 2 ^ 59
def prefixEnd_3337857 : Nat := 4983230072969 + 3 ^ 40 * 3337857 * 2
def baseEnd_3337857 : Nat := 1713924996974452352836981

theorem tailTrace_3337857 : CollatzResearch.WordTrace tailWord_3337857 prefixEnd_3337857 1713924996974452352836981 := by
  unfold tailWord_3337857
  simp only [CollatzResearch.WordTrace]
  refine ⟨121741646268521624435867825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81161097512347749623911883 121741646268521624435867825)
  ·
    refine ⟨91306234701391218326900869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121741646268521624435867825 91306234701391218326900869)
    ·
      refine ⟨17119919006510853436293913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91306234701391218326900869 17119919006510853436293913)
      ·
        refine ⟨12839939254883140077220435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17119919006510853436293913 12839939254883140077220435)
        ·
          refine ⟨19259908882324710115830653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839939254883140077220435 19259908882324710115830653)
          ·
            refine ⟨7222465830871766293436495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19259908882324710115830653 7222465830871766293436495)
            ·
              refine ⟨10833698746307649440154743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222465830871766293436495 10833698746307649440154743)
              ·
                refine ⟨16250548119461474160232115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10833698746307649440154743 16250548119461474160232115)
                ·
                  refine ⟨24375822179192211240348173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16250548119461474160232115 24375822179192211240348173)
                  ·
                    refine ⟨9140933317197079215130565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24375822179192211240348173 9140933317197079215130565)
                    ·
                      refine ⟨1713924996974452352836981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9140933317197079215130565 1713924996974452352836981)
                      ·
                        rfl

theorem cell23_3337857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3337857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337857 prefixEnd_3337857 := by exact prefixLift 3337857
  have htrace : WordTrace (prefixWord ++ tailWord_3337857) baseStart_3337857 baseEnd_3337857 := by
    simpa [prefixWord, tailWord_3337857, baseEnd_3337857] using wordTrace_append hprefix tailTrace_3337857
  have hstable : (prefixWord ++ tailWord_3337857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337857).length < 2 ^ (prefixWord ++ tailWord_3337857).sum := by decide
  have hdescent : baseEnd_3337857 < baseStart_3337857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337877 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 3]
def baseStart_3337877 : Nat := 118140960795 + 3337877 * 2 ^ 59
def prefixEnd_3337877 : Nat := 4983230072969 + 3 ^ 40 * 3337877 * 2
def baseEnd_3337877 : Nat := 1713935266587542274586889

theorem tailTrace_3337877 : CollatzResearch.WordTrace tailWord_3337877 prefixEnd_3337877 1713935266587542274586889 := by
  unfold tailWord_3337877
  simp only [CollatzResearch.WordTrace]
  refine ⟨121742375728449167851595885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81161583818966111901063923 121742375728449167851595885)
  ·
    refine ⟨45653390898168437944348457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121742375728449167851595885 45653390898168437944348457)
    ·
      refine ⟨34240043173626328458261343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45653390898168437944348457 34240043173626328458261343)
      ·
        refine ⟨51360064760439492687392015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34240043173626328458261343 51360064760439492687392015)
        ·
          refine ⟨77040097140659239031088023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51360064760439492687392015 77040097140659239031088023)
          ·
            refine ⟨115560145710988858546632035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77040097140659239031088023 115560145710988858546632035)
            ·
              refine ⟨173340218566483287819948053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115560145710988858546632035 173340218566483287819948053)
              ·
                refine ⟨8125322745303904116560065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173340218566483287819948053 8125322745303904116560065)
                ·
                  refine ⟨6093992058977928087420049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8125322745303904116560065 6093992058977928087420049)
                  ·
                    refine ⟨4570494044233446065565037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6093992058977928087420049 4570494044233446065565037)
                    ·
                      refine ⟨1713935266587542274586889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4570494044233446065565037 1713935266587542274586889)
                      ·
                        rfl

theorem cell23_3337877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_3337877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337877 prefixEnd_3337877 := by exact prefixLift 3337877
  have htrace : WordTrace (prefixWord ++ tailWord_3337877) baseStart_3337877 baseEnd_3337877 := by
    simpa [prefixWord, tailWord_3337877, baseEnd_3337877] using wordTrace_append hprefix tailTrace_3337877
  have hstable : (prefixWord ++ tailWord_3337877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337877).length < 2 ^ (prefixWord ++ tailWord_3337877).sum := by decide
  have hdescent : baseEnd_3337877 < baseStart_3337877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337918 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3337918 : Nat := 118140960795 + 3337918 * 2 ^ 59
def prefixEnd_3337918 : Nat := 4983230072969 + 3 ^ 40 * 3337918 * 2
def baseEnd_3337918 : Nat := 571318773098125538058067

theorem tailTrace_3337918 : CollatzResearch.WordTrace tailWord_3337918 prefixEnd_3337918 571318773098125538058067 := by
  unfold tailWord_3337918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15217983890162578981729801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81162580747533754569225605 15217983890162578981729801)
  ·
    refine ⟨11413487917621934236297351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15217983890162578981729801 11413487917621934236297351)
    ·
      refine ⟨17120231876432901354446027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413487917621934236297351 17120231876432901354446027)
      ·
        refine ⟨25680347814649352031669041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120231876432901354446027 25680347814649352031669041)
        ·
          refine ⟨19260260860987014023751781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25680347814649352031669041 19260260860987014023751781)
          ·
            refine ⟨3611298911435065129453459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19260260860987014023751781 3611298911435065129453459)
            ·
              refine ⟨5416948367152597694180189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611298911435065129453459 5416948367152597694180189)
              ·
                refine ⟨2031355637682224135317571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5416948367152597694180189 2031355637682224135317571)
                ·
                  refine ⟨3047033456523336202976357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031355637682224135317571 3047033456523336202976357)
                  ·
                    refine ⟨571318773098125538058067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3047033456523336202976357 571318773098125538058067)
                    ·
                      rfl

theorem cell23_3337918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3337918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337918 prefixEnd_3337918 := by exact prefixLift 3337918
  have htrace : WordTrace (prefixWord ++ tailWord_3337918) baseStart_3337918 baseEnd_3337918 := by
    simpa [prefixWord, tailWord_3337918, baseEnd_3337918] using wordTrace_append hprefix tailTrace_3337918
  have hstable : (prefixWord ++ tailWord_3337918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337918).length < 2 ^ (prefixWord ++ tailWord_3337918).sum := by decide
  have hdescent : baseEnd_3337918 < baseStart_3337918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337927 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3337927 : Nat := 118140960795 + 3337927 * 2 ^ 59
def prefixEnd_3337927 : Nat := 4983230072969 + 3 ^ 40 * 3337927 * 2
def baseEnd_3337927 : Nat := 571320313540089026320553

theorem tailTrace_3337927 : CollatzResearch.WordTrace tailWord_3337927 prefixEnd_3337927 571320313540089026320553 := by
  unfold tailWord_3337927
  simp only [CollatzResearch.WordTrace]
  refine ⟨121744199378268026390916035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81162799585512017593944023 121744199378268026390916035)
  ·
    refine ⟨182616299067402039586374053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121744199378268026390916035 182616299067402039586374053)
    ·
      refine ⟨34240556075137882422445135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182616299067402039586374053 34240556075137882422445135)
      ·
        refine ⟨51360834112706823633667703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34240556075137882422445135 51360834112706823633667703)
        ·
          refine ⟨77041251169060235450501555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51360834112706823633667703 77041251169060235450501555)
          ·
            refine ⟨115561876753590353175752333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77041251169060235450501555 115561876753590353175752333)
            ·
              refine ⟨43335703782596382440907125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115561876753590353175752333 43335703782596382440907125)
              ·
                refine ⟨4062722229618410853835043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43335703782596382440907125 4062722229618410853835043)
                ·
                  refine ⟨6094083344427616280752565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062722229618410853835043 6094083344427616280752565)
                  ·
                    refine ⟨571320313540089026320553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6094083344427616280752565 571320313540089026320553)
                    ·
                      rfl

theorem cell23_3337927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3337927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337927 prefixEnd_3337927 := by exact prefixLift 3337927
  have htrace : WordTrace (prefixWord ++ tailWord_3337927) baseStart_3337927 baseEnd_3337927 := by
    simpa [prefixWord, tailWord_3337927, baseEnd_3337927] using wordTrace_append hprefix tailTrace_3337927
  have hstable : (prefixWord ++ tailWord_3337927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337927).length < 2 ^ (prefixWord ++ tailWord_3337927).sum := by decide
  have hdescent : baseEnd_3337927 < baseStart_3337927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337948 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 6]
def baseStart_3337948 : Nat := 118140960795 + 3337948 * 2 ^ 59
def prefixEnd_3337948 : Nat := 4983230072969 + 3 ^ 40 * 3337948 * 2
def baseEnd_3337948 : Nat := 190441302634890166311007

theorem tailTrace_3337948 : CollatzResearch.WordTrace tailWord_3337948 prefixEnd_3337948 190441302634890166311007 := by
  unfold tailWord_3337948
  simp only [CollatzResearch.WordTrace]
  refine ⟨60872482655595973488715249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81163310207461297984953665 60872482655595973488715249)
  ·
    refine ⟨45654361991696980116536437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60872482655595973488715249 45654361991696980116536437)
    ·
      refine ⟨4280096436721591885925291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45654361991696980116536437 4280096436721591885925291)
      ·
        refine ⟨6420144655082387828887937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280096436721591885925291 6420144655082387828887937)
        ·
          refine ⟨4815108491311790871665953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6420144655082387828887937 4815108491311790871665953)
          ·
            refine ⟨3611331368483843153749465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4815108491311790871665953 3611331368483843153749465)
            ·
              refine ⟨2708498526362882365312099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611331368483843153749465 2708498526362882365312099)
              ·
                refine ⟨4062747789544323547968149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708498526362882365312099 4062747789544323547968149)
                ·
                  refine ⟨190441302634890166311007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4062747789544323547968149 190441302634890166311007)
                  ·
                    rfl

theorem cell23_3337948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_3337948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337948 prefixEnd_3337948 := by exact prefixLift 3337948
  have htrace : WordTrace (prefixWord ++ tailWord_3337948) baseStart_3337948 baseEnd_3337948 := by
    simpa [prefixWord, tailWord_3337948, baseEnd_3337948] using wordTrace_append hprefix tailTrace_3337948
  have hstable : (prefixWord ++ tailWord_3337948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337948).length < 2 ^ (prefixWord ++ tailWord_3337948).sum := by decide
  have hdescent : baseEnd_3337948 < baseStart_3337948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337957 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_3337957 : Nat := 118140960795 + 3337957 * 2 ^ 59
def prefixEnd_3337957 : Nat := 4983230072969 + 3 ^ 40 * 3337957 * 2
def baseEnd_3337957 : Nat := 571325448346633987195507

theorem tailTrace_3337957 : CollatzResearch.WordTrace tailWord_3337957 prefixEnd_3337957 571325448346633987195507 := by
  unfold tailWord_3337957
  simp only [CollatzResearch.WordTrace]
  refine ⟨121745293568159341514508125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81163529045439561009672083 121745293568159341514508125)
  ·
    refine ⟨45654485088059753067940547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121745293568159341514508125 45654485088059753067940547)
    ·
      refine ⟨68481727632089629601910821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45654485088059753067940547 68481727632089629601910821)
      ·
        refine ⟨12840323931016805550358279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68481727632089629601910821 12840323931016805550358279)
        ·
          refine ⟨19260485896525208325537419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12840323931016805550358279 19260485896525208325537419)
          ·
            refine ⟨28890728844787812488306129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19260485896525208325537419 28890728844787812488306129)
            ·
              refine ⟨21668046633590859366229597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28890728844787812488306129 21668046633590859366229597)
              ·
                refine ⟨8125517487596572262336099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21668046633590859366229597 8125517487596572262336099)
                ·
                  refine ⟨12188276231394858393504149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125517487596572262336099 12188276231394858393504149)
                  ·
                    refine ⟨571325448346633987195507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12188276231394858393504149 571325448346633987195507)
                    ·
                      rfl

theorem cell23_3337957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_3337957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337957 prefixEnd_3337957 := by exact prefixLift 3337957
  have htrace : WordTrace (prefixWord ++ tailWord_3337957) baseStart_3337957 baseEnd_3337957 := by
    simpa [prefixWord, tailWord_3337957, baseEnd_3337957] using wordTrace_append hprefix tailTrace_3337957
  have hstable : (prefixWord ++ tailWord_3337957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337957).length < 2 ^ (prefixWord ++ tailWord_3337957).sum := by decide
  have hdescent : baseEnd_3337957 < baseStart_3337957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337964 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 4]
def baseStart_3337964 : Nat := 118140960795 + 3337964 * 2 ^ 59
def prefixEnd_3337964 : Nat := 4983230072969 + 3 ^ 40 * 3337964 * 2
def baseEnd_3337964 : Nat := 1713979939404483434198989

theorem tailTrace_3337964 : CollatzResearch.WordTrace tailWord_3337964 prefixEnd_3337964 1713979939404483434198989 := by
  unfold tailWord_3337964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60872774439566990855006473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81163699252755987806675297 60872774439566990855006473)
  ·
    refine ⟨45654580829675243141254855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60872774439566990855006473 45654580829675243141254855)
    ·
      refine ⟨68481871244512864711882283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45654580829675243141254855 68481871244512864711882283)
      ·
        refine ⟨102722806866769297067823425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68481871244512864711882283 102722806866769297067823425)
        ·
          refine ⟨77042105150076972800867569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102722806866769297067823425 77042105150076972800867569)
          ·
            refine ⟨57781578862557729600650677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77042105150076972800867569 57781578862557729600650677)
            ·
              refine ⟨5417023018364787150061001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57781578862557729600650677 5417023018364787150061001)
              ·
                refine ⟨4062767263773590362545751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417023018364787150061001 4062767263773590362545751)
                ·
                  refine ⟨6094150895660385543818627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062767263773590362545751 6094150895660385543818627)
                  ·
                    refine ⟨9141226343490578315727941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094150895660385543818627 9141226343490578315727941)
                    ·
                      refine ⟨1713979939404483434198989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9141226343490578315727941 1713979939404483434198989)
                      ·
                        rfl

theorem cell23_3337964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_3337964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337964 prefixEnd_3337964 := by exact prefixLift 3337964
  have htrace : WordTrace (prefixWord ++ tailWord_3337964) baseStart_3337964 baseEnd_3337964 := by
    simpa [prefixWord, tailWord_3337964, baseEnd_3337964] using wordTrace_append hprefix tailTrace_3337964
  have hstable : (prefixWord ++ tailWord_3337964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337964).length < 2 ^ (prefixWord ++ tailWord_3337964).sum := by decide
  have hdescent : baseEnd_3337964 < baseStart_3337964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3337974 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_3337974 : Nat := 118140960795 + 3337974 * 2 ^ 59
def prefixEnd_3337974 : Nat := 4983230072969 + 3 ^ 40 * 3337974 * 2
def baseEnd_3337974 : Nat := 571328358070342798357981

theorem tailTrace_3337974 : CollatzResearch.WordTrace tailWord_3337974 prefixEnd_3337974 571328358070342798357981 := by
  unfold tailWord_3337974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609119600568609588617311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81163942406065168945251317 7609119600568609588617311)
  ·
    refine ⟨11413679400852914382925967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609119600568609588617311 11413679400852914382925967)
    ·
      refine ⟨17120519101279371574388951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11413679400852914382925967 17120519101279371574388951)
      ·
        refine ⟨25680778651919057361583427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17120519101279371574388951 25680778651919057361583427)
        ·
          refine ⟨38521167977878586042375141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25680778651919057361583427 38521167977878586042375141)
          ·
            refine ⟨7222718995852234882945339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38521167977878586042375141 7222718995852234882945339)
            ·
              refine ⟨10834078493778352324418009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222718995852234882945339 10834078493778352324418009)
              ·
                refine ⟨8125558870333764243313507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10834078493778352324418009 8125558870333764243313507)
                ·
                  refine ⟨12188338305500646364970261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8125558870333764243313507 12188338305500646364970261)
                  ·
                    refine ⟨571328358070342798357981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12188338305500646364970261 571328358070342798357981)
                    ·
                      rfl

theorem cell23_3337974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_3337974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3337974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3337974 prefixEnd_3337974 := by exact prefixLift 3337974
  have htrace : WordTrace (prefixWord ++ tailWord_3337974) baseStart_3337974 baseEnd_3337974 := by
    simpa [prefixWord, tailWord_3337974, baseEnd_3337974] using wordTrace_append hprefix tailTrace_3337974
  have hstable : (prefixWord ++ tailWord_3337974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3337974).length < 2 ^ (prefixWord ++ tailWord_3337974).sum := by decide
  have hdescent : baseEnd_3337974 < baseStart_3337974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3337974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338035 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 1, 2, 3]
def baseStart_3338035 : Nat := 118140960795 + 3338035 * 2 ^ 59
def prefixEnd_3338035 : Nat := 4983230072969 + 3 ^ 40 * 3338035 * 2
def baseEnd_3338035 : Nat := 1714016396530952656411163

theorem tailTrace_3338035 : CollatzResearch.WordTrace tailWord_3338035 prefixEnd_3338035 1714016396530952656411163 := by
  unfold tailWord_3338035
  simp only [CollatzResearch.WordTrace]
  refine ⟨121748138461876760835847559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81165425641251173890565039 121748138461876760835847559)
  ·
    refine ⟨182622207692815141253771339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121748138461876760835847559 182622207692815141253771339)
    ·
      refine ⟨273933311539222711880657009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182622207692815141253771339 273933311539222711880657009)
      ·
        refine ⟨205449983654417033910492757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273933311539222711880657009 205449983654417033910492757)
        ·
          refine ⟨2407616995950199616138587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 205449983654417033910492757 2407616995950199616138587)
          ·
            refine ⟨3611425493925299424207881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407616995950199616138587 3611425493925299424207881)
            ·
              refine ⟨2708569120443974568155911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611425493925299424207881 2708569120443974568155911)
              ·
                refine ⟨4062853680665961852233867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708569120443974568155911 4062853680665961852233867)
                ·
                  refine ⟨6094280520998942778350801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062853680665961852233867 6094280520998942778350801)
                  ·
                    refine ⟨4570710390749207083763101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094280520998942778350801 4570710390749207083763101)
                    ·
                      refine ⟨1714016396530952656411163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4570710390749207083763101 1714016396530952656411163)
                      ·
                        rfl

theorem cell23_3338035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 2, 3].length) (baseStart_3338035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338035 prefixEnd_3338035 := by exact prefixLift 3338035
  have htrace : WordTrace (prefixWord ++ tailWord_3338035) baseStart_3338035 baseEnd_3338035 := by
    simpa [prefixWord, tailWord_3338035, baseEnd_3338035] using wordTrace_append hprefix tailTrace_3338035
  have hstable : (prefixWord ++ tailWord_3338035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338035).length < 2 ^ (prefixWord ++ tailWord_3338035).sum := by decide
  have hdescent : baseEnd_3338035 < baseStart_3338035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338137 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_3338137 : Nat := 118140960795 + 3338137 * 2 ^ 59
def prefixEnd_3338137 : Nat := 4983230072969 + 3 ^ 40 * 3338137 * 2
def baseEnd_3338137 : Nat := 571356257185903752445231

theorem tailTrace_3338137 : CollatzResearch.WordTrace tailWord_3338137 prefixEnd_3338137 571356257185903752445231 := by
  unfold tailWord_3338137
  simp only [CollatzResearch.WordTrace]
  refine ⟨121751858707507232256060665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81167905805004821504040443 121751858707507232256060665)
  ·
    refine ⟨91313894030630424192045499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121751858707507232256060665 91313894030630424192045499)
    ·
      refine ⟨136970841045945636288068249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91313894030630424192045499 136970841045945636288068249)
      ·
        refine ⟨102728130784459227216051187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136970841045945636288068249 102728130784459227216051187)
        ·
          refine ⟨154092196176688840824076781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102728130784459227216051187 154092196176688840824076781)
          ·
            refine ⟨57784573566258315309028793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154092196176688840824076781 57784573566258315309028793)
            ·
              refine ⟨43338430174693736481771595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57784573566258315309028793 43338430174693736481771595)
              ·
                refine ⟨65007645262040604722657393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43338430174693736481771595 65007645262040604722657393)
                ·
                  refine ⟨48755733946530453541993045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65007645262040604722657393 48755733946530453541993045)
                  ·
                    refine ⟨571356257185903752445231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48755733946530453541993045 571356257185903752445231)
                    ·
                      rfl

theorem cell23_3338137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_3338137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338137 prefixEnd_3338137 := by exact prefixLift 3338137
  have htrace : WordTrace (prefixWord ++ tailWord_3338137) baseStart_3338137 baseEnd_3338137 := by
    simpa [prefixWord, tailWord_3338137, baseEnd_3338137] using wordTrace_append hprefix tailTrace_3338137
  have hstable : (prefixWord ++ tailWord_3338137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338137).length < 2 ^ (prefixWord ++ tailWord_3338137).sum := by decide
  have hdescent : baseEnd_3338137 < baseStart_3338137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338141 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_3338141 : Nat := 118140960795 + 3338141 * 2 ^ 59
def prefixEnd_3338141 : Nat := 4983230072969 + 3 ^ 40 * 3338141 * 2
def baseEnd_3338141 : Nat := 571356941826776413895225

theorem tailTrace_3338141 : CollatzResearch.WordTrace tailWord_3338141 prefixEnd_3338141 571356941826776413895225 := by
  unfold tailWord_3338141
  simp only [CollatzResearch.WordTrace]
  refine ⟨121752004599492740939206277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81168003066328493959470851 121752004599492740939206277)
  ·
    refine ⟨22828500862404888926101177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121752004599492740939206277 22828500862404888926101177)
    ·
      refine ⟨17121375646803666694575883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22828500862404888926101177 17121375646803666694575883)
      ·
        refine ⟨25682063470205500041863825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17121375646803666694575883 25682063470205500041863825)
        ·
          refine ⟨19261547602654125031397869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25682063470205500041863825 19261547602654125031397869)
          ·
            refine ⟨7223080350995296886774201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19261547602654125031397869 7223080350995296886774201)
            ·
              refine ⟨5417310263246472665080651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223080350995296886774201 5417310263246472665080651)
              ·
                refine ⟨8125965394869708997620977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417310263246472665080651 8125965394869708997620977)
                ·
                  refine ⟨6094474046152281748215733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8125965394869708997620977 6094474046152281748215733)
                  ·
                    refine ⟨571356941826776413895225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6094474046152281748215733 571356941826776413895225)
                    ·
                      rfl

theorem cell23_3338141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_3338141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338141 prefixEnd_3338141 := by exact prefixLift 3338141
  have htrace : WordTrace (prefixWord ++ tailWord_3338141) baseStart_3338141 baseEnd_3338141 := by
    simpa [prefixWord, tailWord_3338141, baseEnd_3338141] using wordTrace_append hprefix tailTrace_3338141
  have hstable : (prefixWord ++ tailWord_3338141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338141).length < 2 ^ (prefixWord ++ tailWord_3338141).sum := by decide
  have hdescent : baseEnd_3338141 < baseStart_3338141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338161 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3338161 : Nat := 118140960795 + 3338161 * 2 ^ 59
def prefixEnd_3338161 : Nat := 4983230072969 + 3 ^ 40 * 3338161 * 2
def baseEnd_3338161 : Nat := 1714081095093419163435583

theorem tailTrace_3338161 : CollatzResearch.WordTrace tailWord_3338161 prefixEnd_3338161 1714081095093419163435583 := by
  unfold tailWord_3338161
  simp only [CollatzResearch.WordTrace]
  refine ⟨121752734059420284354934337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81168489372946856236622891 121752734059420284354934337)
  ·
    refine ⟨91314550544565213266200753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121752734059420284354934337 91314550544565213266200753)
    ·
      refine ⟨68485912908423909949650565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91314550544565213266200753 68485912908423909949650565)
      ·
        refine ⟨12841108670329483115559481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68485912908423909949650565 12841108670329483115559481)
        ·
          refine ⟨9630831502747112336669611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12841108670329483115559481 9630831502747112336669611)
          ·
            refine ⟨14446247254120668505004417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9630831502747112336669611 14446247254120668505004417)
            ·
              refine ⟨10834685440590501378753313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14446247254120668505004417 10834685440590501378753313)
              ·
                refine ⟨8126014080442876034064985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10834685440590501378753313 8126014080442876034064985)
                ·
                  refine ⟨6094510560332157025548739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8126014080442876034064985 6094510560332157025548739)
                  ·
                    refine ⟨9141765840498235538323109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094510560332157025548739 9141765840498235538323109)
                    ·
                      refine ⟨1714081095093419163435583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9141765840498235538323109 1714081095093419163435583)
                      ·
                        rfl

theorem cell23_3338161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3338161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338161 prefixEnd_3338161 := by exact prefixLift 3338161
  have htrace : WordTrace (prefixWord ++ tailWord_3338161) baseStart_3338161 baseEnd_3338161 := by
    simpa [prefixWord, tailWord_3338161, baseEnd_3338161] using wordTrace_append hprefix tailTrace_3338161
  have hstable : (prefixWord ++ tailWord_3338161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338161).length < 2 ^ (prefixWord ++ tailWord_3338161).sum := by decide
  have hdescent : baseEnd_3338161 < baseStart_3338161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338251 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 2, 6, 2]
def baseStart_3338251 : Nat := 118140960795 + 3338251 * 2 ^ 59
def prefixEnd_3338251 : Nat := 4983230072969 + 3 ^ 40 * 3338251 * 2
def baseEnd_3338251 : Nat := 1714127308352323811310169

theorem tailTrace_3338251 : CollatzResearch.WordTrace tailWord_3338251 prefixEnd_3338251 1714127308352323811310169 := by
  unfold tailWord_3338251
  simp only [CollatzResearch.WordTrace]
  refine ⟨121756016629094229725710607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81170677752729486483807071 121756016629094229725710607)
  ·
    refine ⟨182634024943641344588565911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121756016629094229725710607 182634024943641344588565911)
    ·
      refine ⟨273951037415462016882848867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182634024943641344588565911 273951037415462016882848867)
      ·
        refine ⟨410926556123193025324273301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273951037415462016882848867 410926556123193025324273301)
        ·
          refine ⟨19262182318274673062075311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 410926556123193025324273301 19262182318274673062075311)
          ·
            refine ⟨28893273477412009593112967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19262182318274673062075311 28893273477412009593112967)
            ·
              refine ⟨43339910216118014389669451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28893273477412009593112967 43339910216118014389669451)
              ·
                refine ⟨65009865324177021584504177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43339910216118014389669451 65009865324177021584504177)
                ·
                  refine ⟨48757398993132766188378133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65009865324177021584504177 48757398993132766188378133)
                  ·
                    refine ⟨2285503077803098415080225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48757398993132766188378133 2285503077803098415080225)
                    ·
                      refine ⟨1714127308352323811310169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285503077803098415080225 1714127308352323811310169)
                      ·
                        rfl

theorem cell23_3338251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 6, 2].length) (baseStart_3338251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338251 prefixEnd_3338251 := by exact prefixLift 3338251
  have htrace : WordTrace (prefixWord ++ tailWord_3338251) baseStart_3338251 baseEnd_3338251 := by
    simpa [prefixWord, tailWord_3338251, baseEnd_3338251] using wordTrace_append hprefix tailTrace_3338251
  have hstable : (prefixWord ++ tailWord_3338251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338251).length < 2 ^ (prefixWord ++ tailWord_3338251).sum := by decide
  have hdescent : baseEnd_3338251 < baseStart_3338251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338268 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_3338268 : Nat := 118140960795 + 3338268 * 2 ^ 59
def prefixEnd_3338268 : Nat := 4983230072969 + 3 ^ 40 * 3338268 * 2
def baseEnd_3338268 : Nat := 1714136037523450244797591

theorem tailTrace_3338268 : CollatzResearch.WordTrace tailWord_3338268 prefixEnd_3338268 1714136037523450244797591 := by
  unfold tailWord_3338268
  simp only [CollatzResearch.WordTrace]
  refine ⟨60878318335016320814539729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81171091113355094419386305 60878318335016320814539729)
  ·
    refine ⟨45658738751262240610904797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60878318335016320814539729 45658738751262240610904797)
    ·
      refine ⟨17122027031723340229089299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45658738751262240610904797 17122027031723340229089299)
      ·
        refine ⟨25683040547585010343633949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17122027031723340229089299 25683040547585010343633949)
        ·
          refine ⟨9631140205344378878862731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25683040547585010343633949 9631140205344378878862731)
          ·
            refine ⟨14446710308016568318294097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631140205344378878862731 14446710308016568318294097)
            ·
              refine ⟨10835032731012426238720573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14446710308016568318294097 10835032731012426238720573)
              ·
                refine ⟨4063137274129659839520215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10835032731012426238720573 4063137274129659839520215)
                ·
                  refine ⟨6094705911194489759280323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063137274129659839520215 6094705911194489759280323)
                  ·
                    refine ⟨9142058866791734638920485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094705911194489759280323 9142058866791734638920485)
                    ·
                      refine ⟨1714136037523450244797591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9142058866791734638920485 1714136037523450244797591)
                      ·
                        rfl

theorem cell23_3338268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_3338268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338268 prefixEnd_3338268 := by exact prefixLift 3338268
  have htrace : WordTrace (prefixWord ++ tailWord_3338268) baseStart_3338268 baseEnd_3338268 := by
    simpa [prefixWord, tailWord_3338268, baseEnd_3338268] using wordTrace_append hprefix tailTrace_3338268
  have hstable : (prefixWord ++ tailWord_3338268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338268).length < 2 ^ (prefixWord ++ tailWord_3338268).sum := by decide
  have hdescent : baseEnd_3338268 < baseStart_3338268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338271 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_3338271 : Nat := 118140960795 + 3338271 * 2 ^ 59
def prefixEnd_3338271 : Nat := 4983230072969 + 3 ^ 40 * 3338271 * 2
def baseEnd_3338271 : Nat := 1714137577965413733060077

theorem tailTrace_3338271 : CollatzResearch.WordTrace tailWord_3338271 prefixEnd_3338271 1714137577965413733060077 := by
  unfold tailWord_3338271
  simp only [CollatzResearch.WordTrace]
  refine ⟨121756746089021773141438667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81171164059347848760959111 121756746089021773141438667)
  ·
    refine ⟨182635119133532659712158001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121756746089021773141438667 182635119133532659712158001)
    ·
      refine ⟨136976339350149494784118501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182635119133532659712158001 136976339350149494784118501)
      ·
        refine ⟨25683063628153030272022219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136976339350149494784118501 25683063628153030272022219)
        ·
          refine ⟨38524595442229545408033329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25683063628153030272022219 38524595442229545408033329)
          ·
            refine ⟨28893446581672159056024997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38524595442229545408033329 28893446581672159056024997)
            ·
              refine ⟨5417521234063529823004687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28893446581672159056024997 5417521234063529823004687)
              ·
                refine ⟨8126281851095294734507031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417521234063529823004687 8126281851095294734507031)
                ·
                  refine ⟨12189422776642942101760547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8126281851095294734507031 12189422776642942101760547)
                  ·
                    refine ⟨18284134164964413152640821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12189422776642942101760547 18284134164964413152640821)
                    ·
                      refine ⟨1714137577965413733060077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18284134164964413152640821 1714137577965413733060077)
                      ·
                        rfl

theorem cell23_3338271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_3338271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338271 prefixEnd_3338271 := by exact prefixLift 3338271
  have htrace : WordTrace (prefixWord ++ tailWord_3338271) baseStart_3338271 baseEnd_3338271 := by
    simpa [prefixWord, tailWord_3338271, baseEnd_3338271] using wordTrace_append hprefix tailTrace_3338271
  have hstable : (prefixWord ++ tailWord_3338271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338271).length < 2 ^ (prefixWord ++ tailWord_3338271).sum := by decide
  have hdescent : baseEnd_3338271 < baseStart_3338271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338279 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3338279 : Nat := 118140960795 + 3338279 * 2 ^ 59
def prefixEnd_3338279 : Nat := 4983230072969 + 3 ^ 40 * 3338279 * 2
def baseEnd_3338279 : Nat := 1714141685810649701760041

theorem tailTrace_3338279 : CollatzResearch.WordTrace tailWord_3338279 prefixEnd_3338279 1714141685810649701760041 := by
  unfold tailWord_3338279
  simp only [CollatzResearch.WordTrace]
  refine ⟨121757037872992790507729891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81171358581995193671819927 121757037872992790507729891)
  ·
    refine ⟨182635556809489185761594837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121757037872992790507729891 182635556809489185761594837)
    ·
      refine ⟨4280520862722402791287379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 182635556809489185761594837 4280520862722402791287379)
      ·
        refine ⟨6420781294083604186931069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280520862722402791287379 6420781294083604186931069)
        ·
          refine ⟨2407792985281351570099151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6420781294083604186931069 2407792985281351570099151)
          ·
            refine ⟨3611689477922027355148727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407792985281351570099151 3611689477922027355148727)
            ·
              refine ⟨5417534216883041032723091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611689477922027355148727 5417534216883041032723091)
              ·
                refine ⟨8126301325324561549084637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417534216883041032723091 8126301325324561549084637)
                ·
                  refine ⟨3047362996996710580906739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8126301325324561549084637 3047362996996710580906739)
                  ·
                    refine ⟨4571044495495065871360109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047362996996710580906739 4571044495495065871360109)
                    ·
                      refine ⟨1714141685810649701760041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571044495495065871360109 1714141685810649701760041)
                      ·
                        rfl

theorem cell23_3338279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3338279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338279 prefixEnd_3338279 := by exact prefixLift 3338279
  have htrace : WordTrace (prefixWord ++ tailWord_3338279) baseStart_3338279 baseEnd_3338279 := by
    simpa [prefixWord, tailWord_3338279, baseEnd_3338279] using wordTrace_append hprefix tailTrace_3338279
  have hstable : (prefixWord ++ tailWord_3338279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338279).length < 2 ^ (prefixWord ++ tailWord_3338279).sum := by decide
  have hdescent : baseEnd_3338279 < baseStart_3338279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338302 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3338302 : Nat := 118140960795 + 3338302 * 2 ^ 59
def prefixEnd_3338302 : Nat := 4983230072969 + 3 ^ 40 * 3338302 * 2
def baseEnd_3338302 : Nat := 1714153495865703111772435

theorem tailTrace_3338302 : CollatzResearch.WordTrace tailWord_3338302 prefixEnd_3338302 1714153495865703111772435 := by
  unfold tailWord_3338302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219734593988683179477145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81171917834606310290544773 15219734593988683179477145)
  ·
    refine ⟨11414800945491512384607859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15219734593988683179477145 11414800945491512384607859)
    ·
      refine ⟨17122201418237268576911789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11414800945491512384607859 17122201418237268576911789)
      ·
        refine ⟨6420825531838975716341921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17122201418237268576911789 6420825531838975716341921)
        ·
          refine ⟨4815619148879231787256441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6420825531838975716341921 4815619148879231787256441)
          ·
            refine ⟨3611714361659423840442331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4815619148879231787256441 3611714361659423840442331)
            ·
              refine ⟨5417571542489135760663497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611714361659423840442331 5417571542489135760663497)
              ·
                refine ⟨4063178656866851820497623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417571542489135760663497 4063178656866851820497623)
                ·
                  refine ⟨6094767985300277730746435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063178656866851820497623 6094767985300277730746435)
                  ·
                    refine ⟨9142151977950416596119653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094767985300277730746435 9142151977950416596119653)
                    ·
                      refine ⟨1714153495865703111772435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9142151977950416596119653 1714153495865703111772435)
                      ·
                        rfl

theorem cell23_3338302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3338302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338302 prefixEnd_3338302 := by exact prefixLift 3338302
  have htrace : WordTrace (prefixWord ++ tailWord_3338302) baseStart_3338302 baseEnd_3338302 := by
    simpa [prefixWord, tailWord_3338302, baseEnd_3338302] using wordTrace_append hprefix tailTrace_3338302
  have hstable : (prefixWord ++ tailWord_3338302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338302).length < 2 ^ (prefixWord ++ tailWord_3338302).sum := by decide
  have hdescent : baseEnd_3338302 < baseStart_3338302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338305 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3338305 : Nat := 118140960795 + 3338305 * 2 ^ 59
def prefixEnd_3338305 : Nat := 4983230072969 + 3 ^ 40 * 3338305 * 2
def baseEnd_3338305 : Nat := 1714155036307666600034921

theorem tailTrace_3338305 : CollatzResearch.WordTrace tailWord_3338305 prefixEnd_3338305 1714155036307666600034921 := by
  unfold tailWord_3338305
  simp only [CollatzResearch.WordTrace]
  refine ⟨121757986170898596948176369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81171990780599064632117579 121757986170898596948176369)
  ·
    refine ⟨91318489628173947711132277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121757986170898596948176369 91318489628173947711132277)
    ·
      refine ⟨8561108402641307597918651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91318489628173947711132277 8561108402641307597918651)
      ·
        refine ⟨12841662603961961396877977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8561108402641307597918651 12841662603961961396877977)
        ·
          refine ⟨9631246952971471047658483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12841662603961961396877977 9631246952971471047658483)
          ·
            refine ⟨14446870429457206571487725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631246952971471047658483 14446870429457206571487725)
            ·
              refine ⟨5417576411046452464307897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14446870429457206571487725 5417576411046452464307897)
              ·
                refine ⟨4063182308284839348230923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5417576411046452464307897 4063182308284839348230923)
                ·
                  refine ⟨6094773462427259022346385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063182308284839348230923 6094773462427259022346385)
                  ·
                    refine ⟨4571080096820444266759789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094773462427259022346385 4571080096820444266759789)
                    ·
                      refine ⟨1714155036307666600034921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571080096820444266759789 1714155036307666600034921)
                      ·
                        rfl

theorem cell23_3338305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3338305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338305 prefixEnd_3338305 := by exact prefixLift 3338305
  have htrace : WordTrace (prefixWord ++ tailWord_3338305) baseStart_3338305 baseEnd_3338305 := by
    simpa [prefixWord, tailWord_3338305, baseEnd_3338305] using wordTrace_append hprefix tailTrace_3338305
  have hstable : (prefixWord ++ tailWord_3338305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338305).length < 2 ^ (prefixWord ++ tailWord_3338305).sum := by decide
  have hdescent : baseEnd_3338305 < baseStart_3338305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338318 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3338318 : Nat := 118140960795 + 3338318 * 2 ^ 59
def prefixEnd_3338318 : Nat := 4983230072969 + 3 ^ 40 * 3338318 * 2
def baseEnd_3338318 : Nat := 1714161711556175049172361

theorem tailTrace_3338318 : CollatzResearch.WordTrace tailWord_3338318 prefixEnd_3338318 1714161711556175049172361 := by
  unfold tailWord_3338318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219807539981437521049951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81172306879901000112266405 15219807539981437521049951)
  ·
    refine ⟨22829711309972156281574927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15219807539981437521049951 22829711309972156281574927)
    ·
      refine ⟨34244566964958234422362391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22829711309972156281574927 34244566964958234422362391)
      ·
        refine ⟨51366850447437351633543587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34244566964958234422362391 51366850447437351633543587)
        ·
          refine ⟨77050275671156027450315381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51366850447437351633543587 77050275671156027450315381)
          ·
            refine ⟨7223463344170877573467067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77050275671156027450315381 7223463344170877573467067)
            ·
              refine ⟨10835195016256316360200601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223463344170877573467067 10835195016256316360200601)
              ·
                refine ⟨8126396262192237270150451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10835195016256316360200601 8126396262192237270150451)
                ·
                  refine ⟨12189594393288355905225677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8126396262192237270150451 12189594393288355905225677)
                  ·
                    refine ⟨4571097897483133464459629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12189594393288355905225677 4571097897483133464459629)
                    ·
                      refine ⟨1714161711556175049172361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571097897483133464459629 1714161711556175049172361)
                      ·
                        rfl

theorem cell23_3338318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3338318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338318 prefixEnd_3338318 := by exact prefixLift 3338318
  have htrace : WordTrace (prefixWord ++ tailWord_3338318) baseStart_3338318 baseEnd_3338318 := by
    simpa [prefixWord, tailWord_3338318, baseEnd_3338318] using wordTrace_append hprefix tailTrace_3338318
  have hstable : (prefixWord ++ tailWord_3338318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338318).length < 2 ^ (prefixWord ++ tailWord_3338318).sum := by decide
  have hdescent : baseEnd_3338318 < baseStart_3338318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338322 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_3338322 : Nat := 118140960795 + 3338322 * 2 ^ 59
def prefixEnd_3338322 : Nat := 4983230072969 + 3 ^ 40 * 3338322 * 2
def baseEnd_3338322 : Nat := 1714163765478793033522343

theorem tailTrace_3338322 : CollatzResearch.WordTrace tailWord_3338322 prefixEnd_3338322 1714163765478793033522343 := by
  unfold tailWord_3338322
  simp only [CollatzResearch.WordTrace]
  refine ⟨30439651552959252212886305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81172404141224672567696813 30439651552959252212886305)
  ·
    refine ⟨22829738664719439159664729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30439651552959252212886305 22829738664719439159664729)
    ·
      refine ⟨17122303998539579369748547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22829738664719439159664729 17122303998539579369748547)
      ·
        refine ⟨25683455997809369054622821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17122303998539579369748547 25683455997809369054622821)
        ·
          refine ⟨4815647999589256697741779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25683455997809369054622821 4815647999589256697741779)
          ·
            refine ⟨7223471999383885046612669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815647999589256697741779 7223471999383885046612669)
            ·
              refine ⟨2708801999768956892479751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7223471999383885046612669 2708801999768956892479751)
              ·
                refine ⟨4063202999653435338719627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708801999768956892479751 4063202999653435338719627)
                ·
                  refine ⟨6094804499480153008079441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063202999653435338719627 6094804499480153008079441)
                  ·
                    refine ⟨4571103374610114756059581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6094804499480153008079441 4571103374610114756059581)
                    ·
                      refine ⟨1714163765478793033522343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571103374610114756059581 1714163765478793033522343)
                      ·
                        rfl

theorem cell23_3338322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_3338322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338322 prefixEnd_3338322 := by exact prefixLift 3338322
  have htrace : WordTrace (prefixWord ++ tailWord_3338322) baseStart_3338322 baseEnd_3338322 := by
    simpa [prefixWord, tailWord_3338322, baseEnd_3338322] using wordTrace_append hprefix tailTrace_3338322
  have hstable : (prefixWord ++ tailWord_3338322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338322).length < 2 ^ (prefixWord ++ tailWord_3338322).sum := by decide
  have hdescent : baseEnd_3338322 < baseStart_3338322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338341 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3338341 : Nat := 118140960795 + 3338341 * 2 ^ 59
def prefixEnd_3338341 : Nat := 4983230072969 + 3 ^ 40 * 3338341 * 2
def baseEnd_3338341 : Nat := 1714173521611228459184755

theorem tailTrace_3338341 : CollatzResearch.WordTrace tailWord_3338341 prefixEnd_3338341 1714173521611228459184755 := by
  unfold tailWord_3338341
  simp only [CollatzResearch.WordTrace]
  refine ⟨121759299198768175096486877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81172866132512116730991251 121759299198768175096486877)
  ·
    refine ⟨45659737199538065661182579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121759299198768175096486877 45659737199538065661182579)
    ·
      refine ⟨68489605799307098491773869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45659737199538065661182579 68489605799307098491773869)
      ·
        refine ⟨25683602174740161934415201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68489605799307098491773869 25683602174740161934415201)
        ·
          refine ⟨19262701631055121450811401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25683602174740161934415201 19262701631055121450811401)
          ·
            refine ⟨14447026223291341088108551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19262701631055121450811401 14447026223291341088108551)
            ·
              refine ⟨21670539334937011632162827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14447026223291341088108551 21670539334937011632162827)
              ·
                refine ⟨32505809002405517448244241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21670539334937011632162827 32505809002405517448244241)
                ·
                  refine ⟨24379356751804138086183181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32505809002405517448244241 24379356751804138086183181)
                  ·
                    refine ⟨9142258781926551782318693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24379356751804138086183181 9142258781926551782318693)
                    ·
                      refine ⟨1714173521611228459184755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9142258781926551782318693 1714173521611228459184755)
                      ·
                        rfl

theorem cell23_3338341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3338341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338341 prefixEnd_3338341 := by exact prefixLift 3338341
  have htrace : WordTrace (prefixWord ++ tailWord_3338341) baseStart_3338341 baseEnd_3338341 := by
    simpa [prefixWord, tailWord_3338341, baseEnd_3338341] using wordTrace_append hprefix tailTrace_3338341
  have hstable : (prefixWord ++ tailWord_3338341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338341).length < 2 ^ (prefixWord ++ tailWord_3338341).sum := by decide
  have hdescent : baseEnd_3338341 < baseStart_3338341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338351 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 2, 6]
def baseStart_3338351 : Nat := 118140960795 + 3338351 * 2 ^ 59
def prefixEnd_3338351 : Nat := 4983230072969 + 3 ^ 40 * 3338351 * 2
def baseEnd_3338351 : Nat := 571392885472591140019903

theorem tailTrace_3338351 : CollatzResearch.WordTrace tailWord_3338351 prefixEnd_3338351 571392885472591140019903 := by
  unfold tailWord_3338351
  simp only [CollatzResearch.WordTrace]
  refine ⟨121759663928731946804350907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81173109285821297869567271 121759663928731946804350907)
  ·
    refine ⟨182639495893097920206526361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121759663928731946804350907 182639495893097920206526361)
    ·
      refine ⟨136979621919823440154894771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182639495893097920206526361 136979621919823440154894771)
      ·
        refine ⟨205469432879735160232342157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136979621919823440154894771 205469432879735160232342157)
        ·
          refine ⟨77051037329900685087128309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205469432879735160232342157 77051037329900685087128309)
          ·
            refine ⟨7223534749678189226918279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77051037329900685087128309 7223534749678189226918279)
            ·
              refine ⟨10835302124517283840377419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223534749678189226918279 10835302124517283840377419)
              ·
                refine ⟨16252953186775925760566129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10835302124517283840377419 16252953186775925760566129)
                ·
                  refine ⟨12189714890081944320424597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16252953186775925760566129 12189714890081944320424597)
                  ·
                    refine ⟨571392885472591140019903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12189714890081944320424597 571392885472591140019903)
                    ·
                      rfl

theorem cell23_3338351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_3338351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338351 prefixEnd_3338351 := by exact prefixLift 3338351
  have htrace : WordTrace (prefixWord ++ tailWord_3338351) baseStart_3338351 baseEnd_3338351 := by
    simpa [prefixWord, tailWord_3338351, baseEnd_3338351] using wordTrace_append hprefix tailTrace_3338351
  have hstable : (prefixWord ++ tailWord_3338351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338351).length < 2 ^ (prefixWord ++ tailWord_3338351).sum := by decide
  have hdescent : baseEnd_3338351 < baseStart_3338351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338392 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3338392 : Nat := 118140960795 + 3338392 * 2 ^ 59
def prefixEnd_3338392 : Nat := 4983230072969 + 3 ^ 40 * 3338392 * 2
def baseEnd_3338392 : Nat := 1714199709124607759647021

theorem tailTrace_3338392 : CollatzResearch.WordTrace tailWord_3338392 prefixEnd_3338392 1714199709124607759647021 := by
  unfold tailWord_3338392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60880579660791705403296715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81174106214388940537728953 60880579660791705403296715)
  ·
    refine ⟨91320869491187558104945073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60880579660791705403296715 91320869491187558104945073)
    ·
      refine ⟨68490652118390668578708805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91320869491187558104945073 68490652118390668578708805)
      ·
        refine ⟨12841997272198250358507901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68490652118390668578708805 12841997272198250358507901)
        ·
          refine ⟨4815748977074343884440463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12841997272198250358507901 4815748977074343884440463)
          ·
            refine ⟨7223623465611515826660695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815748977074343884440463 7223623465611515826660695)
            ·
              refine ⟨10835435198417273739991043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223623465611515826660695 10835435198417273739991043)
              ·
                refine ⟨16253152797625910609986565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10835435198417273739991043 16253152797625910609986565)
                ·
                  refine ⟨3047466149554858239372481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16253152797625910609986565 3047466149554858239372481)
                  ·
                    refine ⟨2285599612166143679529361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3047466149554858239372481 2285599612166143679529361)
                    ·
                      refine ⟨1714199709124607759647021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285599612166143679529361 1714199709124607759647021)
                      ·
                        rfl

theorem cell23_3338392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3338392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338392 prefixEnd_3338392 := by exact prefixLift 3338392
  have htrace : WordTrace (prefixWord ++ tailWord_3338392) baseStart_3338392 baseEnd_3338392 := by
    simpa [prefixWord, tailWord_3338392, baseEnd_3338392] using wordTrace_append hprefix tailTrace_3338392
  have hstable : (prefixWord ++ tailWord_3338392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338392).length < 2 ^ (prefixWord ++ tailWord_3338392).sum := by decide
  have hdescent : baseEnd_3338392 < baseStart_3338392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338460 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3338460 : Nat := 118140960795 + 3338460 * 2 ^ 59
def prefixEnd_3338460 : Nat := 4983230072969 + 3 ^ 40 * 3338460 * 2
def baseEnd_3338460 : Nat := 1714234625809113493596709

theorem tailTrace_3338460 : CollatzResearch.WordTrace tailWord_3338460 prefixEnd_3338460 1714234625809113493596709 := by
  unfold tailWord_3338460
  simp only [CollatzResearch.WordTrace]
  refine ⟨60881819742668529210034417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81175759656891372280045889 60881819742668529210034417)
  ·
    refine ⟨45661364807001396907525813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60881819742668529210034417 45661364807001396907525813)
    ·
      refine ⟨4280752950656380960080545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45661364807001396907525813 4280752950656380960080545)
      ·
        refine ⟨3210564712992285720060409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4280752950656380960080545 3210564712992285720060409)
        ·
          refine ⟨2407923534744214290045307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210564712992285720060409 2407923534744214290045307)
          ·
            refine ⟨3611885302116321435067961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407923534744214290045307 3611885302116321435067961)
            ·
              refine ⟨2708913976587241076300971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611885302116321435067961 2708913976587241076300971)
              ·
                refine ⟨4063370964880861614451457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708913976587241076300971 4063370964880861614451457)
                ·
                  refine ⟨3047528223660646210838593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4063370964880861614451457 3047528223660646210838593)
                  ·
                    refine ⟨2285646167745484658128945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3047528223660646210838593 2285646167745484658128945)
                    ·
                      refine ⟨1714234625809113493596709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285646167745484658128945 1714234625809113493596709)
                      ·
                        rfl

theorem cell23_3338460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3338460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338460 prefixEnd_3338460 := by exact prefixLift 3338460
  have htrace : WordTrace (prefixWord ++ tailWord_3338460) baseStart_3338460 baseEnd_3338460 := by
    simpa [prefixWord, tailWord_3338460, baseEnd_3338460] using wordTrace_append hprefix tailTrace_3338460
  have hstable : (prefixWord ++ tailWord_3338460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338460).length < 2 ^ (prefixWord ++ tailWord_3338460).sum := by decide
  have hdescent : baseEnd_3338460 < baseStart_3338460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338468 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_3338468 : Nat := 118140960795 + 3338468 * 2 ^ 59
def prefixEnd_3338468 : Nat := 4983230072969 + 3 ^ 40 * 3338468 * 2
def baseEnd_3338468 : Nat := 1714238733654349462296671

theorem tailTrace_3338468 : CollatzResearch.WordTrace tailWord_3338468 prefixEnd_3338468 1714238733654349462296671 := by
  unfold tailWord_3338468
  simp only [CollatzResearch.WordTrace]
  refine ⟨60881965634654037893180029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81175954179538717190906705 60881965634654037893180029)
  ·
    refine ⟨22830737112995264209942511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60881965634654037893180029 22830737112995264209942511)
    ·
      refine ⟨34246105669492896314913767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22830737112995264209942511 34246105669492896314913767)
      ·
        refine ⟨51369158504239344472370651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34246105669492896314913767 51369158504239344472370651)
        ·
          refine ⟨77053737756359016708555977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51369158504239344472370651 77053737756359016708555977)
          ·
            refine ⟨57790303317269262531416983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77053737756359016708555977 57790303317269262531416983)
            ·
              refine ⟨86685454975903893797125475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57790303317269262531416983 86685454975903893797125475)
              ·
                refine ⟨130028182463855840695688213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86685454975903893797125475 130028182463855840695688213)
                ·
                  refine ⟨6095071052993242532610385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130028182463855840695688213 6095071052993242532610385)
                  ·
                    refine ⟨4571303289744931899457789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6095071052993242532610385 4571303289744931899457789)
                    ·
                      refine ⟨1714238733654349462296671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571303289744931899457789 1714238733654349462296671)
                      ·
                        rfl

theorem cell23_3338468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_3338468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338468 prefixEnd_3338468 := by exact prefixLift 3338468
  have htrace : WordTrace (prefixWord ++ tailWord_3338468) baseStart_3338468 baseEnd_3338468 := by
    simpa [prefixWord, tailWord_3338468, baseEnd_3338468] using wordTrace_append hprefix tailTrace_3338468
  have hstable : (prefixWord ++ tailWord_3338468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338468).length < 2 ^ (prefixWord ++ tailWord_3338468).sum := by decide
  have hdescent : baseEnd_3338468 < baseStart_3338468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338511 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_3338511 : Nat := 118140960795 + 3338511 * 2 ^ 59
def prefixEnd_3338511 : Nat := 4983230072969 + 3 ^ 40 * 3338511 * 2
def baseEnd_3338511 : Nat := 1714260813322492794058973

theorem tailTrace_3338511 : CollatzResearch.WordTrace tailWord_3338511 prefixEnd_3338511 1714260813322492794058973 := by
  unfold tailWord_3338511
  simp only [CollatzResearch.WordTrace]
  refine ⟨121765499608152294130175387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81176999738768196086783591 121765499608152294130175387)
  ·
    refine ⟨182648249412228441195263081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121765499608152294130175387 182648249412228441195263081)
    ·
      refine ⟨136986187059171330896447311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182648249412228441195263081 136986187059171330896447311)
      ·
        refine ⟨205479280588756996344670967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136986187059171330896447311 205479280588756996344670967)
        ·
          refine ⟨308218920883135494517006451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205479280588756996344670967 308218920883135494517006451)
          ·
            refine ⟨462328381324703241775509677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308218920883135494517006451 462328381324703241775509677)
            ·
              refine ⟨173373142996763715665816129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462328381324703241775509677 173373142996763715665816129)
              ·
                refine ⟨130029857247572786749362097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173373142996763715665816129 130029857247572786749362097)
                ·
                  refine ⟨97522392935679590062021573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130029857247572786749362097 97522392935679590062021573)
                  ·
                    refine ⟨18285448675439923136629045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97522392935679590062021573 18285448675439923136629045)
                    ·
                      refine ⟨1714260813322492794058973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18285448675439923136629045 1714260813322492794058973)
                      ·
                        rfl

theorem cell23_3338511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_3338511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338511 prefixEnd_3338511 := by exact prefixLift 3338511
  have htrace : WordTrace (prefixWord ++ tailWord_3338511) baseStart_3338511 baseEnd_3338511 := by
    simpa [prefixWord, tailWord_3338511, baseEnd_3338511] using wordTrace_append hprefix tailTrace_3338511
  have hstable : (prefixWord ++ tailWord_3338511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338511).length < 2 ^ (prefixWord ++ tailWord_3338511).sum := by decide
  have hdescent : baseEnd_3338511 < baseStart_3338511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338532 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_3338532 : Nat := 118140960795 + 3338532 * 2 ^ 59
def prefixEnd_3338532 : Nat := 4983230072969 + 3 ^ 40 * 3338532 * 2
def baseEnd_3338532 : Nat := 1714271596416237211896377

theorem tailTrace_3338532 : CollatzResearch.WordTrace tailWord_3338532 prefixEnd_3338532 1714271596416237211896377 := by
  unfold tailWord_3338532
  simp only [CollatzResearch.WordTrace]
  refine ⟨60883132770538107358344925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81177510360717476477793233 60883132770538107358344925)
  ·
    refine ⟨22831174788951790259379347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60883132770538107358344925 22831174788951790259379347)
    ·
      refine ⟨34246762183427685389069021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22831174788951790259379347 34246762183427685389069021)
      ·
        refine ⟨12842535818785382020900883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34246762183427685389069021 12842535818785382020900883)
        ·
          refine ⟨19263803728178073031351325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12842535818785382020900883 19263803728178073031351325)
          ·
            refine ⟨7223926398066777386756747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19263803728178073031351325 7223926398066777386756747)
            ·
              refine ⟨10835889597100166080135121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7223926398066777386756747 10835889597100166080135121)
              ·
                refine ⟨8126917197825124560101341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10835889597100166080135121 8126917197825124560101341)
                ·
                  refine ⟨3047593949184421710038003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8126917197825124560101341 3047593949184421710038003)
                  ·
                    refine ⟨4571390923776632565057005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047593949184421710038003 4571390923776632565057005)
                    ·
                      refine ⟨1714271596416237211896377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571390923776632565057005 1714271596416237211896377)
                      ·
                        rfl

theorem cell23_3338532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_3338532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338532 prefixEnd_3338532 := by exact prefixLift 3338532
  have htrace : WordTrace (prefixWord ++ tailWord_3338532) baseStart_3338532 baseEnd_3338532 := by
    simpa [prefixWord, tailWord_3338532, baseEnd_3338532] using wordTrace_append hprefix tailTrace_3338532
  have hstable : (prefixWord ++ tailWord_3338532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338532).length < 2 ^ (prefixWord ++ tailWord_3338532).sum := by decide
  have hdescent : baseEnd_3338532 < baseStart_3338532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338549 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_3338549 : Nat := 118140960795 + 3338549 * 2 ^ 59
def prefixEnd_3338549 : Nat := 4983230072969 + 3 ^ 40 * 3338549 * 2
def baseEnd_3338549 : Nat := 1714280325587363645383799

theorem tailTrace_3338549 : CollatzResearch.WordTrace tailWord_3338549 prefixEnd_3338549 1714280325587363645383799 := by
  unfold tailWord_3338549
  simp only [CollatzResearch.WordTrace]
  refine ⟨121766885582014626620058701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81177923721343084413372467 121766885582014626620058701)
  ·
    refine ⟨45662582093255484982522013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121766885582014626620058701 45662582093255484982522013)
    ·
      refine ⟨17123468284970806868445755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45662582093255484982522013 17123468284970806868445755)
      ·
        refine ⟨25685202427456210302668633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17123468284970806868445755 25685202427456210302668633)
        ·
          refine ⟨19263901820592157727001475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25685202427456210302668633 19263901820592157727001475)
          ·
            refine ⟨28895852730888236590502213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19263901820592157727001475 28895852730888236590502213)
            ·
              refine ⟨5417972387041544360719165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28895852730888236590502213 5417972387041544360719165)
              ·
                refine ⟨2031739645140579135269687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5417972387041544360719165 2031739645140579135269687)
                ·
                  refine ⟨3047609467710868702904531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031739645140579135269687 3047609467710868702904531)
                  ·
                    refine ⟨4571414201566303054356797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047609467710868702904531 4571414201566303054356797)
                    ·
                      refine ⟨1714280325587363645383799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571414201566303054356797 1714280325587363645383799)
                      ·
                        rfl

theorem cell23_3338549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_3338549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338549 prefixEnd_3338549 := by exact prefixLift 3338549
  have htrace : WordTrace (prefixWord ++ tailWord_3338549) baseStart_3338549 baseEnd_3338549 := by
    simpa [prefixWord, tailWord_3338549, baseEnd_3338549] using wordTrace_append hprefix tailTrace_3338549
  have hstable : (prefixWord ++ tailWord_3338549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338549).length < 2 ^ (prefixWord ++ tailWord_3338549).sum := by decide
  have hdescent : baseEnd_3338549 < baseStart_3338549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338568 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3338568 : Nat := 118140960795 + 3338568 * 2 ^ 59
def prefixEnd_3338568 : Nat := 4983230072969 + 3 ^ 40 * 3338568 * 2
def baseEnd_3338568 : Nat := 1714290081719799071046211

theorem tailTrace_3338568 : CollatzResearch.WordTrace tailWord_3338568 prefixEnd_3338568 1714290081719799071046211 := by
  unfold tailWord_3338568
  simp only [CollatzResearch.WordTrace]
  refine ⟨60883789284472896432500179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81178385712630528576666905 60883789284472896432500179)
  ·
    refine ⟨91325683926709344648750269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60883789284472896432500179 91325683926709344648750269)
    ·
      refine ⟨34247131472516004243281351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91325683926709344648750269 34247131472516004243281351)
      ·
        refine ⟨51370697208774006364922027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34247131472516004243281351 51370697208774006364922027)
        ·
          refine ⟨77056045813161009547383041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51370697208774006364922027 77056045813161009547383041)
          ·
            refine ⟨57792034359870757160537281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77056045813161009547383041 57792034359870757160537281)
            ·
              refine ⟨43344025769903067870402961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57792034359870757160537281 43344025769903067870402961)
              ·
                refine ⟨32508019327427300902802221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43344025769903067870402961 32508019327427300902802221)
                ·
                  refine ⟨12190507247785237838550833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32508019327427300902802221 12190507247785237838550833)
                  ·
                    refine ⟨9142880435838928378913125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12190507247785237838550833 9142880435838928378913125)
                    ·
                      refine ⟨1714290081719799071046211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9142880435838928378913125 1714290081719799071046211)
                      ·
                        rfl

theorem cell23_3338568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3338568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338568 prefixEnd_3338568 := by exact prefixLift 3338568
  have htrace : WordTrace (prefixWord ++ tailWord_3338568) baseStart_3338568 baseEnd_3338568 := by
    simpa [prefixWord, tailWord_3338568, baseEnd_3338568] using wordTrace_append hprefix tailTrace_3338568
  have hstable : (prefixWord ++ tailWord_3338568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338568).length < 2 ^ (prefixWord ++ tailWord_3338568).sum := by decide
  have hdescent : baseEnd_3338568 < baseStart_3338568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338605 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3338605 : Nat := 118140960795 + 3338605 * 2 ^ 59
def prefixEnd_3338605 : Nat := 4983230072969 + 3 ^ 40 * 3338605 * 2
def baseEnd_3338605 : Nat := 1714309080504015426283541

theorem tailTrace_3338605 : CollatzResearch.WordTrace tailWord_3338605 prefixEnd_3338605 1714309080504015426283541 := by
  unfold tailWord_3338605
  simp only [CollatzResearch.WordTrace]
  refine ⟨121768928069811748184097269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81179285379874498789398179 121768928069811748184097269)
  ·
    refine ⟨11415837006544851392259119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121768928069811748184097269 11415837006544851392259119)
    ·
      refine ⟨17123755509817277088388679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11415837006544851392259119 17123755509817277088388679)
      ·
        refine ⟨25685633264725915632583019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17123755509817277088388679 25685633264725915632583019)
        ·
          refine ⟨38528449897088873448874529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25685633264725915632583019 38528449897088873448874529)
          ·
            refine ⟨28896337422816655086655897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38528449897088873448874529 28896337422816655086655897)
            ·
              refine ⟨21672253067112491314991923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28896337422816655086655897 21672253067112491314991923)
              ·
                refine ⟨32508379600668736972487885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21672253067112491314991923 32508379600668736972487885)
                ·
                  refine ⟨12190642350250776364682957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32508379600668736972487885 12190642350250776364682957)
                  ·
                    refine ⟨4571490881344041136756109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12190642350250776364682957 4571490881344041136756109)
                    ·
                      refine ⟨1714309080504015426283541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571490881344041136756109 1714309080504015426283541)
                      ·
                        rfl

theorem cell23_3338605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3338605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338605 prefixEnd_3338605 := by exact prefixLift 3338605
  have htrace : WordTrace (prefixWord ++ tailWord_3338605) baseStart_3338605 baseEnd_3338605 := by
    simpa [prefixWord, tailWord_3338605, baseEnd_3338605] using wordTrace_append hprefix tailTrace_3338605
  have hstable : (prefixWord ++ tailWord_3338605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338605).length < 2 ^ (prefixWord ++ tailWord_3338605).sum := by decide
  have hdescent : baseEnd_3338605 < baseStart_3338605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338632 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_3338632 : Nat := 118140960795 + 3338632 * 2 ^ 59
def prefixEnd_3338632 : Nat := 4983230072969 + 3 ^ 40 * 3338632 * 2
def baseEnd_3338632 : Nat := 1714322944481686820645917

theorem tailTrace_3338632 : CollatzResearch.WordTrace tailWord_3338632 prefixEnd_3338632 1714322944481686820645917 := by
  unfold tailWord_3338632
  simp only [CollatzResearch.WordTrace]
  refine ⟨60884956420356965897665075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81179941893809287863553433 60884956420356965897665075)
  ·
    refine ⟨91327434630535448846497613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60884956420356965897665075 91327434630535448846497613)
    ·
      refine ⟨34247787986450793317436605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91327434630535448846497613 34247787986450793317436605)
      ·
        refine ⟨12842920494919047494038727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34247787986450793317436605 12842920494919047494038727)
        ·
          refine ⟨19264380742378571241058091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12842920494919047494038727 19264380742378571241058091)
          ·
            refine ⟨28896571113567856861587137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19264380742378571241058091 28896571113567856861587137)
            ·
              refine ⟨21672428335175892646190353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28896571113567856861587137 21672428335175892646190353)
              ·
                refine ⟨16254321251381919484642765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21672428335175892646190353 16254321251381919484642765)
                ·
                  refine ⟨6095370469268219806741037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16254321251381919484642765 6095370469268219806741037)
                  ·
                    refine ⟨2285763925975582427527889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6095370469268219806741037 2285763925975582427527889)
                    ·
                      refine ⟨1714322944481686820645917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285763925975582427527889 1714322944481686820645917)
                      ·
                        rfl

theorem cell23_3338632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_3338632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338632 prefixEnd_3338632 := by exact prefixLift 3338632
  have htrace : WordTrace (prefixWord ++ tailWord_3338632) baseStart_3338632 baseEnd_3338632 := by
    simpa [prefixWord, tailWord_3338632, baseEnd_3338632] using wordTrace_append hprefix tailTrace_3338632
  have hstable : (prefixWord ++ tailWord_3338632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338632).length < 2 ^ (prefixWord ++ tailWord_3338632).sum := by decide
  have hdescent : baseEnd_3338632 < baseStart_3338632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338679 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_3338679 : Nat := 118140960795 + 3338679 * 2 ^ 59
def prefixEnd_3338679 : Nat := 4983230072969 + 3 ^ 40 * 3338679 * 2
def baseEnd_3338679 : Nat := 1714347078072448136758201

theorem tailTrace_3338679 : CollatzResearch.WordTrace tailWord_3338679 prefixEnd_3338679 1714347078072448136758201 := by
  unfold tailWord_3338679
  simp only [CollatzResearch.WordTrace]
  refine ⟨121771627071543658822291091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81181084714362439214860727 121771627071543658822291091)
  ·
    refine ⟨182657440607315488233436637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121771627071543658822291091 182657440607315488233436637)
    ·
      refine ⟨68496540227743308087538739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182657440607315488233436637 68496540227743308087538739)
      ·
        refine ⟨102744810341614962131308109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68496540227743308087538739 102744810341614962131308109)
        ·
          refine ⟨38529303878105610799240541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102744810341614962131308109 38529303878105610799240541)
          ·
            refine ⟨14448488954289604049715203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38529303878105610799240541 14448488954289604049715203)
            ·
              refine ⟨21672733431434406074572805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14448488954289604049715203 21672733431434406074572805)
              ·
                refine ⟨4063637518393951138982401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21672733431434406074572805 4063637518393951138982401)
                ·
                  refine ⟨3047728138795463354236801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4063637518393951138982401 3047728138795463354236801)
                  ·
                    refine ⟨2285796104096597515677601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3047728138795463354236801 2285796104096597515677601)
                    ·
                      refine ⟨1714347078072448136758201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285796104096597515677601 1714347078072448136758201)
                      ·
                        rfl

theorem cell23_3338679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_3338679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338679 prefixEnd_3338679 := by exact prefixLift 3338679
  have htrace : WordTrace (prefixWord ++ tailWord_3338679) baseStart_3338679 baseEnd_3338679 := by
    simpa [prefixWord, tailWord_3338679, baseEnd_3338679] using wordTrace_append hprefix tailTrace_3338679
  have hstable : (prefixWord ++ tailWord_3338679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338679).length < 2 ^ (prefixWord ++ tailWord_3338679).sum := by decide
  have hdescent : baseEnd_3338679 < baseStart_3338679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338688 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8]
def baseStart_3338688 : Nat := 118140960795 + 3338688 * 2 ^ 59
def prefixEnd_3338688 : Nat := 4983230072969 + 3 ^ 40 * 3338688 * 2
def baseEnd_3338688 : Nat := 1714351699398338601545659

theorem tailTrace_3338688 : CollatzResearch.WordTrace tailWord_3338688 prefixEnd_3338688 1714351699398338601545659 := by
  unfold tailWord_3338688
  simp only [CollatzResearch.WordTrace]
  refine ⟨60885977664255526679684359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81181303552340702239579145 60885977664255526679684359)
  ·
    refine ⟨91328966496383290019526539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60885977664255526679684359 91328966496383290019526539)
    ·
      refine ⟨136993449744574935029289809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91328966496383290019526539 136993449744574935029289809)
      ·
        refine ⟨102745087308431201271967357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136993449744574935029289809 102745087308431201271967357)
        ·
          refine ⟨38529407740661700476987759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102745087308431201271967357 38529407740661700476987759)
          ·
            refine ⟨57794111610992550715481639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38529407740661700476987759 57794111610992550715481639)
            ·
              refine ⟨86691167416488826073222459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57794111610992550715481639 86691167416488826073222459)
              ·
                refine ⟨130036751124733239109833689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86691167416488826073222459 130036751124733239109833689)
                ·
                  refine ⟨97527563343549929332375267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130036751124733239109833689 97527563343549929332375267)
                  ·
                    refine ⟨146291345015324893998562901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97527563343549929332375267 146291345015324893998562901)
                    ·
                      refine ⟨1714351699398338601545659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146291345015324893998562901 1714351699398338601545659)
                      ·
                        rfl

theorem cell23_3338688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_3338688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338688 prefixEnd_3338688 := by exact prefixLift 3338688
  have htrace : WordTrace (prefixWord ++ tailWord_3338688) baseStart_3338688 baseEnd_3338688 := by
    simpa [prefixWord, tailWord_3338688, baseEnd_3338688] using wordTrace_append hprefix tailTrace_3338688
  have hstable : (prefixWord ++ tailWord_3338688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338688).length < 2 ^ (prefixWord ++ tailWord_3338688).sum := by decide
  have hdescent : baseEnd_3338688 < baseStart_3338688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338695 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_3338695 : Nat := 118140960795 + 3338695 * 2 ^ 59
def prefixEnd_3338695 : Nat := 4983230072969 + 3 ^ 40 * 3338695 * 2
def baseEnd_3338695 : Nat := 1714355293762920074158127

theorem tailTrace_3338695 : CollatzResearch.WordTrace tailWord_3338695 prefixEnd_3338695 1714355293762920074158127 := by
  unfold tailWord_3338695
  simp only [CollatzResearch.WordTrace]
  refine ⟨121772210639485693554873539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81181473759657129036582359 121772210639485693554873539)
  ·
    refine ⟨182658315959228540332310309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121772210639485693554873539 182658315959228540332310309)
    ·
      refine ⟨34248434242355351312308183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182658315959228540332310309 34248434242355351312308183)
      ·
        refine ⟨51372651363533026968462275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34248434242355351312308183 51372651363533026968462275)
        ·
          refine ⟨77058977045299540452693413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51372651363533026968462275 77058977045299540452693413)
          ·
            refine ⟨14448558195993663834880015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77058977045299540452693413 14448558195993663834880015)
            ·
              refine ⟨21672837293990495752320023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14448558195993663834880015 21672837293990495752320023)
              ·
                refine ⟨32509255940985743628480035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21672837293990495752320023 32509255940985743628480035)
                ·
                  refine ⟨48763883911478615442720053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32509255940985743628480035 48763883911478615442720053)
                  ·
                    refine ⟨4571614116701120197755005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48763883911478615442720053 4571614116701120197755005)
                    ·
                      refine ⟨1714355293762920074158127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571614116701120197755005 1714355293762920074158127)
                      ·
                        rfl

theorem cell23_3338695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_3338695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338695 prefixEnd_3338695 := by exact prefixLift 3338695
  have htrace : WordTrace (prefixWord ++ tailWord_3338695) baseStart_3338695 baseEnd_3338695 := by
    simpa [prefixWord, tailWord_3338695, baseEnd_3338695] using wordTrace_append hprefix tailTrace_3338695
  have hstable : (prefixWord ++ tailWord_3338695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338695).length < 2 ^ (prefixWord ++ tailWord_3338695).sum := by decide
  have hdescent : baseEnd_3338695 < baseStart_3338695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338735 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_3338735 : Nat := 118140960795 + 3338735 * 2 ^ 59
def prefixEnd_3338735 : Nat := 4983230072969 + 3 ^ 40 * 3338735 * 2
def baseEnd_3338735 : Nat := 1714375832989099917657943

theorem tailTrace_3338735 : CollatzResearch.WordTrace tailWord_3338735 prefixEnd_3338735 1714375832989099917657943 := by
  unfold tailWord_3338735
  simp only [CollatzResearch.WordTrace]
  refine ⟨121773669559340780386329659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81182446372893853590886439 121773669559340780386329659)
  ·
    refine ⟨182660504339011170579494489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121773669559340780386329659 182660504339011170579494489)
    ·
      refine ⟨136995378254258377934620867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182660504339011170579494489 136995378254258377934620867)
      ·
        refine ⟨205493067381387566901931301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136995378254258377934620867 205493067381387566901931301)
        ·
          refine ⟨38529950134010168794112119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205493067381387566901931301 38529950134010168794112119)
          ·
            refine ⟨57794925201015253191168179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38529950134010168794112119 57794925201015253191168179)
            ·
              refine ⟨86692387801522879786752269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57794925201015253191168179 86692387801522879786752269)
              ·
                refine ⟨32509645425571079920032101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86692387801522879786752269 32509645425571079920032101)
                ·
                  refine ⟨6095558517294577485006019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32509645425571079920032101 6095558517294577485006019)
                  ·
                    refine ⟨9143337775941866227509029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6095558517294577485006019 9143337775941866227509029)
                    ·
                      refine ⟨1714375832989099917657943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9143337775941866227509029 1714375832989099917657943)
                      ·
                        rfl

theorem cell23_3338735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_3338735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338735 prefixEnd_3338735 := by exact prefixLift 3338735
  have htrace : WordTrace (prefixWord ++ tailWord_3338735) baseStart_3338735 baseEnd_3338735 := by
    simpa [prefixWord, tailWord_3338735, baseEnd_3338735] using wordTrace_append hprefix tailTrace_3338735
  have hstable : (prefixWord ++ tailWord_3338735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338735).length < 2 ^ (prefixWord ++ tailWord_3338735).sum := by decide
  have hdescent : baseEnd_3338735 < baseStart_3338735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338755 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3]
def baseStart_3338755 : Nat := 118140960795 + 3338755 * 2 ^ 59
def prefixEnd_3338755 : Nat := 4983230072969 + 3 ^ 40 * 3338755 * 2
def baseEnd_3338755 : Nat := 1714386102602189839407851

theorem tailTrace_3338755 : CollatzResearch.WordTrace tailWord_3338755 prefixEnd_3338755 1714386102602189839407851 := by
  unfold tailWord_3338755
  simp only [CollatzResearch.WordTrace]
  refine ⟨121774399019268323802057719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81182932679512215868038479 121774399019268323802057719)
  ·
    refine ⟨182661598528902485703086579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121774399019268323802057719 182661598528902485703086579)
    ·
      refine ⟨273992397793353728554629869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182661598528902485703086579 273992397793353728554629869)
      ·
        refine ⟨102747149172507648207986201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273992397793353728554629869 102747149172507648207986201)
        ·
          refine ⟨77060361879380736155989651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102747149172507648207986201 77060361879380736155989651)
          ·
            refine ⟨115590542819071104233984477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77060361879380736155989651 115590542819071104233984477)
            ·
              refine ⟨43346453557151664087744179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115590542819071104233984477 43346453557151664087744179)
              ·
                refine ⟨65019680335727496131616269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43346453557151664087744179 65019680335727496131616269)
                ·
                  refine ⟨24382380125897811049356101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65019680335727496131616269 24382380125897811049356101)
                  ·
                    refine ⟨4571696273605839571754269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24382380125897811049356101 4571696273605839571754269)
                    ·
                      refine ⟨1714386102602189839407851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571696273605839571754269 1714386102602189839407851)
                      ·
                        rfl

theorem cell23_3338755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_3338755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338755 prefixEnd_3338755 := by exact prefixLift 3338755
  have htrace : WordTrace (prefixWord ++ tailWord_3338755) baseStart_3338755 baseEnd_3338755 := by
    simpa [prefixWord, tailWord_3338755, baseEnd_3338755] using wordTrace_append hprefix tailTrace_3338755
  have hstable : (prefixWord ++ tailWord_3338755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338755).length < 2 ^ (prefixWord ++ tailWord_3338755).sum := by decide
  have hdescent : baseEnd_3338755 < baseStart_3338755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338762 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3338762 : Nat := 118140960795 + 3338762 * 2 ^ 59
def prefixEnd_3338762 : Nat := 4983230072969 + 3 ^ 40 * 3338762 * 2
def baseEnd_3338762 : Nat := 571463232322257104006773

theorem tailTrace_3338762 : CollatzResearch.WordTrace tailWord_3338762 prefixEnd_3338762 571463232322257104006773 := by
  unfold tailWord_3338762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443663582560740999390635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81183102886828642665041693 30443663582560740999390635)
  ·
    refine ⟨45665495373841111499085953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30443663582560740999390635 45665495373841111499085953)
    ·
      refine ⟨34249121530380833624314465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45665495373841111499085953 34249121530380833624314465)
      ·
        refine ⟨25686841147785625218235849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34249121530380833624314465 25686841147785625218235849)
        ·
          refine ⟨19265130860839218913676887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25686841147785625218235849 19265130860839218913676887)
          ·
            refine ⟨28897696291258828370515331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265130860839218913676887 28897696291258828370515331)
            ·
              refine ⟨43346544436888242555772997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28897696291258828370515331 43346544436888242555772997)
              ·
                refine ⟨8127477081916545479207437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43346544436888242555772997 8127477081916545479207437)
                ·
                  refine ⟨3047803905718704554702789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8127477081916545479207437 3047803905718704554702789)
                  ·
                    refine ⟨571463232322257104006773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3047803905718704554702789 571463232322257104006773)
                    ·
                      rfl

theorem cell23_3338762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3338762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338762 prefixEnd_3338762 := by exact prefixLift 3338762
  have htrace : WordTrace (prefixWord ++ tailWord_3338762) baseStart_3338762 baseEnd_3338762 := by
    simpa [prefixWord, tailWord_3338762, baseEnd_3338762] using wordTrace_append hprefix tailTrace_3338762
  have hstable : (prefixWord ++ tailWord_3338762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338762).length < 2 ^ (prefixWord ++ tailWord_3338762).sum := by decide
  have hdescent : baseEnd_3338762 < baseStart_3338762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338792 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 8]
def baseStart_3338792 : Nat := 118140960795 + 3338792 * 2 ^ 59
def prefixEnd_3338792 : Nat := 4983230072969 + 3 ^ 40 * 3338792 * 2
def baseEnd_3338792 : Nat := 190489455709600688293909

theorem tailTrace_3338792 : CollatzResearch.WordTrace tailWord_3338792 prefixEnd_3338792 190489455709600688293909 := by
  unfold tailWord_3338792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60887874260067139560577315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81183832346756186080769753 60887874260067139560577315)
  ·
    refine ⟨91331811390100709340865973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60887874260067139560577315 91331811390100709340865973)
    ·
      refine ⟨8562357317821941500706185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91331811390100709340865973 8562357317821941500706185)
      ·
        refine ⟨6421767988366456125529639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8562357317821941500706185 6421767988366456125529639)
        ·
          refine ⟨9632651982549684188294459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6421767988366456125529639 9632651982549684188294459)
          ·
            refine ⟨14448977973824526282441689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9632651982549684188294459 14448977973824526282441689)
            ·
              refine ⟨10836733480368394711831267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14448977973824526282441689 10836733480368394711831267)
              ·
                refine ⟨16255100220552592067746901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10836733480368394711831267 16255100220552592067746901)
                ·
                  refine ⟨190489455709600688293909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16255100220552592067746901 190489455709600688293909)
                  ·
                    rfl

theorem cell23_3338792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_3338792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338792 prefixEnd_3338792 := by exact prefixLift 3338792
  have htrace : WordTrace (prefixWord ++ tailWord_3338792) baseStart_3338792 baseEnd_3338792 := by
    simpa [prefixWord, tailWord_3338792, baseEnd_3338792] using wordTrace_append hprefix tailTrace_3338792
  have hstable : (prefixWord ++ tailWord_3338792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338792).length < 2 ^ (prefixWord ++ tailWord_3338792).sum := by decide
  have hdescent : baseEnd_3338792 < baseStart_3338792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338839 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 1, 5]
def baseStart_3338839 : Nat := 118140960795 + 3338839 * 2 ^ 59
def prefixEnd_3338839 : Nat := 4983230072969 + 3 ^ 40 * 3338839 * 2
def baseEnd_3338839 : Nat := 571476411659055836919155

theorem tailTrace_3338839 : CollatzResearch.WordTrace tailWord_3338839 prefixEnd_3338839 571476411659055836919155 := by
  unfold tailWord_3338839
  simp only [CollatzResearch.WordTrace]
  refine ⟨121777462750964006148115571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81184975167309337432077047 121777462750964006148115571)
  ·
    refine ⟨182666194126446009222173357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121777462750964006148115571 182666194126446009222173357)
    ·
      refine ⟨68499822797417253458315009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182666194126446009222173357 68499822797417253458315009)
      ·
        refine ⟨51374867098062940093736257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68499822797417253458315009 51374867098062940093736257)
        ·
          refine ⟨38531150323547205070302193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51374867098062940093736257 38531150323547205070302193)
          ·
            refine ⟨28898362742660403802726645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38531150323547205070302193 28898362742660403802726645)
            ·
              refine ⟨2709221507124412856505623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28898362742660403802726645 2709221507124412856505623)
              ·
                refine ⟨4063832260686619284758435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709221507124412856505623 4063832260686619284758435)
                ·
                  refine ⟨6095748391029928927137653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063832260686619284758435 6095748391029928927137653)
                  ·
                    refine ⟨571476411659055836919155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6095748391029928927137653 571476411659055836919155)
                    ·
                      rfl

theorem cell23_3338839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_3338839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338839 prefixEnd_3338839 := by exact prefixLift 3338839
  have htrace : WordTrace (prefixWord ++ tailWord_3338839) baseStart_3338839 baseEnd_3338839 := by
    simpa [prefixWord, tailWord_3338839, baseEnd_3338839] using wordTrace_append hprefix tailTrace_3338839
  have hstable : (prefixWord ++ tailWord_3338839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338839).length < 2 ^ (prefixWord ++ tailWord_3338839).sum := by decide
  have hdescent : baseEnd_3338839 < baseStart_3338839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338853 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 1, 1, 3]
def baseStart_3338853 : Nat := 118140960795 + 3338853 * 2 ^ 59
def prefixEnd_3338853 : Nat := 4983230072969 + 3 ^ 40 * 3338853 * 2
def baseEnd_3338853 : Nat := 1714436423706330455982401

theorem tailTrace_3338853 : CollatzResearch.WordTrace tailWord_3338853 prefixEnd_3338853 1714436423706330455982401 := by
  unfold tailWord_3338853
  simp only [CollatzResearch.WordTrace]
  refine ⟨121777973372913286539125213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81185315581942191026083475 121777973372913286539125213)
  ·
    refine ⟨45666740014842482452171955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121777973372913286539125213 45666740014842482452171955)
    ·
      refine ⟨68500110022263723678257933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45666740014842482452171955 68500110022263723678257933)
      ·
        refine ⟨25687541258348896379346725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68500110022263723678257933 25687541258348896379346725)
        ·
          refine ⟨4816413985940418071127511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25687541258348896379346725 4816413985940418071127511)
          ·
            refine ⟨7224620978910627106691267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816413985940418071127511 7224620978910627106691267)
            ·
              refine ⟨10836931468365940660036901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7224620978910627106691267 10836931468365940660036901)
              ·
                refine ⟨2031924650318613873756919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10836931468365940660036901 2031924650318613873756919)
                ·
                  refine ⟨3047886975477920810635379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031924650318613873756919 3047886975477920810635379)
                  ·
                    refine ⟨4571830463216881215953069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3047886975477920810635379 4571830463216881215953069)
                    ·
                      refine ⟨1714436423706330455982401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571830463216881215953069 1714436423706330455982401)
                      ·
                        rfl

theorem cell23_3338853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_3338853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338853 prefixEnd_3338853 := by exact prefixLift 3338853
  have htrace : WordTrace (prefixWord ++ tailWord_3338853) baseStart_3338853 baseEnd_3338853 := by
    simpa [prefixWord, tailWord_3338853, baseEnd_3338853] using wordTrace_append hprefix tailTrace_3338853
  have hstable : (prefixWord ++ tailWord_3338853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338853).length < 2 ^ (prefixWord ++ tailWord_3338853).sum := by decide
  have hdescent : baseEnd_3338853 < baseStart_3338853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338892 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3338892 : Nat := 118140960795 + 3338892 * 2 ^ 59
def prefixEnd_3338892 : Nat := 4983230072969 + 3 ^ 40 * 3338892 * 2
def baseEnd_3338892 : Nat := 1714456449451855803394721

theorem tailTrace_3338892 : CollatzResearch.WordTrace tailWord_3338892 prefixEnd_3338892 1714456449451855803394721 := by
  unfold tailWord_3338892
  simp only [CollatzResearch.WordTrace]
  refine ⟨60889697909885998099897465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81186263879847997466529953 60889697909885998099897465)
  ·
    refine ⟨45667273432414498574923099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60889697909885998099897465 45667273432414498574923099)
    ·
      refine ⟨68500910148621747862384649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45667273432414498574923099 68500910148621747862384649)
      ·
        refine ⟨51375682611466310896788487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68500910148621747862384649 51375682611466310896788487)
        ·
          refine ⟨77063523917199466345182731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51375682611466310896788487 77063523917199466345182731)
          ·
            refine ⟨115595285875799199517774097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77063523917199466345182731 115595285875799199517774097)
            ·
              refine ⟨86696464406849399638330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115595285875799199517774097 86696464406849399638330573)
              ·
                refine ⟨32511174152568524864373965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86696464406849399638330573 32511174152568524864373965)
                ·
                  refine ⟨12191690307213196824140237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32511174152568524864373965 12191690307213196824140237)
                  ·
                    refine ⟨4571883865204948809052589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12191690307213196824140237 4571883865204948809052589)
                    ·
                      refine ⟨1714456449451855803394721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4571883865204948809052589 1714456449451855803394721)
                      ·
                        rfl

theorem cell23_3338892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3338892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338892 prefixEnd_3338892 := by exact prefixLift 3338892
  have htrace : WordTrace (prefixWord ++ tailWord_3338892) baseStart_3338892 baseEnd_3338892 := by
    simpa [prefixWord, tailWord_3338892, baseEnd_3338892] using wordTrace_append hprefix tailTrace_3338892
  have hstable : (prefixWord ++ tailWord_3338892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338892).length < 2 ^ (prefixWord ++ tailWord_3338892).sum := by decide
  have hdescent : baseEnd_3338892 < baseStart_3338892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338895 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 7]
def baseStart_3338895 : Nat := 118140960795 + 3338895 * 2 ^ 59
def prefixEnd_3338895 : Nat := 4983230072969 + 3 ^ 40 * 3338895 * 2
def baseEnd_3338895 : Nat := 571485996631273097219069

theorem tailTrace_3338895 : CollatzResearch.WordTrace tailWord_3338895 prefixEnd_3338895 571485996631273097219069 := by
  unfold tailWord_3338895
  simp only [CollatzResearch.WordTrace]
  refine ⟨121779505238761127712154139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81186336825840751808102759 121779505238761127712154139)
  ·
    refine ⟨182669257858141691568231209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121779505238761127712154139 182669257858141691568231209)
    ·
      refine ⟨137001943393606268676173407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182669257858141691568231209 137001943393606268676173407)
      ·
        refine ⟨205502915090409403014260111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137001943393606268676173407 205502915090409403014260111)
        ·
          refine ⟨308254372635614104521390167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205502915090409403014260111 308254372635614104521390167)
          ·
            refine ⟨462381558953421156782085251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308254372635614104521390167 462381558953421156782085251)
            ·
              refine ⟨693572338430131735173127877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462381558953421156782085251 693572338430131735173127877)
              ·
                refine ⟨130044813455649700344961477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693572338430131735173127877 130044813455649700344961477)
                ·
                  refine ⟨24383402522934318814680277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130044813455649700344961477 24383402522934318814680277)
                  ·
                    refine ⟨571485996631273097219069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24383402522934318814680277 571485996631273097219069)
                    ·
                      rfl

theorem cell23_3338895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_3338895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338895 prefixEnd_3338895 := by exact prefixLift 3338895
  have htrace : WordTrace (prefixWord ++ tailWord_3338895) baseStart_3338895 baseEnd_3338895 := by
    simpa [prefixWord, tailWord_3338895, baseEnd_3338895] using wordTrace_append hprefix tailTrace_3338895
  have hstable : (prefixWord ++ tailWord_3338895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338895).length < 2 ^ (prefixWord ++ tailWord_3338895).sum := by decide
  have hdescent : baseEnd_3338895 < baseStart_3338895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338910 : List Nat := [4, 3, 1, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_3338910 : Nat := 118140960795 + 3338910 * 2 ^ 59
def prefixEnd_3338910 : Nat := 4983230072969 + 3 ^ 40 * 3338910 * 2
def baseEnd_3338910 : Nat := 1714465692103636732969639

theorem tailTrace_3338910 : CollatzResearch.WordTrace tailWord_3338910 prefixEnd_3338910 1714465692103636732969639 := by
  unfold tailWord_3338910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222506541713348159243773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81186701555804523515966789 15222506541713348159243773)
  ·
    refine ⟨5708439953142505559716415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15222506541713348159243773 5708439953142505559716415)
    ·
      refine ⟨8562659929713758339574623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708439953142505559716415 8562659929713758339574623)
      ·
        refine ⟨12843989894570637509361935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562659929713758339574623 12843989894570637509361935)
        ·
          refine ⟨19265984841855956264042903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12843989894570637509361935 19265984841855956264042903)
          ·
            refine ⟨28898977262783934396064355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265984841855956264042903 28898977262783934396064355)
            ·
              refine ⟨43348465894175901594096533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28898977262783934396064355 43348465894175901594096533)
              ·
                refine ⟨2031959338789495387223275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43348465894175901594096533 2031959338789495387223275)
                ·
                  refine ⟨3047939008184243080834913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2031959338789495387223275 3047939008184243080834913)
                  ·
                    refine ⟨2285954256138182310626185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3047939008184243080834913 2285954256138182310626185)
                    ·
                      refine ⟨1714465692103636732969639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2285954256138182310626185 1714465692103636732969639)
                      ·
                        rfl

theorem cell23_3338910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_3338910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338910 prefixEnd_3338910 := by exact prefixLift 3338910
  have htrace : WordTrace (prefixWord ++ tailWord_3338910) baseStart_3338910 baseEnd_3338910 := by
    simpa [prefixWord, tailWord_3338910, baseEnd_3338910] using wordTrace_append hprefix tailTrace_3338910
  have hstable : (prefixWord ++ tailWord_3338910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338910).length < 2 ^ (prefixWord ++ tailWord_3338910).sum := by decide
  have hdescent : baseEnd_3338910 < baseStart_3338910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3338952 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3338952 : Nat := 118140960795 + 3338952 * 2 ^ 59
def prefixEnd_3338952 : Nat := 4983230072969 + 3 ^ 40 * 3338952 * 2
def baseEnd_3338952 : Nat := 1714487258291125568644445

theorem tailTrace_3338952 : CollatzResearch.WordTrace tailWord_3338952 prefixEnd_3338952 1714487258291125568644445 := by
  unfold tailWord_3338952
  simp only [CollatzResearch.WordTrace]
  refine ⟨60890792099777313223489555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81187722799703084297986073 60890792099777313223489555)
  ·
    refine ⟨91336188149665969835234333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60890792099777313223489555 91336188149665969835234333)
    ·
      refine ⟨34251070556124738688212875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91336188149665969835234333 34251070556124738688212875)
      ·
        refine ⟨51376605834187108032319313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34251070556124738688212875 51376605834187108032319313)
        ·
          refine ⟨38532454375640331024239485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51376605834187108032319313 38532454375640331024239485)
          ·
            refine ⟨14449670390865124134089807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38532454375640331024239485 14449670390865124134089807)
            ·
              refine ⟨21674505586297686201134711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14449670390865124134089807 21674505586297686201134711)
              ·
                refine ⟨32511758379446529301702067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21674505586297686201134711 32511758379446529301702067)
                ·
                  refine ⟨48767637569169793952553101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32511758379446529301702067 48767637569169793952553101)
                  ·
                    refine ⟨18287864088438672732207413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48767637569169793952553101 18287864088438672732207413)
                    ·
                      refine ⟨1714487258291125568644445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18287864088438672732207413 1714487258291125568644445)
                      ·
                        rfl

theorem cell23_3338952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3338952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3338952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3338952 prefixEnd_3338952 := by exact prefixLift 3338952
  have htrace : WordTrace (prefixWord ++ tailWord_3338952) baseStart_3338952 baseEnd_3338952 := by
    simpa [prefixWord, tailWord_3338952, baseEnd_3338952] using wordTrace_append hprefix tailTrace_3338952
  have hstable : (prefixWord ++ tailWord_3338952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3338952).length < 2 ^ (prefixWord ++ tailWord_3338952).sum := by decide
  have hdescent : baseEnd_3338952 < baseStart_3338952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3338952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339002 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_3339002 : Nat := 118140960795 + 3339002 * 2 ^ 59
def prefixEnd_3339002 : Nat := 4983230072969 + 3 ^ 40 * 3339002 * 2
def baseEnd_3339002 : Nat := 571504310774616791006405

theorem tailTrace_3339002 : CollatzResearch.WordTrace tailWord_3339002 prefixEnd_3339002 571504310774616791006405 := by
  unfold tailWord_3339002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445851962343371246574815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81188938566248989990866173 30445851962343371246574815)
  ·
    refine ⟨45668777943515056869862223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30445851962343371246574815 45668777943515056869862223)
    ·
      refine ⟨68503166915272585304793335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45668777943515056869862223 68503166915272585304793335)
      ·
        refine ⟨102754750372908877957190003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68503166915272585304793335 102754750372908877957190003)
        ·
          refine ⟨154132125559363316935785005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102754750372908877957190003 154132125559363316935785005)
          ·
            refine ⟨57799547084761243850919377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154132125559363316935785005 57799547084761243850919377)
            ·
              refine ⟨43349660313570932888189533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57799547084761243850919377 43349660313570932888189533)
              ·
                refine ⟨16256122617589099833071075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43349660313570932888189533 16256122617589099833071075)
                ·
                  refine ⟨24384183926383649749606613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256122617589099833071075 24384183926383649749606613)
                  ·
                    refine ⟨571504310774616791006405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24384183926383649749606613 571504310774616791006405)
                    ·
                      rfl

theorem cell23_3339002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_3339002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339002 prefixEnd_3339002 := by exact prefixLift 3339002
  have htrace : WordTrace (prefixWord ++ tailWord_3339002) baseStart_3339002 baseEnd_3339002 := by
    simpa [prefixWord, tailWord_3339002, baseEnd_3339002] using wordTrace_append hprefix tailTrace_3339002
  have hstable : (prefixWord ++ tailWord_3339002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339002).length < 2 ^ (prefixWord ++ tailWord_3339002).sum := by decide
  have hdescent : baseEnd_3339002 < baseStart_3339002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339032 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_3339032 : Nat := 118140960795 + 3339032 * 2 ^ 59
def prefixEnd_3339032 : Nat := 4983230072969 + 3 ^ 40 * 3339032 * 2
def baseEnd_3339032 : Nat := 571509445581161751881359

theorem tailTrace_3339032 : CollatzResearch.WordTrace tailWord_3339032 prefixEnd_3339032 571509445581161751881359 := by
  unfold tailWord_3339032
  simp only [CollatzResearch.WordTrace]
  refine ⟨60892251019632400054945675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81189668026176533406594233 60892251019632400054945675)
  ·
    refine ⟨91338376529448600082418513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60892251019632400054945675 91338376529448600082418513)
    ·
      refine ⟨68503782397086450061813885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91338376529448600082418513 68503782397086450061813885)
      ·
        refine ⟨25688918398907418773180207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68503782397086450061813885 25688918398907418773180207)
        ·
          refine ⟨38533377598361128159770311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25688918398907418773180207 38533377598361128159770311)
          ·
            refine ⟨57800066397541692239655467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38533377598361128159770311 57800066397541692239655467)
            ·
              refine ⟨86700099596312538359483201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57800066397541692239655467 86700099596312538359483201)
              ·
                refine ⟨65025074697234403769612401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86700099596312538359483201 65025074697234403769612401)
                ·
                  refine ⟨48768806022925802827209301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65025074697234403769612401 48768806022925802827209301)
                  ·
                    refine ⟨571509445581161751881359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48768806022925802827209301 571509445581161751881359)
                    ·
                      rfl

theorem cell23_3339032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_3339032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339032 prefixEnd_3339032 := by exact prefixLift 3339032
  have htrace : WordTrace (prefixWord ++ tailWord_3339032) baseStart_3339032 baseEnd_3339032 := by
    simpa [prefixWord, tailWord_3339032, baseEnd_3339032] using wordTrace_append hprefix tailTrace_3339032
  have hstable : (prefixWord ++ tailWord_3339032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339032).length < 2 ^ (prefixWord ++ tailWord_3339032).sum := by decide
  have hdescent : baseEnd_3339032 < baseStart_3339032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339049 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_3339049 : Nat := 118140960795 + 3339049 * 2 ^ 59
def prefixEnd_3339049 : Nat := 4983230072969 + 3 ^ 40 * 3339049 * 2
def baseEnd_3339049 : Nat := 571512355304870563043833

theorem tailTrace_3339049 : CollatzResearch.WordTrace tailWord_3339049 prefixEnd_3339049 571512355304870563043833 := by
  unfold tailWord_3339049
  simp only [CollatzResearch.WordTrace]
  refine ⟨121785122080203212013260201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81190081386802141342173467 121785122080203212013260201)
  ·
    refine ⟨91338841560152409009945151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121785122080203212013260201 91338841560152409009945151)
    ·
      refine ⟨137008262340228613514917727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91338841560152409009945151 137008262340228613514917727)
      ·
        refine ⟨205512393510342920272376591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137008262340228613514917727 205512393510342920272376591)
        ·
          refine ⟨308268590265514380408564887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205512393510342920272376591 308268590265514380408564887)
          ·
            refine ⟨462402885398271570612847331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308268590265514380408564887 462402885398271570612847331)
            ·
              refine ⟨693604328097407355919270997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462402885398271570612847331 693604328097407355919270997)
              ·
                refine ⟨8128175719891492452178957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 693604328097407355919270997 8128175719891492452178957)
                ·
                  refine ⟨3048065894959309669567109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8128175719891492452178957 3048065894959309669567109)
                  ·
                    refine ⟨571512355304870563043833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3048065894959309669567109 571512355304870563043833)
                    ·
                      rfl

theorem cell23_3339049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_3339049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339049 prefixEnd_3339049 := by exact prefixLift 3339049
  have htrace : WordTrace (prefixWord ++ tailWord_3339049) baseStart_3339049 baseEnd_3339049 := by
    simpa [prefixWord, tailWord_3339049, baseEnd_3339049] using wordTrace_append hprefix tailTrace_3339049
  have hstable : (prefixWord ++ tailWord_3339049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339049).length < 2 ^ (prefixWord ++ tailWord_3339049).sum := by decide
  have hdescent : baseEnd_3339049 < baseStart_3339049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339053 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3339053 : Nat := 118140960795 + 3339053 * 2 ^ 59
def prefixEnd_3339053 : Nat := 4983230072969 + 3 ^ 40 * 3339053 * 2
def baseEnd_3339053 : Nat := 571513039945743224493827

theorem tailTrace_3339053 : CollatzResearch.WordTrace tailWord_3339053 prefixEnd_3339053 571513039945743224493827 := by
  unfold tailWord_3339053
  simp only [CollatzResearch.WordTrace]
  refine ⟨121785267972188720696405813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81190178648125813797603875 121785267972188720696405813)
  ·
    refine ⟨11417368872392692565288045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121785267972188720696405813 11417368872392692565288045)
    ·
      refine ⟨4281513327147259711983017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11417368872392692565288045 4281513327147259711983017)
      ·
        refine ⟨3211134995360444783987263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4281513327147259711983017 3211134995360444783987263)
        ·
          refine ⟨4816702493040667175980895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211134995360444783987263 4816702493040667175980895)
          ·
            refine ⟨7225053739561000763971343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816702493040667175980895 7225053739561000763971343)
            ·
              refine ⟨10837580609341501145957015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7225053739561000763971343 10837580609341501145957015)
              ·
                refine ⟨16256370914012251718935523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837580609341501145957015 16256370914012251718935523)
                ·
                  refine ⟨24384556371018377578403285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256370914012251718935523 24384556371018377578403285)
                  ·
                    refine ⟨571513039945743224493827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24384556371018377578403285 571513039945743224493827)
                    ·
                      rfl

theorem cell23_3339053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3339053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339053 prefixEnd_3339053 := by exact prefixLift 3339053
  have htrace : WordTrace (prefixWord ++ tailWord_3339053) baseStart_3339053 baseEnd_3339053 := by
    simpa [prefixWord, tailWord_3339053, baseEnd_3339053] using wordTrace_append hprefix tailTrace_3339053
  have hstable : (prefixWord ++ tailWord_3339053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339053).length < 2 ^ (prefixWord ++ tailWord_3339053).sum := by decide
  have hdescent : baseEnd_3339053 < baseStart_3339053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339109 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_3339109 : Nat := 118140960795 + 3339109 * 2 ^ 59
def prefixEnd_3339109 : Nat := 4983230072969 + 3 ^ 40 * 3339109 * 2
def baseEnd_3339109 : Nat := 571522624917960484793741

theorem tailTrace_3339109 : CollatzResearch.WordTrace tailWord_3339109 prefixEnd_3339109 571522624917960484793741 := by
  unfold tailWord_3339109
  simp only [CollatzResearch.WordTrace]
  refine ⟨121787310459985842260444381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81191540306657228173629587 121787310459985842260444381)
  ·
    refine ⟨45670241422494690847666643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121787310459985842260444381 45670241422494690847666643)
    ·
      refine ⟨68505362133742036271499965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45670241422494690847666643 68505362133742036271499965)
      ·
        refine ⟨25689510800153263601812487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68505362133742036271499965 25689510800153263601812487)
        ·
          refine ⟨38534266200229895402718731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25689510800153263601812487 38534266200229895402718731)
          ·
            refine ⟨57801399300344843104078097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38534266200229895402718731 57801399300344843104078097)
            ·
              refine ⟨43351049475258632328058573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57801399300344843104078097 43351049475258632328058573)
              ·
                refine ⟨16256643553221987123021965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43351049475258632328058573 16256643553221987123021965)
                ·
                  refine ⟨6096241332458245171133237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16256643553221987123021965 6096241332458245171133237)
                  ·
                    refine ⟨571522624917960484793741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6096241332458245171133237 571522624917960484793741)
                    ·
                      rfl

theorem cell23_3339109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_3339109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339109 prefixEnd_3339109 := by exact prefixLift 3339109
  have htrace : WordTrace (prefixWord ++ tailWord_3339109) baseStart_3339109 baseEnd_3339109 := by
    simpa [prefixWord, tailWord_3339109, baseEnd_3339109] using wordTrace_append hprefix tailTrace_3339109
  have hstable : (prefixWord ++ tailWord_3339109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339109).length < 2 ^ (prefixWord ++ tailWord_3339109).sum := by decide
  have hdescent : baseEnd_3339109 < baseStart_3339109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339116 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 1, 5, 2]
def baseStart_3339116 : Nat := 118140960795 + 3339116 * 2 ^ 59
def prefixEnd_3339116 : Nat := 4983230072969 + 3 ^ 40 * 3339116 * 2
def baseEnd_3339116 : Nat := 1714571469118462926993691

theorem tailTrace_3339116 : CollatzResearch.WordTrace tailWord_3339116 prefixEnd_3339116 1714571469118462926993691 := by
  unfold tailWord_3339116
  simp only [CollatzResearch.WordTrace]
  refine ⟨60893782885480241227974601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81191710513973654970632801 60893782885480241227974601)
  ·
    refine ⟨45670337164110180920980951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60893782885480241227974601 45670337164110180920980951)
    ·
      refine ⟨68505505746165271381471427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45670337164110180920980951 68505505746165271381471427)
      ·
        refine ⟨102758258619247907072207141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68505505746165271381471427 102758258619247907072207141)
        ·
          refine ⟨19267173491108982576038839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102758258619247907072207141 19267173491108982576038839)
          ·
            refine ⟨28900760236663473864058259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267173491108982576038839 28900760236663473864058259)
            ·
              refine ⟨43351140354995210796087389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28900760236663473864058259 43351140354995210796087389)
              ·
                refine ⟨16256677633123204048532771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43351140354995210796087389 16256677633123204048532771)
                ·
                  refine ⟨24385016449684806072799157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256677633123204048532771 24385016449684806072799157)
                  ·
                    refine ⟨2286095292157950569324921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24385016449684806072799157 2286095292157950569324921)
                    ·
                      refine ⟨1714571469118462926993691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286095292157950569324921 1714571469118462926993691)
                      ·
                        rfl

theorem cell23_3339116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_3339116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339116 prefixEnd_3339116 := by exact prefixLift 3339116
  have htrace : WordTrace (prefixWord ++ tailWord_3339116) baseStart_3339116 baseEnd_3339116 := by
    simpa [prefixWord, tailWord_3339116, baseEnd_3339116] using wordTrace_append hprefix tailTrace_3339116
  have hstable : (prefixWord ++ tailWord_3339116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339116).length < 2 ^ (prefixWord ++ tailWord_3339116).sum := by decide
  have hdescent : baseEnd_3339116 < baseStart_3339116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339134 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3339134 : Nat := 118140960795 + 3339134 * 2 ^ 59
def prefixEnd_3339134 : Nat := 4983230072969 + 3 ^ 40 * 3339134 * 2
def baseEnd_3339134 : Nat := 571526903923414618856203

theorem tailTrace_3339134 : CollatzResearch.WordTrace tailWord_3339134 prefixEnd_3339134 571526903923414618856203 := by
  unfold tailWord_3339134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223527785611908941263057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81192148189930181020069637 15223527785611908941263057)
  ·
    refine ⟨11417645839208931705947293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15223527785611908941263057 11417645839208931705947293)
    ·
      refine ⟨4281617189703349389730235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11417645839208931705947293 4281617189703349389730235)
      ·
        refine ⟨6422425784555024084595353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281617189703349389730235 6422425784555024084595353)
        ·
          refine ⟨4816819338416268063446515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6422425784555024084595353 4816819338416268063446515)
          ·
            refine ⟨7225229007624402095169773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816819338416268063446515 7225229007624402095169773)
            ·
              refine ⟨2709460877859150785688665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7225229007624402095169773 2709460877859150785688665)
              ·
                refine ⟨2032095658394363089266499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2709460877859150785688665 2032095658394363089266499)
                ·
                  refine ⟨3048143487591544633899749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032095658394363089266499 3048143487591544633899749)
                  ·
                    refine ⟨571526903923414618856203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3048143487591544633899749 571526903923414618856203)
                    ·
                      rfl

theorem cell23_3339134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3339134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339134 prefixEnd_3339134 := by exact prefixLift 3339134
  have htrace : WordTrace (prefixWord ++ tailWord_3339134) baseStart_3339134 baseEnd_3339134 := by
    simpa [prefixWord, tailWord_3339134, baseEnd_3339134] using wordTrace_append hprefix tailTrace_3339134
  have hstable : (prefixWord ++ tailWord_3339134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339134).length < 2 ^ (prefixWord ++ tailWord_3339134).sum := by decide
  have hdescent : baseEnd_3339134 < baseStart_3339134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339156 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3339156 : Nat := 118140960795 + 3339156 * 2 ^ 59
def prefixEnd_3339156 : Nat := 4983230072969 + 3 ^ 40 * 3339156 * 2
def baseEnd_3339156 : Nat := 571530669448214256831169

theorem tailTrace_3339156 : CollatzResearch.WordTrace tailWord_3339156 prefixEnd_3339156 571530669448214256831169 := by
  unfold tailWord_3339156
  simp only [CollatzResearch.WordTrace]
  refine ⟨60894512345407784643702661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81192683127210379524936881 60894512345407784643702661)
  ·
    refine ⟨11417721064763959620694249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60894512345407784643702661 11417721064763959620694249)
    ·
      refine ⟨8563290798572969715520687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11417721064763959620694249 8563290798572969715520687)
      ·
        refine ⟨12844936197859454573281031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8563290798572969715520687 12844936197859454573281031)
        ·
          refine ⟨19267404296789181859921547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12844936197859454573281031 19267404296789181859921547)
          ·
            refine ⟨28901106445183772789882321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267404296789181859921547 28901106445183772789882321)
            ·
              refine ⟨21675829833887829592411741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28901106445183772789882321 21675829833887829592411741)
              ·
                refine ⟨8128436187707936097154403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21675829833887829592411741 8128436187707936097154403)
                ·
                  refine ⟨12192654281561904145731605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8128436187707936097154403 12192654281561904145731605)
                  ·
                    refine ⟨571530669448214256831169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12192654281561904145731605 571530669448214256831169)
                    ·
                      rfl

theorem cell23_3339156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3339156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339156 prefixEnd_3339156 := by exact prefixLift 3339156
  have htrace : WordTrace (prefixWord ++ tailWord_3339156) baseStart_3339156 baseEnd_3339156 := by
    simpa [prefixWord, tailWord_3339156, baseEnd_3339156] using wordTrace_append hprefix tailTrace_3339156
  have hstable : (prefixWord ++ tailWord_3339156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339156).length < 2 ^ (prefixWord ++ tailWord_3339156).sum := by decide
  have hdescent : baseEnd_3339156 < baseStart_3339156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339159 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3339159 : Nat := 118140960795 + 3339159 * 2 ^ 59
def prefixEnd_3339159 : Nat := 4983230072969 + 3 ^ 40 * 3339159 * 2
def baseEnd_3339159 : Nat := 1714593548786606258755993

theorem tailTrace_3339159 : CollatzResearch.WordTrace tailWord_3339159 prefixEnd_3339159 1714593548786606258755993 := by
  unfold tailWord_3339159
  simp only [CollatzResearch.WordTrace]
  refine ⟨121789134109804700799764531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81192756073203133866509687 121789134109804700799764531)
  ·
    refine ⟨182683701164707051199646797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121789134109804700799764531 182683701164707051199646797)
    ·
      refine ⟨68506387936765144199867549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182683701164707051199646797 68506387936765144199867549)
      ·
        refine ⟨25689895476286929074950331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68506387936765144199867549 25689895476286929074950331)
        ·
          refine ⟨38534843214430393612425497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25689895476286929074950331 38534843214430393612425497)
          ·
            refine ⟨28901132410822795209319123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38534843214430393612425497 28901132410822795209319123)
            ·
              refine ⟨43351698616234192813978685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28901132410822795209319123 43351698616234192813978685)
              ·
                refine ⟨16256886981087822305242007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43351698616234192813978685 16256886981087822305242007)
                ·
                  refine ⟨24385330471631733457863011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16256886981087822305242007 24385330471631733457863011)
                  ·
                    refine ⟨36577995707447600186794517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24385330471631733457863011 36577995707447600186794517)
                    ·
                      refine ⟨1714593548786606258755993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36577995707447600186794517 1714593548786606258755993)
                      ·
                        rfl

theorem cell23_3339159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3339159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339159 prefixEnd_3339159 := by exact prefixLift 3339159
  have htrace : WordTrace (prefixWord ++ tailWord_3339159) baseStart_3339159 baseEnd_3339159 := by
    simpa [prefixWord, tailWord_3339159, baseEnd_3339159] using wordTrace_append hprefix tailTrace_3339159
  have hstable : (prefixWord ++ tailWord_3339159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339159).length < 2 ^ (prefixWord ++ tailWord_3339159).sum := by decide
  have hdescent : baseEnd_3339159 < baseStart_3339159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339234 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3339234 : Nat := 118140960795 + 3339234 * 2 ^ 59
def prefixEnd_3339234 : Nat := 4983230072969 + 3 ^ 40 * 3339234 * 2
def baseEnd_3339234 : Nat := 1714632059835693465318149

theorem tailTrace_3339234 : CollatzResearch.WordTrace tailWord_3339234 prefixEnd_3339234 1714632059835693465318149 := by
  unfold tailWord_3339234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30447967396133247152186189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81194579723021992405829837 30447967396133247152186189)
  ·
    refine ⟨11417987773549967682069821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30447967396133247152186189 11417987773549967682069821)
    ·
      refine ⟨4281745415081237880776183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11417987773549967682069821 4281745415081237880776183)
      ·
        refine ⟨6422618122621856821164275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281745415081237880776183 6422618122621856821164275)
        ·
          refine ⟨9633927183932785231746413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422618122621856821164275 9633927183932785231746413)
          ·
            refine ⟨3612722693974794461904905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9633927183932785231746413 3612722693974794461904905)
            ·
              refine ⟨2709542020481095846428679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612722693974794461904905 2709542020481095846428679)
              ·
                refine ⟨4064313030721643769643019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709542020481095846428679 4064313030721643769643019)
                ·
                  refine ⟨6096469546082465654464529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064313030721643769643019 6096469546082465654464529)
                  ·
                    refine ⟨4572352159561849240848397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096469546082465654464529 4572352159561849240848397)
                    ·
                      refine ⟨1714632059835693465318149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4572352159561849240848397 1714632059835693465318149)
                      ·
                        rfl

theorem cell23_3339234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3339234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339234 prefixEnd_3339234 := by exact prefixLift 3339234
  have htrace : WordTrace (prefixWord ++ tailWord_3339234) baseStart_3339234 baseEnd_3339234 := by
    simpa [prefixWord, tailWord_3339234, baseEnd_3339234] using wordTrace_append hprefix tailTrace_3339234
  have hstable : (prefixWord ++ tailWord_3339234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339234).length < 2 ^ (prefixWord ++ tailWord_3339234).sum := by decide
  have hdescent : baseEnd_3339234 < baseStart_3339234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339276 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 7]
def baseStart_3339276 : Nat := 118140960795 + 3339276 * 2 ^ 59
def prefixEnd_3339276 : Nat := 4983230072969 + 3 ^ 40 * 3339276 * 2
def baseEnd_3339276 : Nat := 190517069558131366776995

theorem tailTrace_3339276 : CollatzResearch.WordTrace tailWord_3339276 prefixEnd_3339276 190517069558131366776995 := by
  unfold tailWord_3339276
  simp only [CollatzResearch.WordTrace]
  refine ⟨60896700725190414890886841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81195600966920553187849121 60896700725190414890886841)
  ·
    refine ⟨45672525543892811168165131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60896700725190414890886841 45672525543892811168165131)
    ·
      refine ⟨68508788315839216752247697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45672525543892811168165131 68508788315839216752247697)
      ·
        refine ⟨51381591236879412564185773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68508788315839216752247697 51381591236879412564185773)
        ·
          refine ⟨19268096713829779711569665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51381591236879412564185773 19268096713829779711569665)
          ·
            refine ⟨14451072535372334783677249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19268096713829779711569665 14451072535372334783677249)
            ·
              refine ⟨10838304401529251087757937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14451072535372334783677249 10838304401529251087757937)
              ·
                refine ⟨8128728301146938315818453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10838304401529251087757937 8128728301146938315818453)
                ·
                  refine ⟨190517069558131366776995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8128728301146938315818453 190517069558131366776995)
                  ·
                    rfl

theorem cell23_3339276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_3339276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339276 prefixEnd_3339276 := by exact prefixLift 3339276
  have htrace : WordTrace (prefixWord ++ tailWord_3339276) baseStart_3339276 baseEnd_3339276 := by
    simpa [prefixWord, tailWord_3339276, baseEnd_3339276] using wordTrace_append hprefix tailTrace_3339276
  have hstable : (prefixWord ++ tailWord_3339276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339276).length < 2 ^ (prefixWord ++ tailWord_3339276).sum := by decide
  have hdescent : baseEnd_3339276 < baseStart_3339276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339279 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_3339279 : Nat := 118140960795 + 3339279 * 2 ^ 59
def prefixEnd_3339279 : Nat := 4983230072969 + 3 ^ 40 * 3339279 * 2
def baseEnd_3339279 : Nat := 1714655166465145789255441

theorem tailTrace_3339279 : CollatzResearch.WordTrace tailWord_3339279 prefixEnd_3339279 1714655166465145789255441 := by
  unfold tailWord_3339279
  simp only [CollatzResearch.WordTrace]
  refine ⟨121793510869369961294132891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81195673912913307529421927 121793510869369961294132891)
  ·
    refine ⟨182690266304054941941199337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121793510869369961294132891 182690266304054941941199337)
    ·
      refine ⟨137017699728041206455899503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182690266304054941941199337 137017699728041206455899503)
      ·
        refine ⟨205526549592061809683849255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137017699728041206455899503 205526549592061809683849255)
        ·
          refine ⟨308289824388092714525773883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205526549592061809683849255 308289824388092714525773883)
          ·
            refine ⟨462434736582139071788660825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308289824388092714525773883 462434736582139071788660825)
            ·
              refine ⟨346826052436604303841495619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462434736582139071788660825 346826052436604303841495619)
              ·
                refine ⟨520239078654906455762243429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346826052436604303841495619 520239078654906455762243429)
                ·
                  refine ⟨97544827247794960455420643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 520239078654906455762243429 97544827247794960455420643)
                  ·
                    refine ⟨146317240871692440683130965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97544827247794960455420643 146317240871692440683130965)
                    ·
                      refine ⟨1714655166465145789255441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146317240871692440683130965 1714655166465145789255441)
                      ·
                        rfl

theorem cell23_3339279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_3339279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339279 prefixEnd_3339279 := by exact prefixLift 3339279
  have htrace : WordTrace (prefixWord ++ tailWord_3339279) baseStart_3339279 baseEnd_3339279 := by
    simpa [prefixWord, tailWord_3339279, baseEnd_3339279] using wordTrace_append hprefix tailTrace_3339279
  have hstable : (prefixWord ++ tailWord_3339279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339279).length < 2 ^ (prefixWord ++ tailWord_3339279).sum := by decide
  have hdescent : baseEnd_3339279 < baseStart_3339279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339313 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_3339313 : Nat := 118140960795 + 3339313 * 2 ^ 59
def prefixEnd_3339313 : Nat := 4983230072969 + 3 ^ 40 * 3339313 * 2
def baseEnd_3339313 : Nat := 1714672624807398656230285

theorem tailTrace_3339313 : CollatzResearch.WordTrace tailWord_3339313 prefixEnd_3339313 1714672624807398656230285 := by
  unfold tailWord_3339313
  simp only [CollatzResearch.WordTrace]
  refine ⟨121794750951246785100870593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81196500634164523400580395 121794750951246785100870593)
  ·
    refine ⟨91346063213435088825652945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121794750951246785100870593 91346063213435088825652945)
    ·
      refine ⟨68509547410076316619239709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91346063213435088825652945 68509547410076316619239709)
      ·
        refine ⟨25691080278778618732214891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68509547410076316619239709 25691080278778618732214891)
        ·
          refine ⟨38536620418167928098322337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25691080278778618732214891 38536620418167928098322337)
          ·
            refine ⟨28902465313625946073741753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38536620418167928098322337 28902465313625946073741753)
            ·
              refine ⟨21676848985219459555306315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28902465313625946073741753 21676848985219459555306315)
              ·
                refine ⟨32515273477829189332959473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21676848985219459555306315 32515273477829189332959473)
                ·
                  refine ⟨24386455108371891999719605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32515273477829189332959473 24386455108371891999719605)
                  ·
                    refine ⟨2286230166409864874973713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24386455108371891999719605 2286230166409864874973713)
                    ·
                      refine ⟨1714672624807398656230285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286230166409864874973713 1714672624807398656230285)
                      ·
                        rfl

theorem cell23_3339313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_3339313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339313 prefixEnd_3339313 := by exact prefixLift 3339313
  have htrace : WordTrace (prefixWord ++ tailWord_3339313) baseStart_3339313 baseEnd_3339313 := by
    simpa [prefixWord, tailWord_3339313, baseEnd_3339313] using wordTrace_append hprefix tailTrace_3339313
  have hstable : (prefixWord ++ tailWord_3339313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339313).length < 2 ^ (prefixWord ++ tailWord_3339313).sum := by decide
  have hdescent : baseEnd_3339313 < baseStart_3339313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339397 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 3]
def baseStart_3339397 : Nat := 118140960795 + 3339397 * 2 ^ 59
def prefixEnd_3339397 : Nat := 4983230072969 + 3 ^ 40 * 3339397 * 2
def baseEnd_3339397 : Nat := 1714715757182376327579899

theorem tailTrace_3339397 : CollatzResearch.WordTrace tailWord_3339397 prefixEnd_3339397 1714715757182376327579899 := by
  unfold tailWord_3339397
  simp only [CollatzResearch.WordTrace]
  refine ⟨121797814682942467446928445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81198543121961644964618963 121797814682942467446928445)
  ·
    refine ⟨45674180506103425292598167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121797814682942467446928445 45674180506103425292598167)
    ·
      refine ⟨68511270759155137938897251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45674180506103425292598167 68511270759155137938897251)
      ·
        refine ⟨102766906138732706908345877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68511270759155137938897251 102766906138732706908345877)
        ·
          refine ⟨4817198725253095636328713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102766906138732706908345877 4817198725253095636328713)
          ·
            refine ⟨3612899043939821727246535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817198725253095636328713 3612899043939821727246535)
            ·
              refine ⟨5419348565909732590869803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612899043939821727246535 5419348565909732590869803)
              ·
                refine ⟨8129022848864598886304705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419348565909732590869803 8129022848864598886304705)
                ·
                  refine ⟨6096767136648449164728529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8129022848864598886304705 6096767136648449164728529)
                  ·
                    refine ⟨4572575352486336873546397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6096767136648449164728529 4572575352486336873546397)
                    ·
                      refine ⟨1714715757182376327579899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4572575352486336873546397 1714715757182376327579899)
                      ·
                        rfl

theorem cell23_3339397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_3339397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339397 prefixEnd_3339397 := by exact prefixLift 3339397
  have htrace : WordTrace (prefixWord ++ tailWord_3339397) baseStart_3339397 baseEnd_3339397 := by
    simpa [prefixWord, tailWord_3339397, baseEnd_3339397] using wordTrace_append hprefix tailTrace_3339397
  have hstable : (prefixWord ++ tailWord_3339397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339397).length < 2 ^ (prefixWord ++ tailWord_3339397).sum := by decide
  have hdescent : baseEnd_3339397 < baseStart_3339397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339443 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 1, 6]
def baseStart_3339443 : Nat := 118140960795 + 3339443 * 2 ^ 59
def prefixEnd_3339443 : Nat := 4983230072969 + 3 ^ 40 * 3339443 * 2
def baseEnd_3339443 : Nat := 571579792430827715868229

theorem tailTrace_3339443 : CollatzResearch.WordTrace tailWord_3339443 prefixEnd_3339443 571579792430827715868229 := by
  unfold tailWord_3339443
  simp only [CollatzResearch.WordTrace]
  refine ⟨121799492440775817303102983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81199661627183878202068655 121799492440775817303102983)
  ·
    refine ⟨182699238661163725954654475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121799492440775817303102983 182699238661163725954654475)
    ·
      refine ⟨274048857991745588931981713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182699238661163725954654475 274048857991745588931981713)
      ·
        refine ⟨205536643493809191698986285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274048857991745588931981713 205536643493809191698986285)
        ·
          refine ⟨77076241310178446887119857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205536643493809191698986285 77076241310178446887119857)
          ·
            refine ⟨57807180982633835165339893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77076241310178446887119857 57807180982633835165339893)
            ·
              refine ⟨5419423217121922046750615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57807180982633835165339893 5419423217121922046750615)
              ·
                refine ⟨8129134825682883070125923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419423217121922046750615 8129134825682883070125923)
                ·
                  refine ⟨12193702238524324605188885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129134825682883070125923 12193702238524324605188885)
                  ·
                    refine ⟨571579792430827715868229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12193702238524324605188885 571579792430827715868229)
                    ·
                      rfl

theorem cell23_3339443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 6].length) (baseStart_3339443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339443 prefixEnd_3339443 := by exact prefixLift 3339443
  have htrace : WordTrace (prefixWord ++ tailWord_3339443) baseStart_3339443 baseEnd_3339443 := by
    simpa [prefixWord, tailWord_3339443, baseEnd_3339443] using wordTrace_append hprefix tailTrace_3339443
  have hstable : (prefixWord ++ tailWord_3339443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339443).length < 2 ^ (prefixWord ++ tailWord_3339443).sum := by decide
  have hdescent : baseEnd_3339443 < baseStart_3339443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339463 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_3339463 : Nat := 118140960795 + 3339463 * 2 ^ 59
def prefixEnd_3339463 : Nat := 4983230072969 + 3 ^ 40 * 3339463 * 2
def baseEnd_3339463 : Nat := 1714749646905573069354595

theorem tailTrace_3339463 : CollatzResearch.WordTrace tailWord_3339463 prefixEnd_3339463 1714749646905573069354595 := by
  unfold tailWord_3339463
  simp only [CollatzResearch.WordTrace]
  refine ⟨121800221900703360718831043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81200147933802240479220695 121800221900703360718831043)
  ·
    refine ⟨182700332851055041078246565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121800221900703360718831043 182700332851055041078246565)
    ·
      refine ⟨34256312409572820202171231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182700332851055041078246565 34256312409572820202171231)
      ·
        refine ⟨51384468614359230303256847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34256312409572820202171231 51384468614359230303256847)
        ·
          refine ⟨77076702921538845454885271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51384468614359230303256847 77076702921538845454885271)
          ·
            refine ⟨115615054382308268182327907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77076702921538845454885271 115615054382308268182327907)
            ·
              refine ⟨173422581573462402273491861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115615054382308268182327907 173422581573462402273491861)
              ·
                refine ⟨8129183511256050106569931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173422581573462402273491861 8129183511256050106569931)
                ·
                  refine ⟨12193775266884075159854897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129183511256050106569931 12193775266884075159854897)
                  ·
                    refine ⟨9145331450163056369891173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12193775266884075159854897 9145331450163056369891173)
                    ·
                      refine ⟨1714749646905573069354595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9145331450163056369891173 1714749646905573069354595)
                      ·
                        rfl

theorem cell23_3339463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_3339463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339463 prefixEnd_3339463 := by exact prefixLift 3339463
  have htrace : WordTrace (prefixWord ++ tailWord_3339463) baseStart_3339463 baseEnd_3339463 := by
    simpa [prefixWord, tailWord_3339463, baseEnd_3339463] using wordTrace_append hprefix tailTrace_3339463
  have hstable : (prefixWord ++ tailWord_3339463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339463).length < 2 ^ (prefixWord ++ tailWord_3339463).sum := by decide
  have hdescent : baseEnd_3339463 < baseStart_3339463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339478 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3339478 : Nat := 118140960795 + 3339478 * 2 ^ 59
def prefixEnd_3339478 : Nat := 4983230072969 + 3 ^ 40 * 3339478 * 2
def baseEnd_3339478 : Nat := 1714757349115390510667027

theorem tailTrace_3339478 : CollatzResearch.WordTrace tailWord_3339478 prefixEnd_3339478 1714757349115390510667027 := by
  unfold tailWord_3339478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612548062228063642539193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81200512663766012187084725 7612548062228063642539193)
  ·
    refine ⟨5709411046671047731904395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7612548062228063642539193 5709411046671047731904395)
    ·
      refine ⟨8564116570006571597856593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709411046671047731904395 8564116570006571597856593)
      ·
        refine ⟨6423087427504928698392445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8564116570006571597856593 6423087427504928698392445)
        ·
          refine ⟨2408657785314348261897167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6423087427504928698392445 2408657785314348261897167)
          ·
            refine ⟨3612986677971522392845751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408657785314348261897167 3612986677971522392845751)
            ·
              refine ⟨5419480016957283589268627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612986677971522392845751 5419480016957283589268627)
              ·
                refine ⟨8129220025435925383902941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419480016957283589268627 8129220025435925383902941)
                ·
                  refine ⟨3048457509538472018963603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8129220025435925383902941 3048457509538472018963603)
                  ·
                    refine ⟨4572686264307708028445405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3048457509538472018963603 4572686264307708028445405)
                    ·
                      refine ⟨1714757349115390510667027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4572686264307708028445405 1714757349115390510667027)
                      ·
                        rfl

theorem cell23_3339478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3339478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339478 prefixEnd_3339478 := by exact prefixLift 3339478
  have htrace : WordTrace (prefixWord ++ tailWord_3339478) baseStart_3339478 baseEnd_3339478 := by
    simpa [prefixWord, tailWord_3339478, baseEnd_3339478] using wordTrace_append hprefix tailTrace_3339478
  have hstable : (prefixWord ++ tailWord_3339478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339478).length < 2 ^ (prefixWord ++ tailWord_3339478).sum := by decide
  have hdescent : baseEnd_3339478 < baseStart_3339478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339534 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3339534 : Nat := 118140960795 + 3339534 * 2 ^ 59
def prefixEnd_3339534 : Nat := 4983230072969 + 3 ^ 40 * 3339534 * 2
def baseEnd_3339534 : Nat := 1714786104032042291566769

theorem tailTrace_3339534 : CollatzResearch.WordTrace tailWord_3339534 prefixEnd_3339534 1714786104032042291566769 := by
  unfold tailWord_3339534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15225351435430767480583207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81201874322297426563110437 15225351435430767480583207)
  ·
    refine ⟨22838027153146151220874811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15225351435430767480583207 22838027153146151220874811)
    ·
      refine ⟨34257040729719226831312217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22838027153146151220874811 34257040729719226831312217)
      ·
        refine ⟨25692780547289420123484163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34257040729719226831312217 25692780547289420123484163)
        ·
          refine ⟨38539170820934130185226245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25692780547289420123484163 38539170820934130185226245)
          ·
            refine ⟨7226094528925149409729921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38539170820934130185226245 7226094528925149409729921)
            ·
              refine ⟨5419570896693862057297441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7226094528925149409729921 5419570896693862057297441)
              ·
                refine ⟨4064678172520396542973081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419570896693862057297441 4064678172520396542973081)
                ·
                  refine ⟨3048508629390297407229811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064678172520396542973081 3048508629390297407229811)
                  ·
                    refine ⟨4572762944085446110844717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3048508629390297407229811 4572762944085446110844717)
                    ·
                      refine ⟨1714786104032042291566769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4572762944085446110844717 1714786104032042291566769)
                      ·
                        rfl

theorem cell23_3339534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3339534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339534 prefixEnd_3339534 := by exact prefixLift 3339534
  have htrace : WordTrace (prefixWord ++ tailWord_3339534) baseStart_3339534 baseEnd_3339534 := by
    simpa [prefixWord, tailWord_3339534, baseEnd_3339534] using wordTrace_append hprefix tailTrace_3339534
  have hstable : (prefixWord ++ tailWord_3339534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339534).length < 2 ^ (prefixWord ++ tailWord_3339534).sum := by decide
  have hdescent : baseEnd_3339534 < baseStart_3339534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339557 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 1, 4, 2]
def baseStart_3339557 : Nat := 118140960795 + 3339557 * 2 ^ 59
def prefixEnd_3339557 : Nat := 4983230072969 + 3 ^ 40 * 3339557 * 2
def baseEnd_3339557 : Nat := 1714797914087095701579163

theorem tailTrace_3339557 : CollatzResearch.WordTrace tailWord_3339557 prefixEnd_3339557 1714797914087095701579163 := by
  unfold tailWord_3339557
  simp only [CollatzResearch.WordTrace]
  refine ⟨121803650362362814772752925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81202433574908543181835283 121803650362362814772752925)
  ·
    refine ⟨45676368885886055539782347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121803650362362814772752925 45676368885886055539782347)
    ·
      refine ⟨68514553328829083309673521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45676368885886055539782347 68514553328829083309673521)
      ·
        refine ⟨51385914996621812482255141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68514553328829083309673521 51385914996621812482255141)
        ·
          refine ⟨9634859061866589840422839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51385914996621812482255141 9634859061866589840422839)
          ·
            refine ⟨14452288592799884760634259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9634859061866589840422839 14452288592799884760634259)
            ·
              refine ⟨21678432889199827140951389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14452288592799884760634259 21678432889199827140951389)
              ·
                refine ⟨8129412333449935177856771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21678432889199827140951389 8129412333449935177856771)
                ·
                  refine ⟨12194118500174902766785157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129412333449935177856771 12194118500174902766785157)
                  ·
                    refine ⟨2286397218782794268772217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12194118500174902766785157 2286397218782794268772217)
                    ·
                      refine ⟨1714797914087095701579163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286397218782794268772217 1714797914087095701579163)
                      ·
                        rfl

theorem cell23_3339557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_3339557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339557 prefixEnd_3339557 := by exact prefixLift 3339557
  have htrace : WordTrace (prefixWord ++ tailWord_3339557) baseStart_3339557 baseEnd_3339557 := by
    simpa [prefixWord, tailWord_3339557, baseEnd_3339557] using wordTrace_append hprefix tailTrace_3339557
  have hstable : (prefixWord ++ tailWord_3339557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339557).length < 2 ^ (prefixWord ++ tailWord_3339557).sum := by decide
  have hdescent : baseEnd_3339557 < baseStart_3339557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339591 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_3339591 : Nat := 118140960795 + 3339591 * 2 ^ 59
def prefixEnd_3339591 : Nat := 4983230072969 + 3 ^ 40 * 3339591 * 2
def baseEnd_3339591 : Nat := 1714815372429348568554007

theorem tailTrace_3339591 : CollatzResearch.WordTrace tailWord_3339591 prefixEnd_3339591 1714815372429348568554007 := by
  unfold tailWord_3339591
  simp only [CollatzResearch.WordTrace]
  refine ⟨121804890444239638579490627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81203260296159759052993751 121804890444239638579490627)
  ·
    refine ⟨182707335666359457869235941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121804890444239638579490627 182707335666359457869235941)
    ·
      refine ⟨34257625437442398350481739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182707335666359457869235941 34257625437442398350481739)
      ·
        refine ⟨51386438156163597525722609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34257625437442398350481739 51386438156163597525722609)
        ·
          refine ⟨38539828617122698144291957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51386438156163597525722609 38539828617122698144291957)
          ·
            refine ⟨3613108932855252951027371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38539828617122698144291957 3613108932855252951027371)
            ·
              refine ⟨5419663399282879426541057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613108932855252951027371 5419663399282879426541057)
              ·
                refine ⟨4064747549462159569905793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419663399282879426541057 4064747549462159569905793)
                ·
                  refine ⟨3048560662096619677429345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064747549462159569905793 3048560662096619677429345)
                  ·
                    refine ⟨2286420496572464758072009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3048560662096619677429345 2286420496572464758072009)
                    ·
                      refine ⟨1714815372429348568554007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286420496572464758072009 1714815372429348568554007)
                      ·
                        rfl

theorem cell23_3339591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_3339591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339591 prefixEnd_3339591 := by exact prefixLift 3339591
  have htrace : WordTrace (prefixWord ++ tailWord_3339591) baseStart_3339591 baseEnd_3339591 := by
    simpa [prefixWord, tailWord_3339591, baseEnd_3339591] using wordTrace_append hprefix tailTrace_3339591
  have hstable : (prefixWord ++ tailWord_3339591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339591).length < 2 ^ (prefixWord ++ tailWord_3339591).sum := by decide
  have hdescent : baseEnd_3339591 < baseStart_3339591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339603 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_3339603 : Nat := 118140960795 + 3339603 * 2 ^ 59
def prefixEnd_3339603 : Nat := 4983230072969 + 3 ^ 40 * 3339603 * 2
def baseEnd_3339603 : Nat := 1714821534197202521603951

theorem tailTrace_3339603 : CollatzResearch.WordTrace tailWord_3339603 prefixEnd_3339603 1714821534197202521603951 := by
  unfold tailWord_3339603
  simp only [CollatzResearch.WordTrace]
  refine ⟨121805328120196164628927463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81203552080130776419284975 121805328120196164628927463)
  ·
    refine ⟨182707992180294246943391195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121805328120196164628927463 182707992180294246943391195)
    ·
      refine ⟨274061988270441370415086793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182707992180294246943391195 274061988270441370415086793)
      ·
        refine ⟨205546491202831027811315095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274061988270441370415086793 205546491202831027811315095)
        ·
          refine ⟨308319736804246541716972643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205546491202831027811315095 308319736804246541716972643)
          ·
            refine ⟨462479605206369812575458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308319736804246541716972643 462479605206369812575458965)
            ·
              refine ⟨21678731494048584964474639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 462479605206369812575458965 21678731494048584964474639)
              ·
                refine ⟨32518097241072877446711959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21678731494048584964474639 32518097241072877446711959)
                ·
                  refine ⟨48777145861609316170067939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32518097241072877446711959 48777145861609316170067939)
                  ·
                    refine ⟨73165718792413974255101909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48777145861609316170067939 73165718792413974255101909)
                    ·
                      refine ⟨1714821534197202521603951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73165718792413974255101909 1714821534197202521603951)
                      ·
                        rfl

theorem cell23_3339603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_3339603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339603 prefixEnd_3339603 := by exact prefixLift 3339603
  have htrace : WordTrace (prefixWord ++ tailWord_3339603) baseStart_3339603 baseEnd_3339603 := by
    simpa [prefixWord, tailWord_3339603, baseEnd_3339603] using wordTrace_append hprefix tailTrace_3339603
  have hstable : (prefixWord ++ tailWord_3339603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339603).length < 2 ^ (prefixWord ++ tailWord_3339603).sum := by decide
  have hdescent : baseEnd_3339603 < baseStart_3339603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339734 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3339734 : Nat := 118140960795 + 3339734 * 2 ^ 59
def prefixEnd_3339734 : Nat := 4983230072969 + 3 ^ 40 * 3339734 * 2
def baseEnd_3339734 : Nat := 571629600054313836355283

theorem tailTrace_3339734 : CollatzResearch.WordTrace tailWord_3339734 prefixEnd_3339734 571629600054313836355283 := by
  unfold tailWord_3339734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7613131630170098375121641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81206737388481049334630837 7613131630170098375121641)
  ·
    refine ⟨5709848722627573781341231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7613131630170098375121641 5709848722627573781341231)
    ·
      refine ⟨8564773083941360672011847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709848722627573781341231 8564773083941360672011847)
      ·
        refine ⟨12847159625912041008017771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564773083941360672011847 12847159625912041008017771)
        ·
          refine ⟨19270739438868061512026657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12847159625912041008017771 19270739438868061512026657)
          ·
            refine ⟨14453054579151046134019993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270739438868061512026657 14453054579151046134019993)
            ·
              refine ⟨10839790934363284600514995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14453054579151046134019993 10839790934363284600514995)
              ·
                refine ⟨16259686401544926900772493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10839790934363284600514995 16259686401544926900772493)
                ·
                  refine ⟨6097382400579347587789685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16259686401544926900772493 6097382400579347587789685)
                  ·
                    refine ⟨571629600054313836355283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6097382400579347587789685 571629600054313836355283)
                    ·
                      rfl

theorem cell23_3339734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3339734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339734 prefixEnd_3339734 := by exact prefixLift 3339734
  have htrace : WordTrace (prefixWord ++ tailWord_3339734) baseStart_3339734 baseEnd_3339734 := by
    simpa [prefixWord, tailWord_3339734, baseEnd_3339734] using wordTrace_append hprefix tailTrace_3339734
  have hstable : (prefixWord ++ tailWord_3339734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339734).length < 2 ^ (prefixWord ++ tailWord_3339734).sum := by decide
  have hdescent : baseEnd_3339734 < baseStart_3339734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339737 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3339737 : Nat := 118140960795 + 3339737 * 2 ^ 59
def prefixEnd_3339737 : Nat := 4983230072969 + 3 ^ 40 * 3339737 * 2
def baseEnd_3339737 : Nat := 1714890340604904997328335

theorem tailTrace_3339737 : CollatzResearch.WordTrace tailWord_3339737 prefixEnd_3339737 1714890340604904997328335 := by
  unfold tailWord_3339737
  simp only [CollatzResearch.WordTrace]
  refine ⟨121810215501710705514305465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81206810334473803676203643 121810215501710705514305465)
  ·
    refine ⟨91357661626283029135729099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121810215501710705514305465 91357661626283029135729099)
    ·
      refine ⟨137036492439424543703593649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91357661626283029135729099 137036492439424543703593649)
      ·
        refine ⟨102777369329568407777695237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137036492439424543703593649 102777369329568407777695237)
        ·
          refine ⟨19270756749294076458317857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102777369329568407777695237 19270756749294076458317857)
          ·
            refine ⟨14453067561970557343738393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270756749294076458317857 14453067561970557343738393)
            ·
              refine ⟨10839800671477918007803795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14453067561970557343738393 10839800671477918007803795)
              ·
                refine ⟨16259701007216877011705693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10839800671477918007803795 16259701007216877011705693)
                ·
                  refine ⟨6097387877706328879389635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16259701007216877011705693 6097387877706328879389635)
                  ·
                    refine ⟨9146081816559493319084453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6097387877706328879389635 9146081816559493319084453)
                    ·
                      refine ⟨1714890340604904997328335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9146081816559493319084453 1714890340604904997328335)
                      ·
                        rfl

theorem cell23_3339737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3339737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339737 prefixEnd_3339737 := by exact prefixLift 3339737
  have htrace : WordTrace (prefixWord ++ tailWord_3339737) baseStart_3339737 baseEnd_3339737 := by
    simpa [prefixWord, tailWord_3339737, baseEnd_3339737] using wordTrace_append hprefix tailTrace_3339737
  have hstable : (prefixWord ++ tailWord_3339737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339737).length < 2 ^ (prefixWord ++ tailWord_3339737).sum := by decide
  have hdescent : baseEnd_3339737 < baseStart_3339737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339741 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 2, 3, 2]
def baseStart_3339741 : Nat := 118140960795 + 3339741 * 2 ^ 59
def prefixEnd_3339741 : Nat := 4983230072969 + 3 ^ 40 * 3339741 * 2
def baseEnd_3339741 : Nat := 1714892394527522981678317

theorem tailTrace_3339741 : CollatzResearch.WordTrace tailWord_3339741 prefixEnd_3339741 1714892394527522981678317 := by
  unfold tailWord_3339741
  simp only [CollatzResearch.WordTrace]
  refine ⟨121810361393696214197451077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81206907595797476131634051 121810361393696214197451077)
  ·
    refine ⟨22839442761318040162022077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121810361393696214197451077 22839442761318040162022077)
    ·
      refine ⟨8564791035494265060758279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22839442761318040162022077 8564791035494265060758279)
      ·
        refine ⟨12847186553241397591137419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564791035494265060758279 12847186553241397591137419)
        ·
          refine ⟨19270779829862096386706129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12847186553241397591137419 19270779829862096386706129)
          ·
            refine ⟨14453084872396572290029597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270779829862096386706129 14453084872396572290029597)
            ·
              refine ⟨5419906827148714608761099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14453084872396572290029597 5419906827148714608761099)
              ·
                refine ⟨8129860240723071913141649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419906827148714608761099 8129860240723071913141649)
                ·
                  refine ⟨6097395180542303934856237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8129860240723071913141649 6097395180542303934856237)
                  ·
                    refine ⟨2286523192703363975571089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6097395180542303934856237 2286523192703363975571089)
                    ·
                      refine ⟨1714892394527522981678317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286523192703363975571089 1714892394527522981678317)
                      ·
                        rfl

theorem cell23_3339741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_3339741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339741 prefixEnd_3339741 := by exact prefixLift 3339741
  have htrace : WordTrace (prefixWord ++ tailWord_3339741) baseStart_3339741 baseEnd_3339741 := by
    simpa [prefixWord, tailWord_3339741, baseEnd_3339741] using wordTrace_append hprefix tailTrace_3339741
  have hstable : (prefixWord ++ tailWord_3339741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339741).length < 2 ^ (prefixWord ++ tailWord_3339741).sum := by decide
  have hdescent : baseEnd_3339741 < baseStart_3339741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339747 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 1, 6]
def baseStart_3339747 : Nat := 118140960795 + 3339747 * 2 ^ 59
def prefixEnd_3339747 : Nat := 4983230072969 + 3 ^ 40 * 3339747 * 2
def baseEnd_3339747 : Nat := 571631825137149986067763

theorem tailTrace_3339747 : CollatzResearch.WordTrace tailWord_3339747 prefixEnd_3339747 571631825137149986067763 := by
  unfold tailWord_3339747
  simp only [CollatzResearch.WordTrace]
  refine ⟨121810580231674477222169495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81207053487782984814779663 121810580231674477222169495)
  ·
    refine ⟨182715870347511715833254243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121810580231674477222169495 182715870347511715833254243)
    ·
      refine ⟨274073805521267573749881365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182715870347511715833254243 274073805521267573749881365)
      ·
        refine ⟨12847209633809417519525689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 274073805521267573749881365 12847209633809417519525689)
        ·
          refine ⟨9635407225357063139644267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12847209633809417519525689 9635407225357063139644267)
          ·
            refine ⟨14453110838035594709466401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9635407225357063139644267 14453110838035594709466401)
            ·
              refine ⟨10839833128526696032099801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14453110838035594709466401 10839833128526696032099801)
              ·
                refine ⟨8129874846395022024074851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10839833128526696032099801 8129874846395022024074851)
                ·
                  refine ⟨12194812269592533036112277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8129874846395022024074851 12194812269592533036112277)
                  ·
                    refine ⟨571631825137149986067763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12194812269592533036112277 571631825137149986067763)
                    ·
                      rfl

theorem cell23_3339747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 6].length) (baseStart_3339747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339747 prefixEnd_3339747 := by exact prefixLift 3339747
  have htrace : WordTrace (prefixWord ++ tailWord_3339747) baseStart_3339747 baseEnd_3339747 := by
    simpa [prefixWord, tailWord_3339747, baseEnd_3339747] using wordTrace_append hprefix tailTrace_3339747
  have hstable : (prefixWord ++ tailWord_3339747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339747).length < 2 ^ (prefixWord ++ tailWord_3339747).sum := by decide
  have hdescent : baseEnd_3339747 < baseStart_3339747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339751 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3339751 : Nat := 118140960795 + 3339751 * 2 ^ 59
def prefixEnd_3339751 : Nat := 4983230072969 + 3 ^ 40 * 3339751 * 2
def baseEnd_3339751 : Nat := 571632509778022647517757

theorem tailTrace_3339751 : CollatzResearch.WordTrace tailWord_3339751 prefixEnd_3339751 571632509778022647517757 := by
  unfold tailWord_3339751
  simp only [CollatzResearch.WordTrace]
  refine ⟨121810726123659985905315107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81207150749106657270210071 121810726123659985905315107)
  ·
    refine ⟨182716089185489978857972661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121810726123659985905315107 182716089185489978857972661)
    ·
      refine ⟨17129633361139685517934937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182716089185489978857972661 17129633361139685517934937)
      ·
        refine ⟨12847225020854764138451203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17129633361139685517934937 12847225020854764138451203)
        ·
          refine ⟨19270837531282146207676805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12847225020854764138451203 19270837531282146207676805)
          ·
            refine ⟨3613282037115402413939401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19270837531282146207676805 3613282037115402413939401)
            ·
              refine ⟨2709961527836551810454551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613282037115402413939401 2709961527836551810454551)
              ·
                refine ⟨4064942291754827715681827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709961527836551810454551 4064942291754827715681827)
                ·
                  refine ⟨6097413437632241573522741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064942291754827715681827 6097413437632241573522741)
                  ·
                    refine ⟨571632509778022647517757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6097413437632241573522741 571632509778022647517757)
                    ·
                      rfl

theorem cell23_3339751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3339751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339751 prefixEnd_3339751 := by exact prefixLift 3339751
  have htrace : WordTrace (prefixWord ++ tailWord_3339751) baseStart_3339751 baseEnd_3339751 := by
    simpa [prefixWord, tailWord_3339751, baseEnd_3339751] using wordTrace_append hprefix tailTrace_3339751
  have hstable : (prefixWord ++ tailWord_3339751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339751).length < 2 ^ (prefixWord ++ tailWord_3339751).sum := by decide
  have hdescent : baseEnd_3339751 < baseStart_3339751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339760 : List Nat := [2, 1, 1, 1, 3, 5, 10]
def baseStart_3339760 : Nat := 118140960795 + 3339760 * 2 ^ 59
def prefixEnd_3339760 : Nat := 4983230072969 + 3 ^ 40 * 3339760 * 2
def baseEnd_3339760 : Nat := 21171631489629116140009

theorem tailTrace_3339760 : CollatzResearch.WordTrace tailWord_3339760 prefixEnd_3339760 21171631489629116140009 := by
  unfold tailWord_3339760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60905527190313690221196367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81207369587084920294928489 60905527190313690221196367)
  ·
    refine ⟨91358290785470535331794551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60905527190313690221196367 91358290785470535331794551)
    ·
      refine ⟨137037436178205802997691827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91358290785470535331794551 137037436178205802997691827)
      ·
        refine ⟨205556154267308704496537741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137037436178205802997691827 205556154267308704496537741)
        ·
          refine ⟨77083557850240764186201653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205556154267308704496537741 77083557850240764186201653)
          ·
            refine ⟨7226583548460071642456405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77083557850240764186201653 7226583548460071642456405)
            ·
              refine ⟨21171631489629116140009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7226583548460071642456405 21171631489629116140009)
              ·
                rfl

theorem cell23_3339760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 10].length) (baseStart_3339760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339760 prefixEnd_3339760 := by exact prefixLift 3339760
  have htrace : WordTrace (prefixWord ++ tailWord_3339760) baseStart_3339760 baseEnd_3339760 := by
    simpa [prefixWord, tailWord_3339760, baseEnd_3339760] using wordTrace_append hprefix tailTrace_3339760
  have hstable : (prefixWord ++ tailWord_3339760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339760).length < 2 ^ (prefixWord ++ tailWord_3339760).sum := by decide
  have hdescent : baseEnd_3339760 < baseStart_3339760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339804 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3339804 : Nat := 118140960795 + 3339804 * 2 ^ 59
def prefixEnd_3339804 : Nat := 4983230072969 + 3 ^ 40 * 3339804 * 2
def baseEnd_3339804 : Nat := 1714924743808756235190527

theorem tailTrace_3339804 : CollatzResearch.WordTrace tailWord_3339804 prefixEnd_3339804 1714924743808756235190527 := by
  unfold tailWord_3339804
  simp only [CollatzResearch.WordTrace]
  refine ⟨60906329596233987978497233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81208439461645317304662977 60906329596233987978497233)
  ·
    refine ⟨45679747197175490983872925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60906329596233987978497233 45679747197175490983872925)
    ·
      refine ⟨17129905198940809118952347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45679747197175490983872925 17129905198940809118952347)
      ·
        refine ⟨25694857798411213678428521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17129905198940809118952347 25694857798411213678428521)
        ·
          refine ⟨19271143348808410258821391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25694857798411213678428521 19271143348808410258821391)
          ·
            refine ⟨28906715023212615388232087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19271143348808410258821391 28906715023212615388232087)
            ·
              refine ⟨43360072534818923082348131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28906715023212615388232087 43360072534818923082348131)
              ·
                refine ⟨65040108802228384623522197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43360072534818923082348131 65040108802228384623522197)
                ·
                  refine ⟨3048755100104455529227603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65040108802228384623522197 3048755100104455529227603)
                  ·
                    refine ⟨4573132650156683293841405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3048755100104455529227603 4573132650156683293841405)
                    ·
                      refine ⟨1714924743808756235190527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4573132650156683293841405 1714924743808756235190527)
                      ·
                        rfl

theorem cell23_3339804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3339804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339804 prefixEnd_3339804 := by exact prefixLift 3339804
  have htrace : WordTrace (prefixWord ++ tailWord_3339804) baseStart_3339804 baseEnd_3339804 := by
    simpa [prefixWord, tailWord_3339804, baseEnd_3339804] using wordTrace_append hprefix tailTrace_3339804
  have hstable : (prefixWord ++ tailWord_3339804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339804).length < 2 ^ (prefixWord ++ tailWord_3339804).sum := by decide
  have hdescent : baseEnd_3339804 < baseStart_3339804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339822 : List Nat := [4, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3339822 : Nat := 118140960795 + 3339822 * 2 ^ 59
def prefixEnd_3339822 : Nat := 4983230072969 + 3 ^ 40 * 3339822 * 2
def baseEnd_3339822 : Nat := 1714933986460537164765445

theorem tailTrace_3339822 : CollatzResearch.WordTrace tailWord_3339822 prefixEnd_3339822 1714933986460537164765445 := by
  unfold tailWord_3339822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226664463300345628893715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81208877137601843354099813 15226664463300345628893715)
  ·
    refine ⟨22839996694950518443340573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15226664463300345628893715 22839996694950518443340573)
    ·
      refine ⟨8564998760606444416252715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22839996694950518443340573 8564998760606444416252715)
      ·
        refine ⟨12847498140909666624379073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564998760606444416252715 12847498140909666624379073)
        ·
          refine ⟨9635623605682249968284305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12847498140909666624379073 9635623605682249968284305)
          ·
            refine ⟨7226717704261687476213229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9635623605682249968284305 7226717704261687476213229)
            ·
              refine ⟨2710019139098132803579961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7226717704261687476213229 2710019139098132803579961)
              ·
                refine ⟨2032514354323599602684971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710019139098132803579961 2032514354323599602684971)
                ·
                  refine ⟨3048771531485399404027457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032514354323599602684971 3048771531485399404027457)
                  ·
                    refine ⟨2286578648614049553020593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3048771531485399404027457 2286578648614049553020593)
                    ·
                      refine ⟨1714933986460537164765445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286578648614049553020593 1714933986460537164765445)
                      ·
                        rfl

theorem cell23_3339822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3339822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339822 prefixEnd_3339822 := by exact prefixLift 3339822
  have htrace : WordTrace (prefixWord ++ tailWord_3339822) baseStart_3339822 baseEnd_3339822 := by
    simpa [prefixWord, tailWord_3339822, baseEnd_3339822] using wordTrace_append hprefix tailTrace_3339822
  have hstable : (prefixWord ++ tailWord_3339822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339822).length < 2 ^ (prefixWord ++ tailWord_3339822).sum := by decide
  have hdescent : baseEnd_3339822 < baseStart_3339822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339897 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_3339897 : Nat := 118140960795 + 3339897 * 2 ^ 59
def prefixEnd_3339897 : Nat := 4983230072969 + 3 ^ 40 * 3339897 * 2
def baseEnd_3339897 : Nat := 571657499169874790442533

theorem tailTrace_3339897 : CollatzResearch.WordTrace tailWord_3339897 prefixEnd_3339897 571657499169874790442533 := by
  unfold tailWord_3339897
  simp only [CollatzResearch.WordTrace]
  refine ⟨121816051181131052840129945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81210700787420701893419963 121816051181131052840129945)
  ·
    refine ⟨91362038385848289630097459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121816051181131052840129945 91362038385848289630097459)
    ·
      refine ⟨137043057578772434445146189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91362038385848289630097459 137043057578772434445146189)
      ·
        refine ⟨51391146592039662916929821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137043057578772434445146189 51391146592039662916929821)
        ·
          refine ⟨19271679972014873593848683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51391146592039662916929821 19271679972014873593848683)
          ·
            refine ⟨28907519958022310390773025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19271679972014873593848683 28907519958022310390773025)
            ·
              refine ⟨21680639968516732793079769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28907519958022310390773025 21680639968516732793079769)
              ·
                refine ⟨16260479976387549594809827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21680639968516732793079769 16260479976387549594809827)
                ·
                  refine ⟨24390719964581324392214741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16260479976387549594809827 24390719964581324392214741)
                  ·
                    refine ⟨571657499169874790442533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24390719964581324392214741 571657499169874790442533)
                    ·
                      rfl

theorem cell23_3339897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_3339897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339897 prefixEnd_3339897 := by exact prefixLift 3339897
  have htrace : WordTrace (prefixWord ++ tailWord_3339897) baseStart_3339897 baseEnd_3339897 := by
    simpa [prefixWord, tailWord_3339897, baseEnd_3339897] using wordTrace_append hprefix tailTrace_3339897
  have hstable : (prefixWord ++ tailWord_3339897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339897).length < 2 ^ (prefixWord ++ tailWord_3339897).sum := by decide
  have hdescent : baseEnd_3339897 < baseStart_3339897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339904 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2]
def baseStart_3339904 : Nat := 118140960795 + 3339904 * 2 ^ 59
def prefixEnd_3339904 : Nat := 4983230072969 + 3 ^ 40 * 3339904 * 2
def baseEnd_3339904 : Nat := 1714976091874205843940067

theorem tailTrace_3339904 : CollatzResearch.WordTrace tailWord_3339904 prefixEnd_3339904 1714976091874205843940067 := by
  unfold tailWord_3339904
  simp only [CollatzResearch.WordTrace]
  refine ⟨60908153246052846517817383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81210870994737128690423177 60908153246052846517817383)
  ·
    refine ⟨91362229869079269776726075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60908153246052846517817383 91362229869079269776726075)
    ·
      refine ⟨137043344803618904665089113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91362229869079269776726075 137043344803618904665089113)
      ·
        refine ⟨102782508602714178498816835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137043344803618904665089113 102782508602714178498816835)
        ·
          refine ⟨154173762904071267748225253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102782508602714178498816835 154173762904071267748225253)
          ·
            refine ⟨28907580544513362702792235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154173762904071267748225253 28907580544513362702792235)
            ·
              refine ⟨43361370816770044054188353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28907580544513362702792235 43361370816770044054188353)
              ·
                refine ⟨32521028112577533040641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43361370816770044054188353 32521028112577533040641265)
                ·
                  refine ⟨24390771084433149780480949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32521028112577533040641265 24390771084433149780480949)
                  ·
                    refine ⟨2286634789165607791920089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24390771084433149780480949 2286634789165607791920089)
                    ·
                      refine ⟨1714976091874205843940067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286634789165607791920089 1714976091874205843940067)
                      ·
                        rfl

theorem cell23_3339904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_3339904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339904 prefixEnd_3339904 := by exact prefixLift 3339904
  have htrace : WordTrace (prefixWord ++ tailWord_3339904) baseStart_3339904 baseEnd_3339904 := by
    simpa [prefixWord, tailWord_3339904, baseEnd_3339904] using wordTrace_append hprefix tailTrace_3339904
  have hstable : (prefixWord ++ tailWord_3339904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339904).length < 2 ^ (prefixWord ++ tailWord_3339904).sum := by decide
  have hdescent : baseEnd_3339904 < baseStart_3339904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339914 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3339914 : Nat := 118140960795 + 3339914 * 2 ^ 59
def prefixEnd_3339914 : Nat := 4983230072969 + 3 ^ 40 * 3339914 * 2
def baseEnd_3339914 : Nat := 571660408893583601605007

theorem tailTrace_3339914 : CollatzResearch.WordTrace tailWord_3339914 prefixEnd_3339914 571660408893583601605007 := by
  unfold tailWord_3339914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30454167805517366185874699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81211114148046309828999197 30454167805517366185874699)
  ·
    refine ⟨45681251708276049278812049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30454167805517366185874699 45681251708276049278812049)
    ·
      refine ⟨34260938781207036959109037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45681251708276049278812049 34260938781207036959109037)
      ·
        refine ⟨12847852042952638859665889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34260938781207036959109037 12847852042952638859665889)
        ·
          refine ⟨9635889032214479144749417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12847852042952638859665889 9635889032214479144749417)
          ·
            refine ⟨7226916774160859358562063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9635889032214479144749417 7226916774160859358562063)
            ·
              refine ⟨10840375161241289037843095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7226916774160859358562063 10840375161241289037843095)
              ·
                refine ⟨16260562741861933556764643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10840375161241289037843095 16260562741861933556764643)
                ·
                  refine ⟨24390844112792900335146965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16260562741861933556764643 24390844112792900335146965)
                  ·
                    refine ⟨571660408893583601605007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24390844112792900335146965 571660408893583601605007)
                    ·
                      rfl

theorem cell23_3339914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3339914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339914 prefixEnd_3339914 := by exact prefixLift 3339914
  have htrace : WordTrace (prefixWord ++ tailWord_3339914) baseStart_3339914 baseEnd_3339914 := by
    simpa [prefixWord, tailWord_3339914, baseEnd_3339914] using wordTrace_append hprefix tailTrace_3339914
  have hstable : (prefixWord ++ tailWord_3339914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339914).length < 2 ^ (prefixWord ++ tailWord_3339914).sum := by decide
  have hdescent : baseEnd_3339914 < baseStart_3339914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339954 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3339954 : Nat := 118140960795 + 3339954 * 2 ^ 59
def prefixEnd_3339954 : Nat := 4983230072969 + 3 ^ 40 * 3339954 * 2
def baseEnd_3339954 : Nat := 1715001765906930648314837

theorem tailTrace_3339954 : CollatzResearch.WordTrace tailWord_3339954 prefixEnd_3339954 1715001765906930648314837 := by
  unfold tailWord_3339954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30454532535481137893738729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81212086761283034383303277 30454532535481137893738729)
  ·
    refine ⟨22840899401610853420304047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30454532535481137893738729 22840899401610853420304047)
    ·
      refine ⟨34261349102416280130456071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22840899401610853420304047 34261349102416280130456071)
      ·
        refine ⟨51392023653624420195684107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34261349102416280130456071 51392023653624420195684107)
        ·
          refine ⟨77088035480436630293526161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51392023653624420195684107 77088035480436630293526161)
          ·
            refine ⟨57816026610327472720144621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77088035480436630293526161 57816026610327472720144621)
            ·
              refine ⟨21681009978872802270054233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57816026610327472720144621 21681009978872802270054233)
              ·
                refine ⟨16260757484154601702540675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21681009978872802270054233 16260757484154601702540675)
                ·
                  refine ⟨24391136226231902553811013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16260757484154601702540675 24391136226231902553811013)
                  ·
                    refine ⟨4573338042418481728839565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24391136226231902553811013 4573338042418481728839565)
                    ·
                      refine ⟨1715001765906930648314837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4573338042418481728839565 1715001765906930648314837)
                      ·
                        rfl

theorem cell23_3339954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3339954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339954 prefixEnd_3339954 := by exact prefixLift 3339954
  have htrace : WordTrace (prefixWord ++ tailWord_3339954) baseStart_3339954 baseEnd_3339954 := by
    simpa [prefixWord, tailWord_3339954, baseEnd_3339954] using wordTrace_append hprefix tailTrace_3339954
  have hstable : (prefixWord ++ tailWord_3339954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339954).length < 2 ^ (prefixWord ++ tailWord_3339954).sum := by decide
  have hdescent : baseEnd_3339954 < baseStart_3339954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3339988 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3339988 : Nat := 118140960795 + 3339988 * 2 ^ 59
def prefixEnd_3339988 : Nat := 4983230072969 + 3 ^ 40 * 3339988 * 2
def baseEnd_3339988 : Nat := 1715019224249183515289681

theorem tailTrace_3339988 : CollatzResearch.WordTrace tailWord_3339988 prefixEnd_3339988 1715019224249183515289681 := by
  unfold tailWord_3339988
  simp only [CollatzResearch.WordTrace]
  refine ⟨60909685111900687690846309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81212913482534250254461745 60909685111900687690846309)
  ·
    refine ⟨11420565958481378942033683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60909685111900687690846309 11420565958481378942033683)
    ·
      refine ⟨17130848937722068413050525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11420565958481378942033683 17130848937722068413050525)
      ·
        refine ⟨6424068351645775654893947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17130848937722068413050525 6424068351645775654893947)
        ·
          refine ⟨9636102527468663482340921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424068351645775654893947 9636102527468663482340921)
          ·
            refine ⟨7227076895601497611755691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9636102527468663482340921 7227076895601497611755691)
            ·
              refine ⟨10840615343402246417633537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227076895601497611755691 10840615343402246417633537)
              ·
                refine ⟨8130461507551684813225153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10840615343402246417633537 8130461507551684813225153)
                ·
                  refine ⟨6097846130663763609918865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130461507551684813225153 6097846130663763609918865)
                  ·
                    refine ⟨4573384597997822707439149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097846130663763609918865 4573384597997822707439149)
                    ·
                      refine ⟨1715019224249183515289681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4573384597997822707439149 1715019224249183515289681)
                      ·
                        rfl

theorem cell23_3339988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3339988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3339988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3339988 prefixEnd_3339988 := by exact prefixLift 3339988
  have htrace : WordTrace (prefixWord ++ tailWord_3339988) baseStart_3339988 baseEnd_3339988 := by
    simpa [prefixWord, tailWord_3339988, baseEnd_3339988] using wordTrace_append hprefix tailTrace_3339988
  have hstable : (prefixWord ++ tailWord_3339988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3339988).length < 2 ^ (prefixWord ++ tailWord_3339988).sum := by decide
  have hdescent : baseEnd_3339988 < baseStart_3339988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3339988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340004 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_3340004 : Nat := 118140960795 + 3340004 * 2 ^ 59
def prefixEnd_3340004 : Nat := 4983230072969 + 3 ^ 40 * 3340004 * 2
def baseEnd_3340004 : Nat := 571675813313218484229869

theorem tailTrace_3340004 : CollatzResearch.WordTrace tailWord_3340004 prefixEnd_3340004 571675813313218484229869 := by
  unfold tailWord_3340004
  simp only [CollatzResearch.WordTrace]
  refine ⟨60909976895871705057137533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81213302527828940076183377 60909976895871705057137533)
  ·
    refine ⟨22841241335951889396426575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60909976895871705057137533 22841241335951889396426575)
    ·
      refine ⟨34261862003927834094639863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22841241335951889396426575 34261862003927834094639863)
      ·
        refine ⟨51392793005891751141959795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34261862003927834094639863 51392793005891751141959795)
        ·
          refine ⟨77089189508837626712939693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51392793005891751141959795 77089189508837626712939693)
          ·
            refine ⟨28908446065814110017352385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77089189508837626712939693 28908446065814110017352385)
            ·
              refine ⟨21681334549360582513014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28908446065814110017352385 21681334549360582513014289)
              ·
                refine ⟨16261000912020436884760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21681334549360582513014289 16261000912020436884760717)
                ·
                  refine ⟨6097875342007663831785269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16261000912020436884760717 6097875342007663831785269)
                  ·
                    refine ⟨571675813313218484229869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6097875342007663831785269 571675813313218484229869)
                    ·
                      rfl

theorem cell23_3340004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_3340004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340004 prefixEnd_3340004 := by exact prefixLift 3340004
  have htrace : WordTrace (prefixWord ++ tailWord_3340004) baseStart_3340004 baseEnd_3340004 := by
    simpa [prefixWord, tailWord_3340004, baseEnd_3340004] using wordTrace_append hprefix tailTrace_3340004
  have hstable : (prefixWord ++ tailWord_3340004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340004).length < 2 ^ (prefixWord ++ tailWord_3340004).sum := by decide
  have hdescent : baseEnd_3340004 < baseStart_3340004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340008 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 6]
def baseStart_3340008 : Nat := 118140960795 + 3340008 * 2 ^ 59
def prefixEnd_3340008 : Nat := 4983230072969 + 3 ^ 40 * 3340008 * 2
def baseEnd_3340008 : Nat := 190558832651363715226621

theorem tailTrace_3340008 : CollatzResearch.WordTrace tailWord_3340008 prefixEnd_3340008 190558832651363715226621 := by
  unfold tailWord_3340008
  simp only [CollatzResearch.WordTrace]
  refine ⟨60910049841864459398710339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81213399789152612531613785 60910049841864459398710339)
  ·
    refine ⟨91365074762796689098065509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60910049841864459398710339 91365074762796689098065509)
    ·
      refine ⟨17130951518024379205887283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91365074762796689098065509 17130951518024379205887283)
      ·
        refine ⟨25696427277036568808830925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17130951518024379205887283 25696427277036568808830925)
        ·
          refine ⟨9636160228888713303311597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25696427277036568808830925 9636160228888713303311597)
          ·
            refine ⟨3613560085833267488741849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9636160228888713303311597 3613560085833267488741849)
            ·
              refine ⟨2710170064374950616556387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613560085833267488741849 2710170064374950616556387)
              ·
                refine ⟨4065255096562425924834581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710170064374950616556387 4065255096562425924834581)
                ·
                  refine ⟨190558832651363715226621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4065255096562425924834581 190558832651363715226621)
                  ·
                    rfl

theorem cell23_3340008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 6].length) (baseStart_3340008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340008 prefixEnd_3340008 := by exact prefixLift 3340008
  have htrace : WordTrace (prefixWord ++ tailWord_3340008) baseStart_3340008 baseEnd_3340008 := by
    simpa [prefixWord, tailWord_3340008, baseEnd_3340008] using wordTrace_append hprefix tailTrace_3340008
  have hstable : (prefixWord ++ tailWord_3340008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340008).length < 2 ^ (prefixWord ++ tailWord_3340008).sum := by decide
  have hdescent : baseEnd_3340008 < baseStart_3340008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340028 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_3340028 : Nat := 118140960795 + 3340028 * 2 ^ 59
def prefixEnd_3340028 : Nat := 4983230072969 + 3 ^ 40 * 3340028 * 2
def baseEnd_3340028 : Nat := 1715039763475363358789497

theorem tailTrace_3340028 : CollatzResearch.WordTrace tailWord_3340028 prefixEnd_3340028 1715039763475363358789497 := by
  unfold tailWord_3340028
  simp only [CollatzResearch.WordTrace]
  refine ⟨60910414571828231106574369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81213886095770974808765825 60910414571828231106574369)
  ·
    refine ⟨45682810928871173329930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60910414571828231106574369 45682810928871173329930777)
    ·
      refine ⟨34262108196653379997448083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45682810928871173329930777 34262108196653379997448083)
      ·
        refine ⟨51393162294980069996172125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34262108196653379997448083 51393162294980069996172125)
        ·
          refine ⟨19272435860617526248564547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51393162294980069996172125 19272435860617526248564547)
          ·
            refine ⟨28908653790926289372846821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19272435860617526248564547 28908653790926289372846821)
            ·
              refine ⟨5420372585798679257408779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28908653790926289372846821 5420372585798679257408779)
              ·
                refine ⟨8130558878698018886113169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420372585798679257408779 8130558878698018886113169)
                ·
                  refine ⟨6097919159023514164584877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8130558878698018886113169 6097919159023514164584877)
                  ·
                    refine ⟨2286719684633817811719329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6097919159023514164584877 2286719684633817811719329)
                    ·
                      refine ⟨1715039763475363358789497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286719684633817811719329 1715039763475363358789497)
                      ·
                        rfl

theorem cell23_3340028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_3340028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340028 prefixEnd_3340028 := by exact prefixLift 3340028
  have htrace : WordTrace (prefixWord ++ tailWord_3340028) baseStart_3340028 baseEnd_3340028 := by
    simpa [prefixWord, tailWord_3340028, baseEnd_3340028] using wordTrace_append hprefix tailTrace_3340028
  have hstable : (prefixWord ++ tailWord_3340028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340028).length < 2 ^ (prefixWord ++ tailWord_3340028).sum := by decide
  have hdescent : baseEnd_3340028 < baseStart_3340028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340068 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_3340068 : Nat := 118140960795 + 3340068 * 2 ^ 59
def prefixEnd_3340068 : Nat := 4983230072969 + 3 ^ 40 * 3340068 * 2
def baseEnd_3340068 : Nat := 571686767567181067429771

theorem tailTrace_3340068 : CollatzResearch.WordTrace tailWord_3340068 prefixEnd_3340068 571686767567181067429771 := by
  unfold tailWord_3340068
  simp only [CollatzResearch.WordTrace]
  refine ⟨60911144031755774522302429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81214858709007699363069905 60911144031755774522302429)
  ·
    refine ⟨22841679011908415445863411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60911144031755774522302429 22841679011908415445863411)
    ·
      refine ⟨34262518517862623168795117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22841679011908415445863411 34262518517862623168795117)
      ·
        refine ⟨12848444444198483688298169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34262518517862623168795117 12848444444198483688298169)
        ·
          refine ⟨9636333333148862766223627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12848444444198483688298169 9636333333148862766223627)
          ·
            refine ⟨14454499999723294149335441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9636333333148862766223627 14454499999723294149335441)
            ·
              refine ⟨10840874999792470612001581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14454499999723294149335441 10840874999792470612001581)
              ·
                refine ⟨4065328124922176479500593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10840874999792470612001581 4065328124922176479500593)
                ·
                  refine ⟨3048996093691632359625445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065328124922176479500593 3048996093691632359625445)
                  ·
                    refine ⟨571686767567181067429771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3048996093691632359625445 571686767567181067429771)
                    ·
                      rfl

theorem cell23_3340068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_3340068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340068 prefixEnd_3340068 := by exact prefixLift 3340068
  have htrace : WordTrace (prefixWord ++ tailWord_3340068) baseStart_3340068 baseEnd_3340068 := by
    simpa [prefixWord, tailWord_3340068, baseEnd_3340068] using wordTrace_append hprefix tailTrace_3340068
  have hstable : (prefixWord ++ tailWord_3340068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340068).length < 2 ^ (prefixWord ++ tailWord_3340068).sum := by decide
  have hdescent : baseEnd_3340068 < baseStart_3340068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340081 : List Nat := [1, 2, 2, 3, 2, 3, 3, 7]
def baseStart_3340081 : Nat := 118140960795 + 3340081 * 2 ^ 59
def prefixEnd_3340081 : Nat := 4983230072969 + 3 ^ 40 * 3340081 * 2
def baseEnd_3340081 : Nat := 63520999183335246349139

theorem tailTrace_3340081 : CollatzResearch.WordTrace tailWord_3340081 prefixEnd_3340081 63520999183335246349139 := by
  unfold tailWord_3340081
  simp only [CollatzResearch.WordTrace]
  refine ⟨121822762212464452264828097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81215174808309634843218731 121822762212464452264828097)
  ·
    refine ⟨91367071659348339198621073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121822762212464452264828097 91367071659348339198621073)
    ·
      refine ⟨68525303744511254398965805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91367071659348339198621073 68525303744511254398965805)
      ·
        refine ⟨25696988904191720399612177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68525303744511254398965805 25696988904191720399612177)
        ·
          refine ⟨19272741678143790299709133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25696988904191720399612177 19272741678143790299709133)
          ·
            refine ⟨7227278129303921362390925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19272741678143790299709133 7227278129303921362390925)
            ·
              refine ⟨2710229298488970510896597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7227278129303921362390925 2710229298488970510896597)
              ·
                refine ⟨63520999183335246349139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2710229298488970510896597 63520999183335246349139)
                ·
                  rfl

theorem cell23_3340081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 7].length) (baseStart_3340081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340081 prefixEnd_3340081 := by exact prefixLift 3340081
  have htrace : WordTrace (prefixWord ++ tailWord_3340081) baseStart_3340081 baseEnd_3340081 := by
    simpa [prefixWord, tailWord_3340081, baseEnd_3340081] using wordTrace_append hprefix tailTrace_3340081
  have hstable : (prefixWord ++ tailWord_3340081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340081).length < 2 ^ (prefixWord ++ tailWord_3340081).sum := by decide
  have hdescent : baseEnd_3340081 < baseStart_3340081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340102 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3340102 : Nat := 118140960795 + 3340102 * 2 ^ 59
def prefixEnd_3340102 : Nat := 4983230072969 + 3 ^ 40 * 3340102 * 2
def baseEnd_3340102 : Nat := 571692587014598689754719

theorem tailTrace_3340102 : CollatzResearch.WordTrace tailWord_3340102 prefixEnd_3340102 571692587014598689754719 := by
  unfold tailWord_3340102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806985254543386651604455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81215685430258915234228373 3806985254543386651604455)
  ·
    refine ⟨5710477881815079977406683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3806985254543386651604455 5710477881815079977406683)
    ·
      refine ⟨8565716822722619966110025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710477881815079977406683 8565716822722619966110025)
      ·
        refine ⟨6424287617041964974582519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8565716822722619966110025 6424287617041964974582519)
        ·
          refine ⟨9636431425562947461873779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424287617041964974582519 9636431425562947461873779)
          ·
            refine ⟨14454647138344421192810669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9636431425562947461873779 14454647138344421192810669)
            ·
              refine ⟨5420492676879157947304001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14454647138344421192810669 5420492676879157947304001)
              ·
                refine ⟨4065369507659368460478001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5420492676879157947304001 4065369507659368460478001)
                ·
                  refine ⟨3049027130744526345358501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065369507659368460478001 3049027130744526345358501)
                  ·
                    refine ⟨571692587014598689754719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3049027130744526345358501 571692587014598689754719)
                    ·
                      rfl

theorem cell23_3340102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3340102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340102 prefixEnd_3340102 := by exact prefixLift 3340102
  have htrace : WordTrace (prefixWord ++ tailWord_3340102) baseStart_3340102 baseEnd_3340102 := by
    simpa [prefixWord, tailWord_3340102, baseEnd_3340102] using wordTrace_append hprefix tailTrace_3340102
  have hstable : (prefixWord ++ tailWord_3340102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340102).length < 2 ^ (prefixWord ++ tailWord_3340102).sum := by decide
  have hdescent : baseEnd_3340102 < baseStart_3340102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340109 : List Nat := [1, 6, 1, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3340109 : Nat := 118140960795 + 3340109 * 2 ^ 59
def prefixEnd_3340109 : Nat := 4983230072969 + 3 ^ 40 * 3340109 * 2
def baseEnd_3340109 : Nat := 1715081355408377541876625

theorem tailTrace_3340109 : CollatzResearch.WordTrace tailWord_3340109 prefixEnd_3340109 1715081355408377541876625 := by
  unfold tailWord_3340109
  simp only [CollatzResearch.WordTrace]
  refine ⟨121823783456363013046847381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81215855637575342031231587 121823783456363013046847381)
  ·
    refine ⟨5710489849517016236570971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121823783456363013046847381 5710489849517016236570971)
    ·
      refine ⟨8565734774275524354856457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710489849517016236570971 8565734774275524354856457)
      ·
        refine ⟨6424301080706643266142343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8565734774275524354856457 6424301080706643266142343)
        ·
          refine ⟨9636451621059964899213515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424301080706643266142343 9636451621059964899213515)
          ·
            refine ⟨14454677431589947348820273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9636451621059964899213515 14454677431589947348820273)
            ·
              refine ⟨10841008073692460511615205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14454677431589947348820273 10841008073692460511615205)
              ·
                refine ⟨2032689013817336345927851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10841008073692460511615205 2032689013817336345927851)
                ·
                  refine ⟨3049033520726004518891777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032689013817336345927851 3049033520726004518891777)
                  ·
                    refine ⟨2286775140544503389168833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3049033520726004518891777 2286775140544503389168833)
                    ·
                      refine ⟨1715081355408377541876625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286775140544503389168833 1715081355408377541876625)
                      ·
                        rfl

theorem cell23_3340109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3340109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340109 prefixEnd_3340109 := by exact prefixLift 3340109
  have htrace : WordTrace (prefixWord ++ tailWord_3340109) baseStart_3340109 baseEnd_3340109 := by
    simpa [prefixWord, tailWord_3340109, baseEnd_3340109] using wordTrace_append hprefix tailTrace_3340109
  have hstable : (prefixWord ++ tailWord_3340109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340109).length < 2 ^ (prefixWord ++ tailWord_3340109).sum := by decide
  have hdescent : baseEnd_3340109 < baseStart_3340109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340135 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_3340135 : Nat := 118140960795 + 3340135 * 2 ^ 59
def prefixEnd_3340135 : Nat := 4983230072969 + 3 ^ 40 * 3340135 * 2
def baseEnd_3340135 : Nat := 1715094705905394440151505

theorem tailTrace_3340135 : CollatzResearch.WordTrace tailWord_3340135 prefixEnd_3340135 1715094705905394440151505 := by
  unfold tailWord_3340135
  simp only [CollatzResearch.WordTrace]
  refine ⟨121824731754268819487293859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81216487836179212991529239 121824731754268819487293859)
  ·
    refine ⟨182737097631403229230940789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121824731754268819487293859 182737097631403229230940789)
    ·
      refine ⟨17131602902944052740400699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182737097631403229230940789 17131602902944052740400699)
      ·
        refine ⟨25697404354416079110601049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17131602902944052740400699 25697404354416079110601049)
        ·
          refine ⟨19273053265812059332950787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25697404354416079110601049 19273053265812059332950787)
          ·
            refine ⟨28909579898718088999426181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19273053265812059332950787 28909579898718088999426181)
            ·
              refine ⟨5420546231009641687392409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28909579898718088999426181 5420546231009641687392409)
              ·
                refine ⟨4065409673257231265544307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5420546231009641687392409 4065409673257231265544307)
                ·
                  refine ⟨6098114509885846898316461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065409673257231265544307 6098114509885846898316461)
                  ·
                    refine ⟨2286792941207192586868673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6098114509885846898316461 2286792941207192586868673)
                    ·
                      refine ⟨1715094705905394440151505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286792941207192586868673 1715094705905394440151505)
                      ·
                        rfl

theorem cell23_3340135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_3340135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340135 prefixEnd_3340135 := by exact prefixLift 3340135
  have htrace : WordTrace (prefixWord ++ tailWord_3340135) baseStart_3340135 baseEnd_3340135 := by
    simpa [prefixWord, tailWord_3340135, baseEnd_3340135] using wordTrace_append hprefix tailTrace_3340135
  have hstable : (prefixWord ++ tailWord_3340135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340135).length < 2 ^ (prefixWord ++ tailWord_3340135).sum := by decide
  have hdescent : baseEnd_3340135 < baseStart_3340135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340154 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_3340154 : Nat := 118140960795 + 3340154 * 2 ^ 59
def prefixEnd_3340154 : Nat := 4983230072969 + 3 ^ 40 * 3340154 * 2
def baseEnd_3340154 : Nat := 190567162448647762868213

theorem tailTrace_3340154 : CollatzResearch.WordTrace tailWord_3340154 prefixEnd_3340154 190567162448647762868213 := by
  unfold tailWord_3340154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30456356185299996433058879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81216949827466657154823677 30456356185299996433058879)
  ·
    refine ⟨45684534277949994649588319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30456356185299996433058879 45684534277949994649588319)
    ·
      refine ⟨68526801416924991974382479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45684534277949994649588319 68526801416924991974382479)
      ·
        refine ⟨102790202125387487961573719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68526801416924991974382479 102790202125387487961573719)
        ·
          refine ⟨154185303188081231942360579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102790202125387487961573719 154185303188081231942360579)
          ·
            refine ⟨231277954782121847913540869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154185303188081231942360579 231277954782121847913540869)
            ·
              refine ⟨43364616521647846483788913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231277954782121847913540869 43364616521647846483788913)
              ·
                refine ⟨32523462391235884862841685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43364616521647846483788913 32523462391235884862841685)
                ·
                  refine ⟨190567162448647762868213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32523462391235884862841685 190567162448647762868213)
                  ·
                    rfl

theorem cell23_3340154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_3340154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340154 prefixEnd_3340154 := by exact prefixLift 3340154
  have htrace : WordTrace (prefixWord ++ tailWord_3340154) baseStart_3340154 baseEnd_3340154 := by
    simpa [prefixWord, tailWord_3340154, baseEnd_3340154] using wordTrace_append hprefix tailTrace_3340154
  have hstable : (prefixWord ++ tailWord_3340154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340154).length < 2 ^ (prefixWord ++ tailWord_3340154).sum := by decide
  have hdescent : baseEnd_3340154 < baseStart_3340154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340165 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 2, 2, 2]
def baseStart_3340165 : Nat := 118140960795 + 3340165 * 2 ^ 59
def prefixEnd_3340165 : Nat := 4983230072969 + 3 ^ 40 * 3340165 * 2
def baseEnd_3340165 : Nat := 1715110110325029322776367

theorem tailTrace_3340165 : CollatzResearch.WordTrace tailWord_3340165 prefixEnd_3340165 1715110110325029322776367 := by
  unfold tailWord_3340165
  simp only [CollatzResearch.WordTrace]
  refine ⟨121825825944160134610885949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81217217296106756407257299 121825825944160134610885949)
  ·
    refine ⟨45684684729060050479082231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121825825944160134610885949 45684684729060050479082231)
    ·
      refine ⟨68527027093590075718623347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45684684729060050479082231 68527027093590075718623347)
      ·
        refine ⟨102790540640385113577935021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68527027093590075718623347 102790540640385113577935021)
        ·
          refine ⟨38546452740144417591725633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102790540640385113577935021 38546452740144417591725633)
          ·
            refine ⟨28909839555108313193794225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38546452740144417591725633 28909839555108313193794225)
            ·
              refine ⟨21682379666331234895345669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28909839555108313193794225 21682379666331234895345669)
              ·
                refine ⟨4065446187437106542877313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21682379666331234895345669 4065446187437106542877313)
                ·
                  refine ⟨3049084640577829907157985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065446187437106542877313 3049084640577829907157985)
                  ·
                    refine ⟨2286813480433372430368489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3049084640577829907157985 2286813480433372430368489)
                    ·
                      refine ⟨1715110110325029322776367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286813480433372430368489 1715110110325029322776367)
                      ·
                        rfl

theorem cell23_3340165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_3340165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340165 prefixEnd_3340165 := by exact prefixLift 3340165
  have htrace : WordTrace (prefixWord ++ tailWord_3340165) baseStart_3340165 baseEnd_3340165 := by
    simpa [prefixWord, tailWord_3340165, baseEnd_3340165] using wordTrace_append hprefix tailTrace_3340165
  have hstable : (prefixWord ++ tailWord_3340165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340165).length < 2 ^ (prefixWord ++ tailWord_3340165).sum := by decide
  have hdescent : baseEnd_3340165 < baseStart_3340165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340181 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_3340181 : Nat := 118140960795 + 3340181 * 2 ^ 59
def prefixEnd_3340181 : Nat := 4983230072969 + 3 ^ 40 * 3340181 * 2
def baseEnd_3340181 : Nat := 1715118326015501260176293

theorem tailTrace_3340181 : CollatzResearch.WordTrace tailWord_3340181 prefixEnd_3340181 1715118326015501260176293 := by
  unfold tailWord_3340181
  simp only [CollatzResearch.WordTrace]
  refine ⟨121826409512102169343468397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81217606341401446228978931 121826409512102169343468397)
  ·
    refine ⟨45684903567038313503800649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121826409512102169343468397 45684903567038313503800649)
    ·
      refine ⟨34263677675278735127850487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45684903567038313503800649 34263677675278735127850487)
      ·
        refine ⟨51395516512918102691775731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34263677675278735127850487 51395516512918102691775731)
        ·
          refine ⟨77093274769377154037663597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51395516512918102691775731 77093274769377154037663597)
          ·
            refine ⟨28909978038516432764123849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77093274769377154037663597 28909978038516432764123849)
            ·
              refine ⟨21682483528887324573092887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28909978038516432764123849 21682483528887324573092887)
              ·
                refine ⟨32523725293330986859639331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21682483528887324573092887 32523725293330986859639331)
                ·
                  refine ⟨48785587939996480289458997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32523725293330986859639331 48785587939996480289458997)
                  ·
                    refine ⟨4573648869374670027136781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48785587939996480289458997 4573648869374670027136781)
                    ·
                      refine ⟨1715118326015501260176293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4573648869374670027136781 1715118326015501260176293)
                      ·
                        rfl

theorem cell23_3340181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_3340181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340181 prefixEnd_3340181 := by exact prefixLift 3340181
  have htrace : WordTrace (prefixWord ++ tailWord_3340181) baseStart_3340181 baseEnd_3340181 := by
    simpa [prefixWord, tailWord_3340181, baseEnd_3340181] using wordTrace_append hprefix tailTrace_3340181
  have hstable : (prefixWord ++ tailWord_3340181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340181).length < 2 ^ (prefixWord ++ tailWord_3340181).sum := by decide
  have hdescent : baseEnd_3340181 < baseStart_3340181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340222 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_3340222 : Nat := 118140960795 + 3340222 * 2 ^ 59
def prefixEnd_3340222 : Nat := 4983230072969 + 3 ^ 40 * 3340222 * 2
def baseEnd_3340222 : Nat := 190571042080259511084845

theorem tailTrace_3340222 : CollatzResearch.WordTrace tailWord_3340222 prefixEnd_3340222 190571042080259511084845 := by
  unfold tailWord_3340222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228488113119204168213865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81218603269969088897140613 15228488113119204168213865)
  ·
    refine ⟨11421366084839403126160399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15228488113119204168213865 11421366084839403126160399)
    ·
      refine ⟨17132049127259104689240599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11421366084839403126160399 17132049127259104689240599)
      ·
        refine ⟨25698073690888657033860899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17132049127259104689240599 25698073690888657033860899)
        ·
          refine ⟨38547110536332985550791349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25698073690888657033860899 38547110536332985550791349)
          ·
            refine ⟨3613791612781217395386689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38547110536332985550791349 3613791612781217395386689)
            ·
              refine ⟨2710343709585913046540017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613791612781217395386689 2710343709585913046540017)
              ·
                refine ⟨2032757782189434784905013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710343709585913046540017 2032757782189434784905013)
                ·
                  refine ⟨190571042080259511084845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2032757782189434784905013 190571042080259511084845)
                  ·
                    rfl

theorem cell23_3340222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_3340222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340222 prefixEnd_3340222 := by exact prefixLift 3340222
  have htrace : WordTrace (prefixWord ++ tailWord_3340222) baseStart_3340222 baseEnd_3340222 := by
    simpa [prefixWord, tailWord_3340222, baseEnd_3340222] using wordTrace_append hprefix tailTrace_3340222
  have hstable : (prefixWord ++ tailWord_3340222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340222).length < 2 ^ (prefixWord ++ tailWord_3340222).sum := by decide
  have hdescent : baseEnd_3340222 < baseStart_3340222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340248 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 3, 4]
def baseStart_3340248 : Nat := 118140960795 + 3340248 * 2 ^ 59
def prefixEnd_3340248 : Nat := 4983230072969 + 3 ^ 40 * 3340248 * 2
def baseEnd_3340248 : Nat := 571717576406450832679495

theorem tailTrace_3340248 : CollatzResearch.WordTrace tailWord_3340248 prefixEnd_3340248 571717576406450832679495 := by
  unfold tailWord_3340248
  simp only [CollatzResearch.WordTrace]
  refine ⟨60914426601429719893078699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81219235468572959857438265 60914426601429719893078699)
  ·
    refine ⟨91371639902144579839618049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60914426601429719893078699 91371639902144579839618049)
    ·
      refine ⟨68528729926608434879713537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91371639902144579839618049 68528729926608434879713537)
      ·
        refine ⟨51396547444956326159785153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68528729926608434879713537 51396547444956326159785153)
        ·
          refine ⟨38547410583717244619838865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51396547444956326159785153 38547410583717244619838865)
          ·
            refine ⟨28910557937787933464879149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38547410583717244619838865 28910557937787933464879149)
            ·
              refine ⟨10841459226670475049329681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28910557937787933464879149 10841459226670475049329681)
              ·
                refine ⟨8131094420002856286997261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10841459226670475049329681 8131094420002856286997261)
                ·
                  refine ⟨3049160407501071107623973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8131094420002856286997261 3049160407501071107623973)
                  ·
                    refine ⟨571717576406450832679495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3049160407501071107623973 571717576406450832679495)
                    ·
                      rfl

theorem cell23_3340248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_3340248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340248 prefixEnd_3340248 := by exact prefixLift 3340248
  have htrace : WordTrace (prefixWord ++ tailWord_3340248) baseStart_3340248 baseEnd_3340248 := by
    simpa [prefixWord, tailWord_3340248, baseEnd_3340248] using wordTrace_append hprefix tailTrace_3340248
  have hstable : (prefixWord ++ tailWord_3340248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340248).length < 2 ^ (prefixWord ++ tailWord_3340248).sum := by decide
  have hdescent : baseEnd_3340248 < baseStart_3340248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340252 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3340252 : Nat := 118140960795 + 3340252 * 2 ^ 59
def prefixEnd_3340252 : Nat := 4983230072969 + 3 ^ 40 * 3340252 * 2
def baseEnd_3340252 : Nat := 571718261047323494129489

theorem tailTrace_3340252 : CollatzResearch.WordTrace tailWord_3340252 prefixEnd_3340252 571718261047323494129489 := by
  unfold tailWord_3340252
  simp only [CollatzResearch.WordTrace]
  refine ⟨60914499547422474234651505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81219332729896632312868673 60914499547422474234651505)
  ·
    refine ⟨45685874660566855675988629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60914499547422474234651505 45685874660566855675988629)
    ·
      refine ⟨2141525374714071359811967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45685874660566855675988629 2141525374714071359811967)
      ·
        refine ⟨3212288062071107039717951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141525374714071359811967 3212288062071107039717951)
        ·
          refine ⟨4818432093106660559576927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212288062071107039717951 4818432093106660559576927)
          ·
            refine ⟨7227648139659990839365391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818432093106660559576927 7227648139659990839365391)
            ·
              refine ⟨10841472209489986259048087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7227648139659990839365391 10841472209489986259048087)
              ·
                refine ⟨16262208314234979388572131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10841472209489986259048087 16262208314234979388572131)
                ·
                  refine ⟨24393312471352469082858197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16262208314234979388572131 24393312471352469082858197)
                  ·
                    refine ⟨571718261047323494129489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24393312471352469082858197 571718261047323494129489)
                    ·
                      rfl

theorem cell23_3340252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3340252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340252 prefixEnd_3340252 := by exact prefixLift 3340252
  have htrace : WordTrace (prefixWord ++ tailWord_3340252) baseStart_3340252 baseEnd_3340252 := by
    simpa [prefixWord, tailWord_3340252, baseEnd_3340252] using wordTrace_append hprefix tailTrace_3340252
  have hstable : (prefixWord ++ tailWord_3340252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340252).length < 2 ^ (prefixWord ++ tailWord_3340252).sum := by decide
  have hdescent : baseEnd_3340252 < baseStart_3340252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340255 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_3340255 : Nat := 118140960795 + 3340255 * 2 ^ 59
def prefixEnd_3340255 : Nat := 4983230072969 + 3 ^ 40 * 3340255 * 2
def baseEnd_3340255 : Nat := 1715156323583933970650953

theorem tailTrace_3340255 : CollatzResearch.WordTrace tailWord_3340255 prefixEnd_3340255 1715156323583933970650953 := by
  unfold tailWord_3340255
  simp only [CollatzResearch.WordTrace]
  refine ⟨121829108513834079981662219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81219405675889386654441479 121829108513834079981662219)
  ·
    refine ⟨182743662770751119972493329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121829108513834079981662219 182743662770751119972493329)
    ·
      refine ⟨137057747078063339979369997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182743662770751119972493329 137057747078063339979369997)
      ·
        refine ⟨51396655154273752492263749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137057747078063339979369997 51396655154273752492263749)
        ·
          refine ⟨9636872841426328592299453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51396655154273752492263749 9636872841426328592299453)
          ·
            refine ⟨3613827315534873222112295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9636872841426328592299453 3613827315534873222112295)
            ·
              refine ⟨5420740973302309833168443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613827315534873222112295 5420740973302309833168443)
              ·
                refine ⟨8131111459953464749752665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420740973302309833168443 8131111459953464749752665)
                ·
                  refine ⟨6098333594965098562314499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8131111459953464749752665 6098333594965098562314499)
                  ·
                    refine ⟨9147500392447647843471749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6098333594965098562314499 9147500392447647843471749)
                    ·
                      refine ⟨1715156323583933970650953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9147500392447647843471749 1715156323583933970650953)
                      ·
                        rfl

theorem cell23_3340255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_3340255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340255 prefixEnd_3340255 := by exact prefixLift 3340255
  have htrace : WordTrace (prefixWord ++ tailWord_3340255) baseStart_3340255 baseEnd_3340255 := by
    simpa [prefixWord, tailWord_3340255, baseEnd_3340255] using wordTrace_append hprefix tailTrace_3340255
  have hstable : (prefixWord ++ tailWord_3340255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340255).length < 2 ^ (prefixWord ++ tailWord_3340255).sum := by decide
  have hdescent : baseEnd_3340255 < baseStart_3340255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340281 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3340281 : Nat := 118140960795 + 3340281 * 2 ^ 59
def prefixEnd_3340281 : Nat := 4983230072969 + 3 ^ 40 * 3340281 * 2
def baseEnd_3340281 : Nat := 1715169674080950868925833

theorem tailTrace_3340281 : CollatzResearch.WordTrace tailWord_3340281 prefixEnd_3340281 1715169674080950868925833 := by
  unfold tailWord_3340281
  simp only [CollatzResearch.WordTrace]
  refine ⟨121830056811739886422108697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81220037874493257614739131 121830056811739886422108697)
  ·
    refine ⟨91372542608804914816581523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121830056811739886422108697 91372542608804914816581523)
    ·
      refine ⟨137058813913207372224872285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91372542608804914816581523 137058813913207372224872285)
      ·
        refine ⟨51397055217452764584327107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137058813913207372224872285 51397055217452764584327107)
        ·
          refine ⟨77095582826179146876490661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51397055217452764584327107 77095582826179146876490661)
          ·
            refine ⟨14455421779908590039341999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77095582826179146876490661 14455421779908590039341999)
            ·
              refine ⟨21683132669862885059012999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14455421779908590039341999 21683132669862885059012999)
              ·
                refine ⟨32524699004794327588519499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21683132669862885059012999 32524699004794327588519499)
                ·
                  refine ⟨48787048507191491382779249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32524699004794327588519499 48787048507191491382779249)
                  ·
                    refine ⟨36590286380393618537084437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48787048507191491382779249 36590286380393618537084437)
                    ·
                      refine ⟨1715169674080950868925833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36590286380393618537084437 1715169674080950868925833)
                      ·
                        rfl

theorem cell23_3340281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3340281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340281 prefixEnd_3340281 := by exact prefixLift 3340281
  have htrace : WordTrace (prefixWord ++ tailWord_3340281) baseStart_3340281 baseEnd_3340281 := by
    simpa [prefixWord, tailWord_3340281, baseEnd_3340281] using wordTrace_append hprefix tailTrace_3340281
  have hstable : (prefixWord ++ tailWord_3340281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340281).length < 2 ^ (prefixWord ++ tailWord_3340281).sum := by decide
  have hdescent : baseEnd_3340281 < baseStart_3340281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340291 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 5, 5]
def baseStart_3340291 : Nat := 118140960795 + 3340291 * 2 ^ 59
def prefixEnd_3340291 : Nat := 4983230072969 + 3 ^ 40 * 3340291 * 2
def baseEnd_3340291 : Nat := 571724936295831943266929

theorem tailTrace_3340291 : CollatzResearch.WordTrace tailWord_3340291 prefixEnd_3340291 571724936295831943266929 := by
  unfold tailWord_3340291
  simp only [CollatzResearch.WordTrace]
  refine ⟨121830421541703658129972727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81220281027802438753315151 121830421541703658129972727)
  ·
    refine ⟨182745632312555487194959091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121830421541703658129972727 182745632312555487194959091)
    ·
      refine ⟨274118448468833230792438637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182745632312555487194959091 274118448468833230792438637)
      ·
        refine ⟨102794418175812461547164489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274118448468833230792438637 102794418175812461547164489)
        ·
          refine ⟨77095813631859346160373367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102794418175812461547164489 77095813631859346160373367)
          ·
            refine ⟨115643720447789019240560051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77095813631859346160373367 115643720447789019240560051)
            ·
              refine ⟨173465580671683528860840077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115643720447789019240560051 173465580671683528860840077)
              ·
                refine ⟨65049592751881323322815029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173465580671683528860840077 65049592751881323322815029)
                ·
                  refine ⟨6098399320488874061513909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65049592751881323322815029 6098399320488874061513909)
                  ·
                    refine ⟨571724936295831943266929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6098399320488874061513909 571724936295831943266929)
                    ·
                      rfl

theorem cell23_3340291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 5].length) (baseStart_3340291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340291 prefixEnd_3340291 := by exact prefixLift 3340291
  have htrace : WordTrace (prefixWord ++ tailWord_3340291) baseStart_3340291 baseEnd_3340291 := by
    simpa [prefixWord, tailWord_3340291, baseEnd_3340291] using wordTrace_append hprefix tailTrace_3340291
  have hstable : (prefixWord ++ tailWord_3340291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340291).length < 2 ^ (prefixWord ++ tailWord_3340291).sum := by decide
  have hdescent : baseEnd_3340291 < baseStart_3340291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340295 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 6]
def baseStart_3340295 : Nat := 118140960795 + 3340295 * 2 ^ 59
def prefixEnd_3340295 : Nat := 4983230072969 + 3 ^ 40 * 3340295 * 2
def baseEnd_3340295 : Nat := 190575206978901534905641

theorem tailTrace_3340295 : CollatzResearch.WordTrace tailWord_3340295 prefixEnd_3340295 190575206978901534905641 := by
  unfold tailWord_3340295
  simp only [CollatzResearch.WordTrace]
  refine ⟨121830567433689166813118339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81220378289126111208745559 121830567433689166813118339)
  ·
    refine ⟨182745851150533750219677509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121830567433689166813118339 182745851150533750219677509)
    ·
      refine ⟨34264847090725078166189533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182745851150533750219677509 34264847090725078166189533)
      ·
        refine ⟨12849317659021904312321075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34264847090725078166189533 12849317659021904312321075)
        ·
          refine ⟨19273976488532856468481613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12849317659021904312321075 19273976488532856468481613)
          ·
            refine ⟨7227741183199821175680605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19273976488532856468481613 7227741183199821175680605)
            ·
              refine ⟨2710402943699932940880227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7227741183199821175680605 2710402943699932940880227)
              ·
                refine ⟨4065604415549899411320341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710402943699932940880227 4065604415549899411320341)
                ·
                  refine ⟨190575206978901534905641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4065604415549899411320341 190575206978901534905641)
                  ·
                    rfl

theorem cell23_3340295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 6].length) (baseStart_3340295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340295 prefixEnd_3340295 := by exact prefixLift 3340295
  have htrace : WordTrace (prefixWord ++ tailWord_3340295) baseStart_3340295 baseEnd_3340295 := by
    simpa [prefixWord, tailWord_3340295, baseEnd_3340295] using wordTrace_append hprefix tailTrace_3340295
  have hstable : (prefixWord ++ tailWord_3340295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340295).length < 2 ^ (prefixWord ++ tailWord_3340295).sum := by decide
  have hdescent : baseEnd_3340295 < baseStart_3340295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340348 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3340348 : Nat := 118140960795 + 3340348 * 2 ^ 59
def prefixEnd_3340348 : Nat := 4983230072969 + 3 ^ 40 * 3340348 * 2
def baseEnd_3340348 : Nat := 1715204077284802106788025

theorem tailTrace_3340348 : CollatzResearch.WordTrace tailWord_3340348 prefixEnd_3340348 1715204077284802106788025 := by
  unfold tailWord_3340348
  simp only [CollatzResearch.WordTrace]
  refine ⟨60916250251248578432398849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81221667001664771243198465 60916250251248578432398849)
  ·
    refine ⟨45687187688436433824299137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60916250251248578432398849 45687187688436433824299137)
    ·
      refine ⟨34265390766327325368224353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45687187688436433824299137 34265390766327325368224353)
      ·
        refine ⟨25699043074745494026168265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34265390766327325368224353 25699043074745494026168265)
        ·
          refine ⟨19274282306059120519626199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25699043074745494026168265 19274282306059120519626199)
          ·
            refine ⟨28911423459088680779439299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274282306059120519626199 28911423459088680779439299)
            ·
              refine ⟨43367135188633021169158949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28911423459088680779439299 43367135188633021169158949)
              ·
                refine ⟨8131337847868691469217303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43367135188633021169158949 8131337847868691469217303)
                ·
                  refine ⟨12197006771803037203825955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8131337847868691469217303 12197006771803037203825955)
                  ·
                    refine ⟨18295510157704555805738933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12197006771803037203825955 18295510157704555805738933)
                    ·
                      refine ⟨1715204077284802106788025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18295510157704555805738933 1715204077284802106788025)
                      ·
                        rfl

theorem cell23_3340348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3340348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340348 prefixEnd_3340348 := by exact prefixLift 3340348
  have htrace : WordTrace (prefixWord ++ tailWord_3340348) baseStart_3340348 baseEnd_3340348 := by
    simpa [prefixWord, tailWord_3340348, baseEnd_3340348] using wordTrace_append hprefix tailTrace_3340348
  have hstable : (prefixWord ++ tailWord_3340348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340348).length < 2 ^ (prefixWord ++ tailWord_3340348).sum := by decide
  have hdescent : baseEnd_3340348 < baseStart_3340348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340351 : List Nat := [1, 1, 2, 2, 3, 1, 3, 10]
def baseStart_3340351 : Nat := 118140960795 + 3340351 * 2 ^ 59
def prefixEnd_3340351 : Nat := 4983230072969 + 3 ^ 40 * 3340351 * 2
def baseEnd_3340351 : Nat := 63526133989880207224093

theorem tailTrace_3340351 : CollatzResearch.WordTrace tailWord_3340351 prefixEnd_3340351 63526133989880207224093 := by
  unfold tailWord_3340351
  simp only [CollatzResearch.WordTrace]
  refine ⟨121832609921486288377156907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81221739947657525584771271 121832609921486288377156907)
  ·
    refine ⟨182748914882229432565735361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121832609921486288377156907 182748914882229432565735361)
    ·
      refine ⟨137061686161672074424301521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182748914882229432565735361 137061686161672074424301521)
      ·
        refine ⟨102796264621254055818226141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137061686161672074424301521 102796264621254055818226141)
        ·
          refine ⟨38548599232970270931834803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102796264621254055818226141 38548599232970270931834803)
          ·
            refine ⟨57822898849455406397752205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38548599232970270931834803 57822898849455406397752205)
            ·
              refine ⟨21683587068545777399157077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57822898849455406397752205 21683587068545777399157077)
              ·
                refine ⟨63526133989880207224093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21683587068545777399157077 63526133989880207224093)
                ·
                  rfl

theorem cell23_3340351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 10].length) (baseStart_3340351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340351 prefixEnd_3340351 := by exact prefixLift 3340351
  have htrace : WordTrace (prefixWord ++ tailWord_3340351) baseStart_3340351 baseEnd_3340351 := by
    simpa [prefixWord, tailWord_3340351, baseEnd_3340351] using wordTrace_append hprefix tailTrace_3340351
  have hstable : (prefixWord ++ tailWord_3340351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340351).length < 2 ^ (prefixWord ++ tailWord_3340351).sum := by decide
  have hdescent : baseEnd_3340351 < baseStart_3340351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340371 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_3340371 : Nat := 118140960795 + 3340371 * 2 ^ 59
def prefixEnd_3340371 : Nat := 4983230072969 + 3 ^ 40 * 3340371 * 2
def baseEnd_3340371 : Nat := 1715215887339855516800419

theorem tailTrace_3340371 : CollatzResearch.WordTrace tailWord_3340371 prefixEnd_3340371 1715215887339855516800419 := by
  unfold tailWord_3340371
  simp only [CollatzResearch.WordTrace]
  refine ⟨121833339381413831792884967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81222226254275887861923311 121833339381413831792884967)
  ·
    refine ⟨182750009072120747689327451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121833339381413831792884967 182750009072120747689327451)
    ·
      refine ⟨274125013608181121533991177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182750009072120747689327451 274125013608181121533991177)
      ·
        refine ⟨205593760206135841150493383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274125013608181121533991177 205593760206135841150493383)
        ·
          refine ⟨308390640309203761725740075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205593760206135841150493383 308390640309203761725740075)
          ·
            refine ⟨462585960463805642588610113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308390640309203761725740075 462585960463805642588610113)
            ·
              refine ⟨346939470347854231941457585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462585960463805642588610113 346939470347854231941457585)
              ·
                refine ⟨260204602760890673956093189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346939470347854231941457585 260204602760890673956093189)
                ·
                  refine ⟨48788363017667001366767473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260204602760890673956093189 48788363017667001366767473)
                  ·
                    refine ⟨36591272263250251025075605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48788363017667001366767473 36591272263250251025075605)
                    ·
                      refine ⟨1715215887339855516800419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36591272263250251025075605 1715215887339855516800419)
                      ·
                        rfl

theorem cell23_3340371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_3340371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340371 prefixEnd_3340371 := by exact prefixLift 3340371
  have htrace : WordTrace (prefixWord ++ tailWord_3340371) baseStart_3340371 baseEnd_3340371 := by
    simpa [prefixWord, tailWord_3340371, baseEnd_3340371] using wordTrace_append hprefix tailTrace_3340371
  have hstable : (prefixWord ++ tailWord_3340371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340371).length < 2 ^ (prefixWord ++ tailWord_3340371).sum := by decide
  have hdescent : baseEnd_3340371 < baseStart_3340371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340396 : List Nat := [2, 2, 1, 1, 3, 3, 4, 2, 1, 2, 2]
def baseStart_3340396 : Nat := 118140960795 + 3340396 * 2 ^ 59
def prefixEnd_3340396 : Nat := 4983230072969 + 3 ^ 40 * 3340396 * 2
def baseEnd_3340396 : Nat := 1715228724356217918987805

theorem tailTrace_3340396 : CollatzResearch.WordTrace tailWord_3340396 prefixEnd_3340396 1715228724356217918987805 := by
  unfold tailWord_3340396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60917125603161630531272521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81222834137548840708363361 60917125603161630531272521)
  ·
    refine ⟨45687844202371222898454391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60917125603161630531272521 45687844202371222898454391)
    ·
      refine ⟨68531766303556834347681587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45687844202371222898454391 68531766303556834347681587)
      ·
        refine ⟨102797649455335251521522381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68531766303556834347681587 102797649455335251521522381)
        ·
          refine ⟨38549118545750719320570893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102797649455335251521522381 38549118545750719320570893)
          ·
            refine ⟨14455919454656519745214085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38549118545750719320570893 14455919454656519745214085)
            ·
              refine ⟨2710484897748097452227641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14455919454656519745214085 2710484897748097452227641)
              ·
                refine ⟨2032863673311073089170731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710484897748097452227641 2032863673311073089170731)
                ·
                  refine ⟨3049295509966609633756097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032863673311073089170731 3049295509966609633756097)
                  ·
                    refine ⟨2286971632474957225317073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3049295509966609633756097 2286971632474957225317073)
                    ·
                      refine ⟨1715228724356217918987805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2286971632474957225317073 1715228724356217918987805)
                      ·
                        rfl

theorem cell23_3340396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_3340396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340396 prefixEnd_3340396 := by exact prefixLift 3340396
  have htrace : WordTrace (prefixWord ++ tailWord_3340396) baseStart_3340396 baseEnd_3340396 := by
    simpa [prefixWord, tailWord_3340396, baseEnd_3340396] using wordTrace_append hprefix tailTrace_3340396
  have hstable : (prefixWord ++ tailWord_3340396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340396).length < 2 ^ (prefixWord ++ tailWord_3340396).sum := by decide
  have hdescent : baseEnd_3340396 < baseStart_3340396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340398 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3340398 : Nat := 118140960795 + 3340398 * 2 ^ 59
def prefixEnd_3340398 : Nat := 4983230072969 + 3 ^ 40 * 3340398 * 2
def baseEnd_3340398 : Nat := 571743250439175637054265

theorem tailTrace_3340398 : CollatzResearch.WordTrace tailWord_3340398 prefixEnd_3340398 571743250439175637054265 := by
  unfold tailWord_3340398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229290519039501925514731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81222882768210676936078565 15229290519039501925514731)
  ·
    refine ⟨22843935778559252888272097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15229290519039501925514731 22843935778559252888272097)
    ·
      refine ⟨17132951833919439666204073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22843935778559252888272097 17132951833919439666204073)
      ·
        refine ⟨12849713875439579749653055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17132951833919439666204073 12849713875439579749653055)
        ·
          refine ⟨19274570813159369624479583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12849713875439579749653055 19274570813159369624479583)
          ·
            refine ⟨28911856219739054436719375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19274570813159369624479583 28911856219739054436719375)
            ·
              refine ⟨43367784329608581655079063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28911856219739054436719375 43367784329608581655079063)
              ·
                refine ⟨65051676494412872482618595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43367784329608581655079063 65051676494412872482618595)
                ·
                  refine ⟨97577514741619308723927893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65051676494412872482618595 97577514741619308723927893)
                  ·
                    refine ⟨571743250439175637054265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 97577514741619308723927893 571743250439175637054265)
                    ·
                      rfl

theorem cell23_3340398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3340398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340398 prefixEnd_3340398 := by exact prefixLift 3340398
  have htrace : WordTrace (prefixWord ++ tailWord_3340398) baseStart_3340398 baseEnd_3340398 := by
    simpa [prefixWord, tailWord_3340398, baseEnd_3340398] using wordTrace_append hprefix tailTrace_3340398
  have hstable : (prefixWord ++ tailWord_3340398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340398).length < 2 ^ (prefixWord ++ tailWord_3340398).sum := by decide
  have hdescent : baseEnd_3340398 < baseStart_3340398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340412 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3340412 : Nat := 118140960795 + 3340412 * 2 ^ 59
def prefixEnd_3340412 : Nat := 4983230072969 + 3 ^ 40 * 3340412 * 2
def baseEnd_3340412 : Nat := 1715236940046689856387731

theorem tailTrace_3340412 : CollatzResearch.WordTrace tailWord_3340412 prefixEnd_3340412 1715236940046689856387731 := by
  unfold tailWord_3340412
  simp only [CollatzResearch.WordTrace]
  refine ⟨60917417387132647897563745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81223223182843530530084993 60917417387132647897563745)
  ·
    refine ⟨45688063040349485923172809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60917417387132647897563745 45688063040349485923172809)
    ·
      refine ⟨34266047280262114442379607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45688063040349485923172809 34266047280262114442379607)
      ·
        refine ⟨51399070920393171663569411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34266047280262114442379607 51399070920393171663569411)
        ·
          refine ⟨77098606380589757495354117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51399070920393171663569411 77098606380589757495354117)
          ·
            refine ⟨14455988696360579530378897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77098606380589757495354117 14455988696360579530378897)
            ·
              refine ⟨10841991522270434647784173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14455988696360579530378897 10841991522270434647784173)
              ·
                refine ⟨4065746820851412992919065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10841991522270434647784173 4065746820851412992919065)
                ·
                  refine ⟨3049310115638559744689299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4065746820851412992919065 3049310115638559744689299)
                  ·
                    refine ⟨4573965173457839617033949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3049310115638559744689299 4573965173457839617033949)
                    ·
                      refine ⟨1715236940046689856387731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4573965173457839617033949 1715236940046689856387731)
                      ·
                        rfl

theorem cell23_3340412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3340412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340412 prefixEnd_3340412 := by exact prefixLift 3340412
  have htrace : WordTrace (prefixWord ++ tailWord_3340412) baseStart_3340412 baseEnd_3340412 := by
    simpa [prefixWord, tailWord_3340412, baseEnd_3340412] using wordTrace_append hprefix tailTrace_3340412
  have hstable : (prefixWord ++ tailWord_3340412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340412).length < 2 ^ (prefixWord ++ tailWord_3340412).sum := by decide
  have hdescent : baseEnd_3340412 < baseStart_3340412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340439 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_3340439 : Nat := 118140960795 + 3340439 * 2 ^ 59
def prefixEnd_3340439 : Nat := 4983230072969 + 3 ^ 40 * 3340439 * 2
def baseEnd_3340439 : Nat := 1715250804024361250750107

theorem tailTrace_3340439 : CollatzResearch.WordTrace tailWord_3340439 prefixEnd_3340439 1715250804024361250750107 := by
  unfold tailWord_3340439
  simp only [CollatzResearch.WordTrace]
  refine ⟨121835819545167479406360371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81223879696778319604240247 121835819545167479406360371)
  ·
    refine ⟨182753729317751219109540557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121835819545167479406360371 182753729317751219109540557)
    ·
      refine ⟨68532648494156707166077709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182753729317751219109540557 68532648494156707166077709)
      ·
        refine ⟨25699743185308765187279141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68532648494156707166077709 25699743185308765187279141)
        ·
          refine ⟨4818701847245393472614839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25699743185308765187279141 4818701847245393472614839)
          ·
            refine ⟨7228052770868090208922259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818701847245393472614839 7228052770868090208922259)
            ·
              refine ⟨10842079156302135313383389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7228052770868090208922259 10842079156302135313383389)
              ·
                refine ⟨4065779683613300742518771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10842079156302135313383389 4065779683613300742518771)
                ·
                  refine ⟨6098669525419951113778157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065779683613300742518771 6098669525419951113778157)
                  ·
                    refine ⟨2287001072032481667666809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6098669525419951113778157 2287001072032481667666809)
                    ·
                      refine ⟨1715250804024361250750107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2287001072032481667666809 1715250804024361250750107)
                      ·
                        rfl

theorem cell23_3340439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_3340439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340439 prefixEnd_3340439 := by exact prefixLift 3340439
  have htrace : WordTrace (prefixWord ++ tailWord_3340439) baseStart_3340439 baseEnd_3340439 := by
    simpa [prefixWord, tailWord_3340439, baseEnd_3340439] using wordTrace_append hprefix tailTrace_3340439
  have hstable : (prefixWord ++ tailWord_3340439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340439).length < 2 ^ (prefixWord ++ tailWord_3340439).sum := by decide
  have hdescent : baseEnd_3340439 < baseStart_3340439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340528 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5]
def baseStart_3340528 : Nat := 118140960795 + 3340528 * 2 ^ 59
def prefixEnd_3340528 : Nat := 4983230072969 + 3 ^ 40 * 3340528 * 2
def baseEnd_3340528 : Nat := 1715296503802611402537197

theorem tailTrace_3340528 : CollatzResearch.WordTrace tailWord_3340528 prefixEnd_3340528 1715296503802611402537197 := by
  unfold tailWord_3340528
  simp only [CollatzResearch.WordTrace]
  refine ⟨60919532820922523803175119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81226043761230031737566825 60919532820922523803175119)
  ·
    refine ⟨91379299231383785704762679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60919532820922523803175119 91379299231383785704762679)
    ·
      refine ⟨137068948847075678557144019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91379299231383785704762679 137068948847075678557144019)
      ·
        refine ⟨205603423270613517835716029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137068948847075678557144019 205603423270613517835716029)
        ·
          refine ⟨77101283726480069188393511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205603423270613517835716029 77101283726480069188393511)
          ·
            refine ⟨115651925589720103782590267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77101283726480069188393511 115651925589720103782590267)
            ·
              refine ⟨173477888384580155673885401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115651925589720103782590267 173477888384580155673885401)
              ·
                refine ⟨130108416288435116755414051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173477888384580155673885401 130108416288435116755414051)
                ·
                  refine ⟨195162624432652675133121077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130108416288435116755414051 195162624432652675133121077)
                  ·
                    refine ⟨18296496040561188293730101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195162624432652675133121077 18296496040561188293730101)
                    ·
                      refine ⟨1715296503802611402537197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18296496040561188293730101 1715296503802611402537197)
                      ·
                        rfl

theorem cell23_3340528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_3340528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340528 prefixEnd_3340528 := by exact prefixLift 3340528
  have htrace : WordTrace (prefixWord ++ tailWord_3340528) baseStart_3340528 baseEnd_3340528 := by
    simpa [prefixWord, tailWord_3340528, baseEnd_3340528] using wordTrace_append hprefix tailTrace_3340528
  have hstable : (prefixWord ++ tailWord_3340528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340528).length < 2 ^ (prefixWord ++ tailWord_3340528).sum := by decide
  have hdescent : baseEnd_3340528 < baseStart_3340528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340565 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 6]
def baseStart_3340565 : Nat := 118140960795 + 3340565 * 2 ^ 59
def prefixEnd_3340565 : Nat := 4983230072969 + 3 ^ 40 * 3340565 * 2
def baseEnd_3340565 : Nat := 190590611398536417530503

theorem tailTrace_3340565 : CollatzResearch.WordTrace tailWord_3340565 prefixEnd_3340565 190590611398536417530503 := by
  unfold tailWord_3340565
  simp only [CollatzResearch.WordTrace]
  refine ⟨121840415142711002925447149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81226943428474001950298099 121840415142711002925447149)
  ·
    refine ⟨45690155678516626097042681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121840415142711002925447149 45690155678516626097042681)
    ·
      refine ⟨34267616758887469572782011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45690155678516626097042681 34267616758887469572782011)
      ·
        refine ⟨51401425138331204359173017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34267616758887469572782011 51401425138331204359173017)
        ·
          refine ⟨38551068853748403269379763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51401425138331204359173017 38551068853748403269379763)
          ·
            refine ⟨57826603280622604904069645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38551068853748403269379763 57826603280622604904069645)
            ·
              refine ⟨21684976230233476839026117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57826603280622604904069645 21684976230233476839026117)
              ·
                refine ⟨4065933043168776907317397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21684976230233476839026117 4065933043168776907317397)
                ·
                  refine ⟨190590611398536417530503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4065933043168776907317397 190590611398536417530503)
                  ·
                    rfl

theorem cell23_3340565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_3340565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340565 prefixEnd_3340565 := by exact prefixLift 3340565
  have htrace : WordTrace (prefixWord ++ tailWord_3340565) baseStart_3340565 baseEnd_3340565 := by
    simpa [prefixWord, tailWord_3340565, baseEnd_3340565] using wordTrace_append hprefix tailTrace_3340565
  have hstable : (prefixWord ++ tailWord_3340565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340565).length < 2 ^ (prefixWord ++ tailWord_3340565).sum := by decide
  have hdescent : baseEnd_3340565 < baseStart_3340565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340595 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 3, 5]
def baseStart_3340595 : Nat := 118140960795 + 3340595 * 2 ^ 59
def prefixEnd_3340595 : Nat := 4983230072969 + 3 ^ 40 * 3340595 * 2
def baseEnd_3340595 : Nat := 571776969002154213466463

theorem tailTrace_3340595 : CollatzResearch.WordTrace tailWord_3340595 prefixEnd_3340595 571776969002154213466463 := by
  unfold tailWord_3340595
  simp only [CollatzResearch.WordTrace]
  refine ⟨121841509332602318049039239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81227672888401545366026159 121841509332602318049039239)
  ·
    refine ⟨182762263998903477073558859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121841509332602318049039239 182762263998903477073558859)
    ·
      refine ⟨274143395998355215610338289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182762263998903477073558859 274143395998355215610338289)
      ·
        refine ⟨205607546998766411707753717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274143395998355215610338289 205607546998766411707753717)
        ·
          refine ⟨19275707531134351097601911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205607546998766411707753717 19275707531134351097601911)
          ·
            refine ⟨28913561296701526646402867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19275707531134351097601911 28913561296701526646402867)
            ·
              refine ⟨43370341945052289969604301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28913561296701526646402867 43370341945052289969604301)
              ·
                refine ⟨16263878229394608738601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43370341945052289969604301 16263878229394608738601613)
                ·
                  refine ⟨6098954336022978276975605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16263878229394608738601613 6098954336022978276975605)
                  ·
                    refine ⟨571776969002154213466463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6098954336022978276975605 571776969002154213466463)
                    ·
                      rfl

theorem cell23_3340595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 5].length) (baseStart_3340595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340595 prefixEnd_3340595 := by exact prefixLift 3340595
  have htrace : WordTrace (prefixWord ++ tailWord_3340595) baseStart_3340595 baseEnd_3340595 := by
    simpa [prefixWord, tailWord_3340595, baseEnd_3340595] using wordTrace_append hprefix tailTrace_3340595
  have hstable : (prefixWord ++ tailWord_3340595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340595).length < 2 ^ (prefixWord ++ tailWord_3340595).sum := by decide
  have hdescent : baseEnd_3340595 < baseStart_3340595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3340596 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3340596 : Nat := 118140960795 + 3340596 * 2 ^ 59
def prefixEnd_3340596 : Nat := 4983230072969 + 3 ^ 40 * 3340596 * 2
def baseEnd_3340596 : Nat := 1715331420487117136486885

theorem tailTrace_3340596 : CollatzResearch.WordTrace tailWord_3340596 prefixEnd_3340596 1715331420487117136486885 := by
  unfold tailWord_3340596
  simp only [CollatzResearch.WordTrace]
  refine ⟨60920772902799347609912821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81227697203732463479883761 60920772902799347609912821)
  ·
    refine ⟨5711322459637438838429327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60920772902799347609912821 5711322459637438838429327)
    ·
      refine ⟨8566983689456158257643991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711322459637438838429327 8566983689456158257643991)
      ·
        refine ⟨12850475534184237386465987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566983689456158257643991 12850475534184237386465987)
        ·
          refine ⟨19275713301276356079698981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12850475534184237386465987 19275713301276356079698981)
          ·
            refine ⟨3614196243989316764943559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19275713301276356079698981 3614196243989316764943559)
            ·
              refine ⟨5421294365983975147415339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614196243989316764943559 5421294365983975147415339)
              ·
                refine ⟨8131941548975962721123009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421294365983975147415339 8131941548975962721123009)
                ·
                  refine ⟨6098956161731972040842257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8131941548975962721123009 6098956161731972040842257)
                  ·
                    refine ⟨4574217121298979030631693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6098956161731972040842257 4574217121298979030631693)
                    ·
                      refine ⟨1715331420487117136486885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4574217121298979030631693 1715331420487117136486885)
                      ·
                        rfl

theorem cell23_3340596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3340596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3340596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3340596 prefixEnd_3340596 := by exact prefixLift 3340596
  have htrace : WordTrace (prefixWord ++ tailWord_3340596) baseStart_3340596 baseEnd_3340596 := by
    simpa [prefixWord, tailWord_3340596, baseEnd_3340596] using wordTrace_append hprefix tailTrace_3340596
  have hstable : (prefixWord ++ tailWord_3340596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3340596).length < 2 ^ (prefixWord ++ tailWord_3340596).sum := by decide
  have hdescent : baseEnd_3340596 < baseStart_3340596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3340596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
