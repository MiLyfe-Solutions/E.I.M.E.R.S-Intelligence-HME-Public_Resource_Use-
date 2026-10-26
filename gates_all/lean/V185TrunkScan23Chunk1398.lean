import V185TrunkScan23Chunk1397

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8280828 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_8280828 : Nat := 118140960795 + 8280828 * 2 ^ 59
def prefixEnd_8280828 : Nat := 4983230072969 + 3 ^ 40 * 8280828 * 2
def baseEnd_8280828 : Nat := 4252044981209632456067171

theorem tailTrace_8280828 : CollatzResearch.WordTrace tailWord_8280828 prefixEnd_8280828 4252044981209632456067171 := by
  unfold tailWord_8280828
  simp only [CollatzResearch.WordTrace]
  refine ⟨151013304821990941836545569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201351073095987922448727425 151013304821990941836545569)
  ·
    refine ⟨113259978616493206377409177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151013304821990941836545569 113259978616493206377409177)
    ·
      refine ⟨84944983962369904783056883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113259978616493206377409177 84944983962369904783056883)
      ·
        refine ⟨127417475943554857174585325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84944983962369904783056883 127417475943554857174585325)
        ·
          refine ⟨47781553478833071440469497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127417475943554857174585325 47781553478833071440469497)
          ·
            refine ⟨35836165109124803580352123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47781553478833071440469497 35836165109124803580352123)
            ·
              refine ⟨53754247663687205370528185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35836165109124803580352123 53754247663687205370528185)
              ·
                refine ⟨40315685747765404027896139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53754247663687205370528185 40315685747765404027896139)
                ·
                  refine ⟨60473528621648106041844209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40315685747765404027896139 60473528621648106041844209)
                  ·
                    refine ⟨45355146466236079531383157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60473528621648106041844209 45355146466236079531383157)
                    ·
                      refine ⟨4252044981209632456067171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45355146466236079531383157 4252044981209632456067171)
                      ·
                        rfl

theorem cell23_8280828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_8280828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280828 prefixEnd_8280828 := by exact prefixLift 8280828
  have htrace : WordTrace (prefixWord ++ tailWord_8280828) baseStart_8280828 baseEnd_8280828 := by
    simpa [prefixWord, tailWord_8280828, baseEnd_8280828] using wordTrace_append hprefix tailTrace_8280828
  have hstable : (prefixWord ++ tailWord_8280828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280828).length < 2 ^ (prefixWord ++ tailWord_8280828).sum := by decide
  have hdescent : baseEnd_8280828 < baseStart_8280828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280839 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 5]
def baseStart_8280839 : Nat := 118140960795 + 8280839 * 2 ^ 59
def prefixEnd_8280839 : Nat := 4983230072969 + 3 ^ 40 * 8280839 * 2
def baseEnd_8280839 : Nat := 472450069944092434781069

theorem tailTrace_8280839 : CollatzResearch.WordTrace tailWord_8280839 prefixEnd_8280839 472450069944092434781069 := by
  unfold tailWord_8280839
  simp only [CollatzResearch.WordTrace]
  refine ⟨302027010846942032551741571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201351340564628021701161047 302027010846942032551741571)
  ·
    refine ⟨453040516270413048827612357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302027010846942032551741571 453040516270413048827612357)
    ·
      refine ⟨84945096800702446655177317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453040516270413048827612357 84945096800702446655177317)
      ·
        refine ⟨15927205650131708747845747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84945096800702446655177317 15927205650131708747845747)
        ·
          refine ⟨23890808475197563121768621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15927205650131708747845747 23890808475197563121768621)
          ·
            refine ⟨8959053178199086170663233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23890808475197563121768621 8959053178199086170663233)
            ·
              refine ⟨6719289883649314627997425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8959053178199086170663233 6719289883649314627997425)
              ·
                refine ⟨5039467412736985970998069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6719289883649314627997425 5039467412736985970998069)
                ·
                  refine ⟨472450069944092434781069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5039467412736985970998069 472450069944092434781069)
                  ·
                    rfl

theorem cell23_8280839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 5].length) (baseStart_8280839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280839 prefixEnd_8280839 := by exact prefixLift 8280839
  have htrace : WordTrace (prefixWord ++ tailWord_8280839) baseStart_8280839 baseEnd_8280839 := by
    simpa [prefixWord, tailWord_8280839, baseEnd_8280839] using wordTrace_append hprefix tailTrace_8280839
  have hstable : (prefixWord ++ tailWord_8280839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280839).length < 2 ^ (prefixWord ++ tailWord_8280839).sum := by decide
  have hdescent : baseEnd_8280839 < baseStart_8280839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280865 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 3, 4]
def baseStart_8280865 : Nat := 118140960795 + 8280865 * 2 ^ 59
def prefixEnd_8280865 : Nat := 4983230072969 + 3 ^ 40 * 8280865 * 2
def baseEnd_8280865 : Nat := 1417354659997949603768167

theorem tailTrace_8280865 : CollatzResearch.WordTrace tailWord_8280865 prefixEnd_8280865 1417354659997949603768167 := by
  unfold tailWord_8280865
  simp only [CollatzResearch.WordTrace]
  refine ⟨302027959144847838992188049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201351972763231892661458699 302027959144847838992188049)
  ·
    refine ⟨226520969358635879244141037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302027959144847838992188049 226520969358635879244141037)
    ·
      refine ⟨84945363509488454716552889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226520969358635879244141037 84945363509488454716552889)
      ·
        refine ⟨63709022632116341037414667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84945363509488454716552889 63709022632116341037414667)
        ·
          refine ⟨95563533948174511556122001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63709022632116341037414667 95563533948174511556122001)
          ·
            refine ⟨71672650461130883667091501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95563533948174511556122001 71672650461130883667091501)
            ·
              refine ⟨26877243922924081375159313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71672650461130883667091501 26877243922924081375159313)
              ·
                refine ⟨20157932942193061031369485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26877243922924081375159313 20157932942193061031369485)
                ·
                  refine ⟨7559224853322397886763557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20157932942193061031369485 7559224853322397886763557)
                  ·
                    refine ⟨1417354659997949603768167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559224853322397886763557 1417354659997949603768167)
                    ·
                      rfl

theorem cell23_8280865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_8280865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280865 prefixEnd_8280865 := by exact prefixLift 8280865
  have htrace : WordTrace (prefixWord ++ tailWord_8280865) baseStart_8280865 baseEnd_8280865 := by
    simpa [prefixWord, tailWord_8280865, baseEnd_8280865] using wordTrace_append hprefix tailTrace_8280865
  have hstable : (prefixWord ++ tailWord_8280865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280865).length < 2 ^ (prefixWord ++ tailWord_8280865).sum := by decide
  have hdescent : baseEnd_8280865 < baseStart_8280865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280895 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 6]
def baseStart_8280895 : Nat := 118140960795 + 8280895 * 2 ^ 59
def prefixEnd_8280895 : Nat := 4983230072969 + 3 ^ 40 * 8280895 * 2
def baseEnd_8280895 : Nat := 472453264934831521547707

theorem tailTrace_8280895 : CollatzResearch.WordTrace tailWord_8280895 prefixEnd_8280895 472453264934831521547707 := by
  unfold tailWord_8280895
  simp only [CollatzResearch.WordTrace]
  refine ⟨302029053334739154115780139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201352702223159436077186759 302029053334739154115780139)
  ·
    refine ⟨453043580002108731173670209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302029053334739154115780139 453043580002108731173670209)
    ·
      refine ⟨339782685001581548380252657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453043580002108731173670209 339782685001581548380252657)
      ·
        refine ⟨254837013751186161285189493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339782685001581548380252657 254837013751186161285189493)
        ·
          refine ⟨23890970039173702620486515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254837013751186161285189493 23890970039173702620486515)
          ·
            refine ⟨35836455058760553930729773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23890970039173702620486515 35836455058760553930729773)
            ·
              refine ⟨13438670647035207724023665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35836455058760553930729773 13438670647035207724023665)
              ·
                refine ⟨10079002985276405793017749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13438670647035207724023665 10079002985276405793017749)
                ·
                  refine ⟨472453264934831521547707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10079002985276405793017749 472453264934831521547707)
                  ·
                    rfl

theorem cell23_8280895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 6].length) (baseStart_8280895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280895 prefixEnd_8280895 := by exact prefixLift 8280895
  have htrace : WordTrace (prefixWord ++ tailWord_8280895) baseStart_8280895 baseEnd_8280895 := by
    simpa [prefixWord, tailWord_8280895, baseEnd_8280895] using wordTrace_append hprefix tailTrace_8280895
  have hstable : (prefixWord ++ tailWord_8280895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280895).length < 2 ^ (prefixWord ++ tailWord_8280895).sum := by decide
  have hdescent : baseEnd_8280895 < baseStart_8280895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280922 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_8280922 : Nat := 118140960795 + 8280922 * 2 ^ 59
def prefixEnd_8280922 : Nat := 4983230072969 + 3 ^ 40 * 8280922 * 2
def baseEnd_8280922 : Nat := 4252093248391155088291739

theorem tailTrace_8280922 : CollatzResearch.WordTrace tailWord_8280922 prefixEnd_8280922 4252093248391155088291739 := by
  unfold tailWord_8280922
  simp only [CollatzResearch.WordTrace]
  refine ⟨75507509526410334431753255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201353358737094225151342013 75507509526410334431753255)
  ·
    refine ⟨113261264289615501647629883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75507509526410334431753255 113261264289615501647629883)
    ·
      refine ⟨169891896434423252471444825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113261264289615501647629883 169891896434423252471444825)
      ·
        refine ⟨127418922325817439353583619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169891896434423252471444825 127418922325817439353583619)
        ·
          refine ⟨191128383488726159030375429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127418922325817439353583619 191128383488726159030375429)
          ·
            refine ⟨35836571904136154818195393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191128383488726159030375429 35836571904136154818195393)
            ·
              refine ⟨26877428928102116113646545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35836571904136154818195393 26877428928102116113646545)
              ·
                refine ⟨20158071696076587085234909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26877428928102116113646545 20158071696076587085234909)
                ·
                  refine ⟨7559276886028720156963091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20158071696076587085234909 7559276886028720156963091)
                  ·
                    refine ⟨11338915329043080235444637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7559276886028720156963091 11338915329043080235444637)
                    ·
                      refine ⟨4252093248391155088291739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11338915329043080235444637 4252093248391155088291739)
                      ·
                        rfl

theorem cell23_8280922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_8280922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280922 prefixEnd_8280922 := by exact prefixLift 8280922
  have htrace : WordTrace (prefixWord ++ tailWord_8280922) baseStart_8280922 baseEnd_8280922 := by
    simpa [prefixWord, tailWord_8280922, baseEnd_8280922] using wordTrace_append hprefix tailTrace_8280922
  have hstable : (prefixWord ++ tailWord_8280922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280922).length < 2 ^ (prefixWord ++ tailWord_8280922).sum := by decide
  have hdescent : baseEnd_8280922 < baseStart_8280922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280932 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_8280932 : Nat := 118140960795 + 8280932 * 2 ^ 59
def prefixEnd_8280932 : Nat := 4983230072969 + 3 ^ 40 * 8280932 * 2
def baseEnd_8280932 : Nat := 4252098383197700049166693

theorem tailTrace_8280932 : CollatzResearch.WordTrace tailWord_8280932 prefixEnd_8280932 4252098383197700049166693 := by
  unfold tailWord_8280932
  simp only [CollatzResearch.WordTrace]
  refine ⟨151015201417802554717438525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201353601890403406289918033 151015201417802554717438525)
  ·
    refine ⟨56630700531675958019039447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151015201417802554717438525 56630700531675958019039447)
    ·
      refine ⟨84946050797513937028559171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56630700531675958019039447 84946050797513937028559171)
      ·
        refine ⟨127419076196270905542838757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84946050797513937028559171 127419076196270905542838757)
        ·
          refine ⟨23891076786800794789282267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127419076196270905542838757 23891076786800794789282267)
          ·
            refine ⟨35836615180201192183923401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23891076786800794789282267 35836615180201192183923401)
            ·
              refine ⟨26877461385150894137942551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35836615180201192183923401 26877461385150894137942551)
              ·
                refine ⟨40316192077726341206913827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26877461385150894137942551 40316192077726341206913827)
                ·
                  refine ⟨60474288116589511810370741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40316192077726341206913827 60474288116589511810370741)
                  ·
                    refine ⟨5669464510930266732222257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60474288116589511810370741 5669464510930266732222257)
                    ·
                      refine ⟨4252098383197700049166693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669464510930266732222257 4252098383197700049166693)
                      ·
                        rfl

theorem cell23_8280932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_8280932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280932 prefixEnd_8280932 := by exact prefixLift 8280932
  have htrace : WordTrace (prefixWord ++ tailWord_8280932) baseStart_8280932 baseEnd_8280932 := by
    simpa [prefixWord, tailWord_8280932, baseEnd_8280932] using wordTrace_append hprefix tailTrace_8280932
  have hstable : (prefixWord ++ tailWord_8280932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280932).length < 2 ^ (prefixWord ++ tailWord_8280932).sum := by decide
  have hdescent : baseEnd_8280932 < baseStart_8280932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280939 : List Nat := [1, 1, 1, 1, 2, 2, 7, 3, 1, 1, 3]
def baseStart_8280939 : Nat := 118140960795 + 8280939 * 2 ^ 59
def prefixEnd_8280939 : Nat := 4983230072969 + 3 ^ 40 * 8280939 * 2
def baseEnd_8280939 : Nat := 4252101977562281521779161

theorem tailTrace_8280939 : CollatzResearch.WordTrace tailWord_8280939 prefixEnd_8280939 4252101977562281521779161 := by
  unfold tailWord_8280939
  simp only [CollatzResearch.WordTrace]
  refine ⟨302030658146579749630381871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201353772097719833086921247 302030658146579749630381871)
  ·
    refine ⟨453045987219869624445572807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302030658146579749630381871 453045987219869624445572807)
    ·
      refine ⟨679568980829804436668359211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453045987219869624445572807 679568980829804436668359211)
      ·
        refine ⟨1019353471244706655002538817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679568980829804436668359211 1019353471244706655002538817)
        ·
          refine ⟨764515103433529991251904113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019353471244706655002538817 764515103433529991251904113)
          ·
            refine ⟨573386327575147493438928085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764515103433529991251904113 573386327575147493438928085)
            ·
              refine ⟨13438742052542519377474877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 573386327575147493438928085 13438742052542519377474877)
              ·
                refine ⟨5039528269703444766553079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13438742052542519377474877 5039528269703444766553079)
                ·
                  refine ⟨7559292404555167149829619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039528269703444766553079 7559292404555167149829619)
                  ·
                    refine ⟨11338938606832750724744429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7559292404555167149829619 11338938606832750724744429)
                    ·
                      refine ⟨4252101977562281521779161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11338938606832750724744429 4252101977562281521779161)
                      ·
                        rfl

theorem cell23_8280939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 1, 1, 3].length) (baseStart_8280939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280939 prefixEnd_8280939 := by exact prefixLift 8280939
  have htrace : WordTrace (prefixWord ++ tailWord_8280939) baseStart_8280939 baseEnd_8280939 := by
    simpa [prefixWord, tailWord_8280939, baseEnd_8280939] using wordTrace_append hprefix tailTrace_8280939
  have hstable : (prefixWord ++ tailWord_8280939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280939).length < 2 ^ (prefixWord ++ tailWord_8280939).sum := by decide
  have hdescent : baseEnd_8280939 < baseStart_8280939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280949 : List Nat := [1, 3, 4, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_8280949 : Nat := 118140960795 + 8280949 * 2 ^ 59
def prefixEnd_8280949 : Nat := 4983230072969 + 3 ^ 40 * 8280949 * 2
def baseEnd_8280949 : Nat := 4252107112368826482654115

theorem tailTrace_8280949 : CollatzResearch.WordTrace tailWord_8280949 prefixEnd_8280949 4252107112368826482654115 := by
  unfold tailWord_8280949
  simp only [CollatzResearch.WordTrace]
  refine ⟨302031022876543521338245901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201354015251029014225497267 302031022876543521338245901)
  ·
    refine ⟨113261633578703820501842213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302031022876543521338245901 113261633578703820501842213)
    ·
      refine ⟨21236556296006966344095415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113261633578703820501842213 21236556296006966344095415)
      ·
        refine ⟨31854834444010449516143123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21236556296006966344095415 31854834444010449516143123)
        ·
          refine ⟨47782251666015674274214685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31854834444010449516143123 47782251666015674274214685)
          ·
            refine ⟨17918344374755877852830507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47782251666015674274214685 17918344374755877852830507)
            ·
              refine ⟨26877516562133816779245761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17918344374755877852830507 26877516562133816779245761)
              ·
                refine ⟨20158137421600362584434321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26877516562133816779245761 20158137421600362584434321)
                ·
                  refine ⟨15118603066200271938325741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20158137421600362584434321 15118603066200271938325741)
                  ·
                    refine ⟨5669476149825101976872153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15118603066200271938325741 5669476149825101976872153)
                    ·
                      refine ⟨4252107112368826482654115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669476149825101976872153 4252107112368826482654115)
                      ·
                        rfl

theorem cell23_8280949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_8280949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280949 prefixEnd_8280949 := by exact prefixLift 8280949
  have htrace : WordTrace (prefixWord ++ tailWord_8280949) baseStart_8280949 baseEnd_8280949 := by
    simpa [prefixWord, tailWord_8280949, baseEnd_8280949] using wordTrace_append hprefix tailTrace_8280949
  have hstable : (prefixWord ++ tailWord_8280949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280949).length < 2 ^ (prefixWord ++ tailWord_8280949).sum := by decide
  have hdescent : baseEnd_8280949 < baseStart_8280949 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280955 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 4, 4]
def baseStart_8280955 : Nat := 118140960795 + 8280955 * 2 ^ 59
def prefixEnd_8280955 : Nat := 4983230072969 + 3 ^ 40 * 8280955 * 2
def baseEnd_8280955 : Nat := 1417370064417584486393029

theorem tailTrace_8280955 : CollatzResearch.WordTrace tailWord_8280955 prefixEnd_8280955 1417370064417584486393029 := by
  unfold tailWord_8280955
  simp only [CollatzResearch.WordTrace]
  refine ⟨302031241714521784362964319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201354161143014522908642879 302031241714521784362964319)
  ·
    refine ⟨453046862571782676544446479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302031241714521784362964319 453046862571782676544446479)
    ·
      refine ⟨679570293857674014816669719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453046862571782676544446479 679570293857674014816669719)
      ·
        refine ⟨1019355440786511022225004579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679570293857674014816669719 1019355440786511022225004579)
        ·
          refine ⟨1529033161179766533337506869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019355440786511022225004579 1529033161179766533337506869)
          ·
            refine ⟨143346858860603112500391269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1529033161179766533337506869 143346858860603112500391269)
            ·
              refine ⟨26877536036363083593823363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143346858860603112500391269 26877536036363083593823363)
              ·
                refine ⟨40316304054544625390735045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26877536036363083593823363 40316304054544625390735045)
                ·
                  refine ⟨7559307010227117260762821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40316304054544625390735045 7559307010227117260762821)
                  ·
                    refine ⟨1417370064417584486393029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559307010227117260762821 1417370064417584486393029)
                    ·
                      rfl

theorem cell23_8280955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 4].length) (baseStart_8280955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280955 prefixEnd_8280955 := by exact prefixLift 8280955
  have htrace : WordTrace (prefixWord ++ tailWord_8280955) baseStart_8280955 baseEnd_8280955 := by
    simpa [prefixWord, tailWord_8280955, baseEnd_8280955] using wordTrace_append hprefix tailTrace_8280955
  have hstable : (prefixWord ++ tailWord_8280955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280955).length < 2 ^ (prefixWord ++ tailWord_8280955).sum := by decide
  have hdescent : baseEnd_8280955 < baseStart_8280955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280965 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_8280965 : Nat := 118140960795 + 8280965 * 2 ^ 59
def prefixEnd_8280965 : Nat := 4983230072969 + 3 ^ 40 * 8280965 * 2
def baseEnd_8280965 : Nat := 4252115328059298420054041

theorem tailTrace_8280965 : CollatzResearch.WordTrace tailWord_8280965 prefixEnd_8280965 4252115328059298420054041 := by
  unfold tailWord_8280965
  simp only [CollatzResearch.WordTrace]
  refine ⟨302031606444485556070828349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201354404296323704047218899 302031606444485556070828349)
  ·
    refine ⟨113261852416682083526560631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302031606444485556070828349 113261852416682083526560631)
    ·
      refine ⟨169892778625023125289840947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113261852416682083526560631 169892778625023125289840947)
      ·
        refine ⟨254839167937534687934761421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169892778625023125289840947 254839167937534687934761421)
        ·
          refine ⟨95564687976575507975535533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254839167937534687934761421 95564687976575507975535533)
          ·
            refine ⟨35836757991215815490825825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95564687976575507975535533 35836757991215815490825825)
            ·
              refine ⟨26877568493411861618119369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35836757991215815490825825 26877568493411861618119369)
              ·
                refine ⟨20158176370058896213589527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26877568493411861618119369 20158176370058896213589527)
                ·
                  refine ⟨30237264555088344320384291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20158176370058896213589527 30237264555088344320384291)
                  ·
                    refine ⟨45355896832632516480576437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30237264555088344320384291 45355896832632516480576437)
                    ·
                      refine ⟨4252115328059298420054041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45355896832632516480576437 4252115328059298420054041)
                      ·
                        rfl

theorem cell23_8280965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_8280965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280965 prefixEnd_8280965 := by exact prefixLift 8280965
  have htrace : WordTrace (prefixWord ++ tailWord_8280965) baseStart_8280965 baseEnd_8280965 := by
    simpa [prefixWord, tailWord_8280965, baseEnd_8280965] using wordTrace_append hprefix tailTrace_8280965
  have hstable : (prefixWord ++ tailWord_8280965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280965).length < 2 ^ (prefixWord ++ tailWord_8280965).sum := by decide
  have hdescent : baseEnd_8280965 < baseStart_8280965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280995 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3]
def baseStart_8280995 : Nat := 118140960795 + 8280995 * 2 ^ 59
def prefixEnd_8280995 : Nat := 4983230072969 + 3 ^ 40 * 8280995 * 2
def baseEnd_8280995 : Nat := 4252130732478933302678903

theorem tailTrace_8280995 : CollatzResearch.WordTrace tailWord_8280995 prefixEnd_8280995 4252130732478933302678903 := by
  unfold tailWord_8280995
  simp only [CollatzResearch.WordTrace]
  refine ⟨302032700634376871194420439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201355133756251247462946959 302032700634376871194420439)
  ·
    refine ⟨453049050951565306791630659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302032700634376871194420439 453049050951565306791630659)
    ·
      refine ⟨679573576427347960187445989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453049050951565306791630659 679573576427347960187445989)
      ·
        refine ⟨127420045580127742535146123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 679573576427347960187445989 127420045580127742535146123)
        ·
          refine ⟨191130068370191613802719185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127420045580127742535146123 191130068370191613802719185)
          ·
            refine ⟨143347551277643710352039389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191130068370191613802719185 143347551277643710352039389)
            ·
              refine ⟨53755331729116391382014771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143347551277643710352039389 53755331729116391382014771)
              ·
                refine ⟨80632997593674587073022157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53755331729116391382014771 80632997593674587073022157)
                ·
                  refine ⟨30237374097627970152383309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80632997593674587073022157 30237374097627970152383309)
                  ·
                    refine ⟨11339015286610488807143741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30237374097627970152383309 11339015286610488807143741)
                    ·
                      refine ⟨4252130732478933302678903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11339015286610488807143741 4252130732478933302678903)
                      ·
                        rfl

theorem cell23_8280995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_8280995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280995 prefixEnd_8280995 := by exact prefixLift 8280995
  have htrace : WordTrace (prefixWord ++ tailWord_8280995) baseStart_8280995 baseEnd_8280995 := by
    simpa [prefixWord, tailWord_8280995, baseEnd_8280995] using wordTrace_append hprefix tailTrace_8280995
  have hstable : (prefixWord ++ tailWord_8280995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280995).length < 2 ^ (prefixWord ++ tailWord_8280995).sum := by decide
  have hdescent : baseEnd_8280995 < baseStart_8280995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280996 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_8280996 : Nat := 118140960795 + 8280996 * 2 ^ 59
def prefixEnd_8280996 : Nat := 4983230072969 + 3 ^ 40 * 8280996 * 2
def baseEnd_8280996 : Nat := 4252131245959587798766399

theorem tailTrace_8280996 : CollatzResearch.WordTrace tailWord_8280996 prefixEnd_8280996 4252131245959587798766399 := by
  unfold tailWord_8280996
  simp only [CollatzResearch.WordTrace]
  refine ⟨151016368553686624182603421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201355158071582165576804561 151016368553686624182603421)
  ·
    refine ⟨56631138207632484068476283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151016368553686624182603421 56631138207632484068476283)
    ·
      refine ⟨84946707311448726102714425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56631138207632484068476283 84946707311448726102714425)
      ·
        refine ⟨63710030483586544577035819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84946707311448726102714425 63710030483586544577035819)
        ·
          refine ⟨95565045725379816865553729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63710030483586544577035819 95565045725379816865553729)
          ·
            refine ⟨71673784294034862649165297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95565045725379816865553729 71673784294034862649165297)
            ·
              refine ⟨53755338220526146986873973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71673784294034862649165297 53755338220526146986873973)
              ·
                refine ⟨5039562958174326280019435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53755338220526146986873973 5039562958174326280019435)
                ·
                  refine ⟨7559344437261489420029153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039562958174326280019435 7559344437261489420029153)
                  ·
                    refine ⟨5669508327946117065021865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559344437261489420029153 5669508327946117065021865)
                    ·
                      refine ⟨4252131245959587798766399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669508327946117065021865 4252131245959587798766399)
                      ·
                        rfl

theorem cell23_8280996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_8280996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280996 prefixEnd_8280996 := by exact prefixLift 8280996
  have htrace : WordTrace (prefixWord ++ tailWord_8280996) baseStart_8280996 baseEnd_8280996 := by
    simpa [prefixWord, tailWord_8280996, baseEnd_8280996] using wordTrace_append hprefix tailTrace_8280996
  have hstable : (prefixWord ++ tailWord_8280996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280996).length < 2 ^ (prefixWord ++ tailWord_8280996).sum := by decide
  have hdescent : baseEnd_8280996 < baseStart_8280996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8280999 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_8280999 : Nat := 118140960795 + 8280999 * 2 ^ 59
def prefixEnd_8280999 : Nat := 4983230072969 + 3 ^ 40 * 8280999 * 2
def baseEnd_8280999 : Nat := 4252132786401551287028885

theorem tailTrace_8280999 : CollatzResearch.WordTrace tailWord_8280999 prefixEnd_8280999 4252132786401551287028885 := by
  unfold tailWord_8280999
  simp only [CollatzResearch.WordTrace]
  refine ⟨302032846526362379877566051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201355231017574919918377367 302032846526362379877566051)
  ·
    refine ⟨453049269789543569816349077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302032846526362379877566051 453049269789543569816349077)
    ·
      refine ⟨21236684521384854835141363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 453049269789543569816349077 21236684521384854835141363)
      ·
        refine ⟨31855026782077282252712045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21236684521384854835141363 31855026782077282252712045)
        ·
          refine ⟨11945635043278980844767017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31855026782077282252712045 11945635043278980844767017)
          ·
            refine ⟨8959226282459235633575263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11945635043278980844767017 8959226282459235633575263)
            ·
              refine ⟨13438839423688853450362895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8959226282459235633575263 13438839423688853450362895)
              ·
                refine ⟨20158259135533280175544343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13438839423688853450362895 20158259135533280175544343)
                ·
                  refine ⟨30237388703299920263316515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20158259135533280175544343 30237388703299920263316515)
                  ·
                    refine ⟨45356083054949880394974773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30237388703299920263316515 45356083054949880394974773)
                    ·
                      refine ⟨4252132786401551287028885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45356083054949880394974773 4252132786401551287028885)
                      ·
                        rfl

theorem cell23_8280999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_8280999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8280999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8280999 prefixEnd_8280999 := by exact prefixLift 8280999
  have htrace : WordTrace (prefixWord ++ tailWord_8280999) baseStart_8280999 baseEnd_8280999 := by
    simpa [prefixWord, tailWord_8280999, baseEnd_8280999] using wordTrace_append hprefix tailTrace_8280999
  have hstable : (prefixWord ++ tailWord_8280999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8280999).length < 2 ^ (prefixWord ++ tailWord_8280999).sum := by decide
  have hdescent : baseEnd_8280999 < baseStart_8280999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8280999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281008 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_8281008 : Nat := 118140960795 + 8281008 * 2 ^ 59
def prefixEnd_8281008 : Nat := 4983230072969 + 3 ^ 40 * 8281008 * 2
def baseEnd_8281008 : Nat := 4252137407727441751816343

theorem tailTrace_8281008 : CollatzResearch.WordTrace tailWord_8281008 prefixEnd_8281008 4252137407727441751816343 := by
  unfold tailWord_8281008
  simp only [CollatzResearch.WordTrace]
  refine ⟨151016587391664887207321839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201355449855553182943095785 151016587391664887207321839)
  ·
    refine ⟨226524881087497330810982759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151016587391664887207321839 226524881087497330810982759)
    ·
      refine ⟨339787321631245996216474139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226524881087497330810982759 339787321631245996216474139)
      ·
        refine ⟨509680982446868994324711209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339787321631245996216474139 509680982446868994324711209)
        ·
          refine ⟨382260736835151745743533407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509680982446868994324711209 382260736835151745743533407)
          ·
            refine ⟨573391105252727618615300111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382260736835151745743533407 573391105252727618615300111)
            ·
              refine ⟨860086657879091427922950167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573391105252727618615300111 860086657879091427922950167)
              ·
                refine ⟨1290129986818637141884425251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860086657879091427922950167 1290129986818637141884425251)
                ·
                  refine ⟨1935194980227955712826637877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1290129986818637141884425251 1935194980227955712826637877)
                  ·
                    refine ⟨181424529396370848077497301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1935194980227955712826637877 181424529396370848077497301)
                    ·
                      refine ⟨4252137407727441751816343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181424529396370848077497301 4252137407727441751816343)
                      ·
                        rfl

theorem cell23_8281008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_8281008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281008 prefixEnd_8281008 := by exact prefixLift 8281008
  have htrace : WordTrace (prefixWord ++ tailWord_8281008) baseStart_8281008 baseEnd_8281008 := by
    simpa [prefixWord, tailWord_8281008, baseEnd_8281008] using wordTrace_append hprefix tailTrace_8281008
  have hstable : (prefixWord ++ tailWord_8281008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281008).length < 2 ^ (prefixWord ++ tailWord_8281008).sum := by decide
  have hdescent : baseEnd_8281008 < baseStart_8281008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281090 : List Nat := [3, 4, 1, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_8281090 : Nat := 118140960795 + 8281090 * 2 ^ 59
def prefixEnd_8281090 : Nat := 4983230072969 + 3 ^ 40 * 8281090 * 2
def baseEnd_8281090 : Nat := 4252179513141110430990967

theorem tailTrace_8281090 : CollatzResearch.WordTrace tailWord_8281090 prefixEnd_8281090 4252179513141110430990967 := by
  unfold tailWord_8281090
  simp only [CollatzResearch.WordTrace]
  refine ⟨75509041392258175604782181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201357443712688468279419149 75509041392258175604782181)
  ·
    refine ⟨14157945261048407925896659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75509041392258175604782181 14157945261048407925896659)
    ·
      refine ⟨21236917891572611888844989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14157945261048407925896659 21236917891572611888844989)
      ·
        refine ⟨7963844209339729458316871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21236917891572611888844989 7963844209339729458316871)
        ·
          refine ⟨11945766314009594187475307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963844209339729458316871 11945766314009594187475307)
          ·
            refine ⟨17918649471014391281212961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11945766314009594187475307 17918649471014391281212961)
            ·
              refine ⟨13438987103260793460909721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17918649471014391281212961 13438987103260793460909721)
              ·
                refine ⟨10079240327445595095682291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13438987103260793460909721 10079240327445595095682291)
                ·
                  refine ⟨15118860491168392643523437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10079240327445595095682291 15118860491168392643523437)
                  ·
                    refine ⟨5669572684188147241321289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15118860491168392643523437 5669572684188147241321289)
                    ·
                      refine ⟨4252179513141110430990967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669572684188147241321289 4252179513141110430990967)
                      ·
                        rfl

theorem cell23_8281090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_8281090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281090 prefixEnd_8281090 := by exact prefixLift 8281090
  have htrace : WordTrace (prefixWord ++ tailWord_8281090) baseStart_8281090 baseEnd_8281090 := by
    simpa [prefixWord, tailWord_8281090, baseEnd_8281090] using wordTrace_append hprefix tailTrace_8281090
  have hstable : (prefixWord ++ tailWord_8281090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281090).length < 2 ^ (prefixWord ++ tailWord_8281090).sum := by decide
  have hdescent : baseEnd_8281090 < baseStart_8281090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281105 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_8281105 : Nat := 118140960795 + 8281105 * 2 ^ 59
def prefixEnd_8281105 : Nat := 4983230072969 + 3 ^ 40 * 8281105 * 2
def baseEnd_8281105 : Nat := 1417395738450309290767799

theorem tailTrace_8281105 : CollatzResearch.WordTrace tailWord_8281105 prefixEnd_8281105 1417395738450309290767799 := by
  unfold tailWord_8281105
  simp only [CollatzResearch.WordTrace]
  refine ⟨302036712663978359980924769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201357808442652239987283179 302036712663978359980924769)
  ·
    refine ⟨226527534497983769985693577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302036712663978359980924769 226527534497983769985693577)
    ·
      refine ⟨169895650873487827489270183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226527534497983769985693577 169895650873487827489270183)
      ·
        refine ⟨254843476310231741233905275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169895650873487827489270183 254843476310231741233905275)
        ·
          refine ⟨382265214465347611850857913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254843476310231741233905275 382265214465347611850857913)
          ·
            refine ⟨286698910849010708888143435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382265214465347611850857913 286698910849010708888143435)
            ·
              refine ⟨430048366273516063332215153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286698910849010708888143435 430048366273516063332215153)
              ·
                refine ⟨322536274705137047499161365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430048366273516063332215153 322536274705137047499161365)
                ·
                  refine ⟨15118887876803299101523189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322536274705137047499161365 15118887876803299101523189)
                  ·
                    refine ⟨1417395738450309290767799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15118887876803299101523189 1417395738450309290767799)
                    ·
                      rfl

theorem cell23_8281105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_8281105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281105 prefixEnd_8281105 := by exact prefixLift 8281105
  have htrace : WordTrace (prefixWord ++ tailWord_8281105) baseStart_8281105 baseEnd_8281105 := by
    simpa [prefixWord, tailWord_8281105, baseEnd_8281105] using wordTrace_append hprefix tailTrace_8281105
  have hstable : (prefixWord ++ tailWord_8281105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281105).length < 2 ^ (prefixWord ++ tailWord_8281105).sum := by decide
  have hdescent : baseEnd_8281105 < baseStart_8281105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281109 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 5]
def baseStart_8281109 : Nat := 118140960795 + 8281109 * 2 ^ 59
def prefixEnd_8281109 : Nat := 4983230072969 + 3 ^ 40 * 8281109 * 2
def baseEnd_8281109 : Nat := 472465474363727317405931

theorem tailTrace_8281109 : CollatzResearch.WordTrace tailWord_8281109 prefixEnd_8281109 472465474363727317405931 := by
  unfold tailWord_8281109
  simp only [CollatzResearch.WordTrace]
  refine ⟨302036858555963868664070381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201357905703975912442713587 302036858555963868664070381)
  ·
    refine ⟨113263821958486450749026393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302036858555963868664070381 113263821958486450749026393)
    ·
      refine ⟨84947866468864838061769795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113263821958486450749026393 84947866468864838061769795)
      ·
        refine ⟨127421799703297257092654693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84947866468864838061769795 127421799703297257092654693)
        ·
          refine ⟨23891587444368235704872755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127421799703297257092654693 23891587444368235704872755)
          ·
            refine ⟨35837381166552353557309133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23891587444368235704872755 35837381166552353557309133)
            ·
              refine ⟨13439017937457132583990925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35837381166552353557309133 13439017937457132583990925)
              ·
                refine ⟨5039631726546424718996597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13439017937457132583990925 5039631726546424718996597)
                ·
                  refine ⟨472465474363727317405931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5039631726546424718996597 472465474363727317405931)
                  ·
                    rfl

theorem cell23_8281109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_8281109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281109 prefixEnd_8281109 := by exact prefixLift 8281109
  have htrace : WordTrace (prefixWord ++ tailWord_8281109) baseStart_8281109 baseEnd_8281109 := by
    simpa [prefixWord, tailWord_8281109, baseEnd_8281109] using wordTrace_append hprefix tailTrace_8281109
  have hstable : (prefixWord ++ tailWord_8281109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281109).length < 2 ^ (prefixWord ++ tailWord_8281109).sum := by decide
  have hdescent : baseEnd_8281109 < baseStart_8281109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281122 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_8281122 : Nat := 118140960795 + 8281122 * 2 ^ 59
def prefixEnd_8281122 : Nat := 4983230072969 + 3 ^ 40 * 8281122 * 2
def baseEnd_8281122 : Nat := 1417398648174018101930273

theorem tailTrace_8281122 : CollatzResearch.WordTrace tailWord_8281122 prefixEnd_8281122 1417398648174018101930273 := by
  unfold tailWord_8281122
  simp only [CollatzResearch.WordTrace]
  refine ⟨75509333176229192971073405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201358221803277847922862413 75509333176229192971073405)
  ·
    refine ⟨28315999941085947364152527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75509333176229192971073405 28315999941085947364152527)
    ·
      refine ⟨42473999911628921046228791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28315999941085947364152527 42473999911628921046228791)
      ·
        refine ⟨63710999867443381569343187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42473999911628921046228791 63710999867443381569343187)
        ·
          refine ⟨95566499801165072354014781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63710999867443381569343187 95566499801165072354014781)
          ·
            refine ⟨35837437425436902132755543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95566499801165072354014781 35837437425436902132755543)
            ·
              refine ⟨53756156138155353199133315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35837437425436902132755543 53756156138155353199133315)
              ·
                refine ⟨80634234207233029798699973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53756156138155353199133315 80634234207233029798699973)
                ·
                  refine ⟨15118918913856193087256245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80634234207233029798699973 15118918913856193087256245)
                  ·
                    refine ⟨1417398648174018101930273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15118918913856193087256245 1417398648174018101930273)
                    ·
                      rfl

theorem cell23_8281122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_8281122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281122 prefixEnd_8281122 := by exact prefixLift 8281122
  have htrace : WordTrace (prefixWord ++ tailWord_8281122) baseStart_8281122 baseEnd_8281122 := by
    simpa [prefixWord, tailWord_8281122, baseEnd_8281122] using wordTrace_append hprefix tailTrace_8281122
  have hstable : (prefixWord ++ tailWord_8281122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281122).length < 2 ^ (prefixWord ++ tailWord_8281122).sum := by decide
  have hdescent : baseEnd_8281122 < baseStart_8281122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281152 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_8281152 : Nat := 118140960795 + 8281152 * 2 ^ 59
def prefixEnd_8281152 : Nat := 4983230072969 + 3 ^ 40 * 8281152 * 2
def baseEnd_8281152 : Nat := 1417403782980563062805227

theorem tailTrace_8281152 : CollatzResearch.WordTrace tailWord_8281152 prefixEnd_8281152 1417403782980563062805227 := by
  unfold tailWord_8281152
  simp only [CollatzResearch.WordTrace]
  refine ⟨151019213447404043503942855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201358951263205391338590473 151019213447404043503942855)
  ·
    refine ⟨226528820171106065255914283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151019213447404043503942855 226528820171106065255914283)
    ·
      refine ⟨339793230256659097883871425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226528820171106065255914283 339793230256659097883871425)
      ·
        refine ⟨254844922692494323412903569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339793230256659097883871425 254844922692494323412903569)
        ·
          refine ⟨191133692019370742559677677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254844922692494323412903569 191133692019370742559677677)
          ·
            refine ⟨71675134507264028459879129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191133692019370742559677677 71675134507264028459879129)
            ·
              refine ⟨53756350880448021344909347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71675134507264028459879129 53756350880448021344909347)
              ·
                refine ⟨80634526320672032017364021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53756350880448021344909347 80634526320672032017364021)
                ·
                  refine ⟨7559486842563003001627877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80634526320672032017364021 7559486842563003001627877)
                  ·
                    refine ⟨1417403782980563062805227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7559486842563003001627877 1417403782980563062805227)
                    ·
                      rfl

theorem cell23_8281152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_8281152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281152 prefixEnd_8281152 := by exact prefixLift 8281152
  have htrace : WordTrace (prefixWord ++ tailWord_8281152) baseStart_8281152 baseEnd_8281152 := by
    simpa [prefixWord, tailWord_8281152, baseEnd_8281152] using wordTrace_append hprefix tailTrace_8281152
  have hstable : (prefixWord ++ tailWord_8281152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281152).length < 2 ^ (prefixWord ++ tailWord_8281152).sum := by decide
  have hdescent : baseEnd_8281152 < baseStart_8281152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281159 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_8281159 : Nat := 118140960795 + 8281159 * 2 ^ 59
def prefixEnd_8281159 : Nat := 4983230072969 + 3 ^ 40 * 8281159 * 2
def baseEnd_8281159 : Nat := 4252214943306270661028149

theorem tailTrace_8281159 : CollatzResearch.WordTrace tailWord_8281159 prefixEnd_8281159 4252214943306270661028149 := by
  unfold tailWord_8281159
  simp only [CollatzResearch.WordTrace]
  refine ⟨302038682205782727203390531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201359121470521818135593687 302038682205782727203390531)
  ·
    refine ⟨453058023308674090805085797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302038682205782727203390531 453058023308674090805085797)
    ·
      refine ⟨84948379370376392025953587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453058023308674090805085797 84948379370376392025953587)
      ·
        refine ⟨127422569055564588038930381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84948379370376392025953587 127422569055564588038930381)
        ·
          refine ⟨47783463395836720514598893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127422569055564588038930381 47783463395836720514598893)
          ·
            refine ⟨17918798773438770192974585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47783463395836720514598893 17918798773438770192974585)
            ·
              refine ⟨13439099080079077644730939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17918798773438770192974585 13439099080079077644730939)
              ·
                refine ⟨20158648620118616467096409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13439099080079077644730939 20158648620118616467096409)
                ·
                  refine ⟨15118986465088962350322307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20158648620118616467096409 15118986465088962350322307)
                  ·
                    refine ⟨22678479697633443525483461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15118986465088962350322307 22678479697633443525483461)
                    ·
                      refine ⟨4252214943306270661028149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22678479697633443525483461 4252214943306270661028149)
                      ·
                        rfl

theorem cell23_8281159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_8281159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281159 prefixEnd_8281159 := by exact prefixLift 8281159
  have htrace : WordTrace (prefixWord ++ tailWord_8281159) baseStart_8281159 baseEnd_8281159 := by
    simpa [prefixWord, tailWord_8281159, baseEnd_8281159] using wordTrace_append hprefix tailTrace_8281159
  have hstable : (prefixWord ++ tailWord_8281159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281159).length < 2 ^ (prefixWord ++ tailWord_8281159).sum := by decide
  have hdescent : baseEnd_8281159 < baseStart_8281159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281162 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_8281162 : Nat := 118140960795 + 8281162 * 2 ^ 59
def prefixEnd_8281162 : Nat := 4983230072969 + 3 ^ 40 * 8281162 * 2
def baseEnd_8281162 : Nat := 4252216483748234149290635

theorem tailTrace_8281162 : CollatzResearch.WordTrace tailWord_8281162 prefixEnd_8281162 4252216483748234149290635 := by
  unfold tailWord_8281162
  simp only [CollatzResearch.WordTrace]
  refine ⟨75509697906192964678937435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201359194416514572477166493 75509697906192964678937435)
  ·
    refine ⟨113264546859289447018406153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75509697906192964678937435 113264546859289447018406153)
    ·
      refine ⟨84948410144467085263804615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113264546859289447018406153 84948410144467085263804615)
      ·
        refine ⟨127422615216700627895706923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84948410144467085263804615 127422615216700627895706923)
        ·
          refine ⟨191133922825050941843560385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127422615216700627895706923 191133922825050941843560385)
          ·
            refine ⟨143350442118788206382670289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191133922825050941843560385 143350442118788206382670289)
            ·
              refine ⟨107512831589091154787002717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143350442118788206382670289 107512831589091154787002717)
              ·
                refine ⟨40317311845909183045126019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107512831589091154787002717 40317311845909183045126019)
                ·
                  refine ⟨60475967768863774567689029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40317311845909183045126019 60475967768863774567689029)
                  ·
                    refine ⟨11339243956661957731441693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60475967768863774567689029 11339243956661957731441693)
                    ·
                      refine ⟨4252216483748234149290635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11339243956661957731441693 4252216483748234149290635)
                      ·
                        rfl

theorem cell23_8281162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_8281162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281162 prefixEnd_8281162 := by exact prefixLift 8281162
  have htrace : WordTrace (prefixWord ++ tailWord_8281162) baseStart_8281162 baseEnd_8281162 := by
    simpa [prefixWord, tailWord_8281162, baseEnd_8281162] using wordTrace_append hprefix tailTrace_8281162
  have hstable : (prefixWord ++ tailWord_8281162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281162).length < 2 ^ (prefixWord ++ tailWord_8281162).sum := by decide
  have hdescent : baseEnd_8281162 < baseStart_8281162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281212 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_8281212 : Nat := 118140960795 + 8281212 * 2 ^ 59
def prefixEnd_8281212 : Nat := 4983230072969 + 3 ^ 40 * 8281212 * 2
def baseEnd_8281212 : Nat := 1417414052593652984555135

theorem tailTrace_8281212 : CollatzResearch.WordTrace tailWord_8281212 prefixEnd_8281212 1417414052593652984555135 := by
  unfold tailWord_8281212
  simp only [CollatzResearch.WordTrace]
  refine ⟨151020307637295358627534945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201360410183060478170046593 151020307637295358627534945)
  ·
    refine ⟨113265230727971518970651209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151020307637295358627534945 113265230727971518970651209)
    ·
      refine ⟨84948923045978639227988407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113265230727971518970651209 84948923045978639227988407)
      ·
        refine ⟨127423384568967958841982611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84948923045978639227988407 127423384568967958841982611)
        ·
          refine ⟨191135076853451938262973917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127423384568967958841982611 191135076853451938262973917)
          ·
            refine ⟨71675653820044476848615219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191135076853451938262973917 71675653820044476848615219)
            ·
              refine ⟨107513480730066715272922829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71675653820044476848615219 107513480730066715272922829)
              ·
                refine ⟨40317555273775018227346061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107513480730066715272922829 40317555273775018227346061)
                ·
                  refine ⟨15119083227665631835254773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40317555273775018227346061 15119083227665631835254773)
                  ·
                    refine ⟨1417414052593652984555135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15119083227665631835254773 1417414052593652984555135)
                    ·
                      rfl

theorem cell23_8281212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_8281212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281212 prefixEnd_8281212 := by exact prefixLift 8281212
  have htrace : WordTrace (prefixWord ++ tailWord_8281212) baseStart_8281212 baseEnd_8281212 := by
    simpa [prefixWord, tailWord_8281212, baseEnd_8281212] using wordTrace_append hprefix tailTrace_8281212
  have hstable : (prefixWord ++ tailWord_8281212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281212).length < 2 ^ (prefixWord ++ tailWord_8281212).sum := by decide
  have hdescent : baseEnd_8281212 < baseStart_8281212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281219 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 5, 2]
def baseStart_8281219 : Nat := 118140960795 + 8281219 * 2 ^ 59
def prefixEnd_8281219 : Nat := 4983230072969 + 3 ^ 40 * 8281219 * 2
def baseEnd_8281219 : Nat := 4252245752145540426277873

theorem tailTrace_8281219 : CollatzResearch.WordTrace tailWord_8281219 prefixEnd_8281219 4252245752145540426277873 := by
  unfold tailWord_8281219
  simp only [CollatzResearch.WordTrace]
  refine ⟨302040870585565357450574711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201360580390376904967049807 302040870585565357450574711)
  ·
    refine ⟨453061305878348036175862067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302040870585565357450574711 453061305878348036175862067)
    ·
      refine ⟨679591958817522054263793101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453061305878348036175862067 679591958817522054263793101)
      ·
        refine ⟨254846984556570770348922413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679591958817522054263793101 254846984556570770348922413)
        ·
          refine ⟨95567619208714038880845905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254846984556570770348922413 95567619208714038880845905)
          ·
            refine ⟨71675714406535529160634429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95567619208714038880845905 71675714406535529160634429)
            ·
              refine ⟨26878392902450823435237911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71675714406535529160634429 26878392902450823435237911)
              ·
                refine ⟨40317589353676235152856867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26878392902450823435237911 40317589353676235152856867)
                ·
                  refine ⟨60476384030514352729285301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40317589353676235152856867 60476384030514352729285301)
                  ·
                    refine ⟨5669661002860720568370497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60476384030514352729285301 5669661002860720568370497)
                    ·
                      refine ⟨4252245752145540426277873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669661002860720568370497 4252245752145540426277873)
                      ·
                        rfl

theorem cell23_8281219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_8281219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281219 prefixEnd_8281219 := by exact prefixLift 8281219
  have htrace : WordTrace (prefixWord ++ tailWord_8281219) baseStart_8281219 baseEnd_8281219 := by
    simpa [prefixWord, tailWord_8281219, baseEnd_8281219] using wordTrace_append hprefix tailTrace_8281219
  have hstable : (prefixWord ++ tailWord_8281219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281219).length < 2 ^ (prefixWord ++ tailWord_8281219).sum := by decide
  have hdescent : baseEnd_8281219 < baseStart_8281219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281232 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_8281232 : Nat := 118140960795 + 8281232 * 2 ^ 59
def prefixEnd_8281232 : Nat := 4983230072969 + 3 ^ 40 * 8281232 * 2
def baseEnd_8281232 : Nat := 4252252427394048875415313

theorem tailTrace_8281232 : CollatzResearch.WordTrace tailWord_8281232 prefixEnd_8281232 4252252427394048875415313 := by
  unfold tailWord_8281232
  simp only [CollatzResearch.WordTrace]
  refine ⟨151020672367259130335398975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201360896489678840447198633 151020672367259130335398975)
  ·
    refine ⟨226531008550888695503098463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151020672367259130335398975 226531008550888695503098463)
    ·
      refine ⟨339796512826333043254647695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226531008550888695503098463 339796512826333043254647695)
      ·
        refine ⟨509694769239499564881971543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339796512826333043254647695 509694769239499564881971543)
        ·
          refine ⟨764542153859249347322957315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509694769239499564881971543 764542153859249347322957315)
          ·
            refine ⟨1146813230788874020984435973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764542153859249347322957315 1146813230788874020984435973)
            ·
              refine ⟨215027480772913878934581745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1146813230788874020984435973 215027480772913878934581745)
              ·
                refine ⟨161270610579685409200936309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215027480772913878934581745 161270610579685409200936309)
                ·
                  refine ⟨15119119741845507112587779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161270610579685409200936309 15119119741845507112587779)
                  ·
                    refine ⟨22678679612768260668881669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15119119741845507112587779 22678679612768260668881669)
                    ·
                      refine ⟨4252252427394048875415313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22678679612768260668881669 4252252427394048875415313)
                      ·
                        rfl

theorem cell23_8281232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_8281232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281232 prefixEnd_8281232 := by exact prefixLift 8281232
  have htrace : WordTrace (prefixWord ++ tailWord_8281232) baseStart_8281232 baseEnd_8281232 := by
    simpa [prefixWord, tailWord_8281232, baseEnd_8281232] using wordTrace_append hprefix tailTrace_8281232
  have hstable : (prefixWord ++ tailWord_8281232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281232).length < 2 ^ (prefixWord ++ tailWord_8281232).sum := by decide
  have hdescent : baseEnd_8281232 < baseStart_8281232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281266 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_8281266 : Nat := 118140960795 + 8281266 * 2 ^ 59
def prefixEnd_8281266 : Nat := 4983230072969 + 3 ^ 40 * 8281266 * 2
def baseEnd_8281266 : Nat := 4252269885736301742390157

theorem tailTrace_8281266 : CollatzResearch.WordTrace tailWord_8281266 prefixEnd_8281266 4252269885736301742390157 := by
  unfold tailWord_8281266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75510646204098771119383913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201361723210930056318357101 75510646204098771119383913)
  ·
    refine ⟨56632984653074078339537935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75510646204098771119383913 56632984653074078339537935)
    ·
      refine ⟨84949476979611117509306903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56632984653074078339537935 84949476979611117509306903)
      ·
        refine ⟨127424215469416676263960355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84949476979611117509306903 127424215469416676263960355)
        ·
          refine ⟨191136323204125014395940533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127424215469416676263960355 191136323204125014395940533)
          ·
            refine ⟨17919030300386720099619425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191136323204125014395940533 17919030300386720099619425)
            ·
              refine ⟨13439272725290040074714569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17919030300386720099619425 13439272725290040074714569)
              ·
                refine ⟨10079454543967530056035927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13439272725290040074714569 10079454543967530056035927)
                ·
                  refine ⟨15119181815951295084053891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10079454543967530056035927 15119181815951295084053891)
                  ·
                    refine ⟨22678772723926942626080837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15119181815951295084053891 22678772723926942626080837)
                    ·
                      refine ⟨4252269885736301742390157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22678772723926942626080837 4252269885736301742390157)
                      ·
                        rfl

theorem cell23_8281266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_8281266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281266 prefixEnd_8281266 := by exact prefixLift 8281266
  have htrace : WordTrace (prefixWord ++ tailWord_8281266) baseStart_8281266 baseEnd_8281266 := by
    simpa [prefixWord, tailWord_8281266, baseEnd_8281266] using wordTrace_append hprefix tailTrace_8281266
  have hstable : (prefixWord ++ tailWord_8281266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281266).length < 2 ^ (prefixWord ++ tailWord_8281266).sum := by decide
  have hdescent : baseEnd_8281266 < baseStart_8281266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281283 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 1, 2, 2]
def baseStart_8281283 : Nat := 118140960795 + 8281283 * 2 ^ 59
def prefixEnd_8281283 : Nat := 4983230072969 + 3 ^ 40 * 8281283 * 2
def baseEnd_8281283 : Nat := 4252278614907428175877579

theorem tailTrace_8281283 : CollatzResearch.WordTrace tailWord_8281283 prefixEnd_8281283 4252278614907428175877579 := by
  unfold tailWord_8281283
  simp only [CollatzResearch.WordTrace]
  refine ⟨302043204857333496380904503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201362136571555664253936335 302043204857333496380904503)
  ·
    refine ⟨453064807286000244571356755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302043204857333496380904503 453064807286000244571356755)
    ·
      refine ⟨679597210929000366857035133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453064807286000244571356755 679597210929000366857035133)
      ·
        refine ⟨254848954098375137571388175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679597210929000366857035133 254848954098375137571388175)
        ·
          refine ⟨382273431147562706357082263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254848954098375137571388175 382273431147562706357082263)
          ·
            refine ⟨573410146721344059535623395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382273431147562706357082263 573410146721344059535623395)
            ·
              refine ⟨860115220082016089303435093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573410146721344059535623395 860115220082016089303435093)
              ·
                refine ⟨5039737617668063023262315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 860115220082016089303435093 5039737617668063023262315)
                ·
                  refine ⟨7559606426502094534893473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5039737617668063023262315 7559606426502094534893473)
                  ·
                    refine ⟨5669704819876570901170105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7559606426502094534893473 5669704819876570901170105)
                    ·
                      refine ⟨4252278614907428175877579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669704819876570901170105 4252278614907428175877579)
                      ·
                        rfl

theorem cell23_8281283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_8281283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281283 prefixEnd_8281283 := by exact prefixLift 8281283
  have htrace : WordTrace (prefixWord ++ tailWord_8281283) baseStart_8281283 baseEnd_8281283 := by
    simpa [prefixWord, tailWord_8281283, baseEnd_8281283] using wordTrace_append hprefix tailTrace_8281283
  have hstable : (prefixWord ++ tailWord_8281283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281283).length < 2 ^ (prefixWord ++ tailWord_8281283).sum := by decide
  have hdescent : baseEnd_8281283 < baseStart_8281283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281373 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_8281373 : Nat := 118140960795 + 8281373 * 2 ^ 59
def prefixEnd_8281373 : Nat := 4983230072969 + 3 ^ 40 * 8281373 * 2
def baseEnd_8281373 : Nat := 4252324828166332823752165

theorem tailTrace_8281373 : CollatzResearch.WordTrace tailWord_8281373 prefixEnd_8281373 4252324828166332823752165 := by
  unfold tailWord_8281373
  simp only [CollatzResearch.WordTrace]
  refine ⟨302046487427007441751680773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201364324951338294501120515 302046487427007441751680773)
  ·
    refine ⟨56633716392563895328440145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302046487427007441751680773 56633716392563895328440145)
    ·
      refine ⟨42475287294422921496330109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56633716392563895328440145 42475287294422921496330109)
      ·
        refine ⟨15928232735408595561123791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42475287294422921496330109 15928232735408595561123791)
        ·
          refine ⟨23892349103112893341685687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15928232735408595561123791 23892349103112893341685687)
          ·
            refine ⟨35838523654669340012528531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23892349103112893341685687 35838523654669340012528531)
            ·
              refine ⟨53757785482004010018792797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35838523654669340012528531 53757785482004010018792797)
              ·
                refine ⟨20159169555751503757047299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53757785482004010018792797 20159169555751503757047299)
                ·
                  refine ⟨30238754333627255635570949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20159169555751503757047299 30238754333627255635570949)
                  ·
                    refine ⟨5669766437555110431669553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30238754333627255635570949 5669766437555110431669553)
                    ·
                      refine ⟨4252324828166332823752165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5669766437555110431669553 4252324828166332823752165)
                      ·
                        rfl

theorem cell23_8281373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_8281373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281373 prefixEnd_8281373 := by exact prefixLift 8281373
  have htrace : WordTrace (prefixWord ++ tailWord_8281373) baseStart_8281373 baseEnd_8281373 := by
    simpa [prefixWord, tailWord_8281373, baseEnd_8281373] using wordTrace_append hprefix tailTrace_8281373
  have hstable : (prefixWord ++ tailWord_8281373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281373).length < 2 ^ (prefixWord ++ tailWord_8281373).sum := by decide
  have hdescent : baseEnd_8281373 < baseStart_8281373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281379 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 7]
def baseStart_8281379 : Nat := 118140960795 + 8281379 * 2 ^ 59
def prefixEnd_8281379 : Nat := 4983230072969 + 3 ^ 40 * 8281379 * 2
def baseEnd_8281379 : Nat := 472480878783362200030793

theorem tailTrace_8281379 : CollatzResearch.WordTrace tailWord_8281379 prefixEnd_8281379 472480878783362200030793 := by
  unfold tailWord_8281379
  simp only [CollatzResearch.WordTrace]
  refine ⟨302046706264985704776399191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201364470843323803184266127 302046706264985704776399191)
  ·
    refine ⟨453070059397478557164598787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302046706264985704776399191 453070059397478557164598787)
    ·
      refine ⟨679605089096217835746898181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453070059397478557164598787 679605089096217835746898181)
      ·
        refine ⟨127425954205540844202543409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 679605089096217835746898181 127425954205540844202543409)
        ·
          refine ⟨95569465654155633151907557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127425954205540844202543409 95569465654155633151907557)
          ·
            refine ⟨17919274810154181215982667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95569465654155633151907557 17919274810154181215982667)
            ·
              refine ⟨26878912215231271823974001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919274810154181215982667 26878912215231271823974001)
              ·
                refine ⟨20159184161423453867980501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26878912215231271823974001 20159184161423453867980501)
                ·
                  refine ⟨472480878783362200030793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20159184161423453867980501 472480878783362200030793)
                  ·
                    rfl

theorem cell23_8281379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 7].length) (baseStart_8281379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281379 prefixEnd_8281379 := by exact prefixLift 8281379
  have htrace : WordTrace (prefixWord ++ tailWord_8281379) baseStart_8281379 baseEnd_8281379 := by
    simpa [prefixWord, tailWord_8281379, baseEnd_8281379] using wordTrace_append hprefix tailTrace_8281379
  have hstable : (prefixWord ++ tailWord_8281379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281379).length < 2 ^ (prefixWord ++ tailWord_8281379).sum := by decide
  have hdescent : baseEnd_8281379 < baseStart_8281379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281406 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_8281406 : Nat := 118140960795 + 8281406 * 2 ^ 59
def prefixEnd_8281406 : Nat := 4983230072969 + 3 ^ 40 * 8281406 * 2
def baseEnd_8281406 : Nat := 4252341773027931194639513

theorem tailTrace_8281406 : CollatzResearch.WordTrace tailWord_8281406 prefixEnd_8281406 4252341773027931194639513 := by
  unfold tailWord_8281406
  simp only [CollatzResearch.WordTrace]
  refine ⟨37755961379485986048454009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201365127357258592258421381 37755961379485986048454009)
  ·
    refine ⟨28316971034614489536340507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37755961379485986048454009 28316971034614489536340507)
    ·
      refine ⟨42475456551921734304510761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28316971034614489536340507 42475456551921734304510761)
      ·
        refine ⟨31856592413941300728383071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42475456551921734304510761 31856592413941300728383071)
        ·
          refine ⟨47784888620911951092574607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31856592413941300728383071 47784888620911951092574607)
          ·
            refine ⟨71677332931367926638861911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47784888620911951092574607 71677332931367926638861911)
            ·
              refine ⟨107515999397051889958292867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71677332931367926638861911 107515999397051889958292867)
              ·
                refine ⟨161273999095577834937439301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107515999397051889958292867 161273999095577834937439301)
                ·
                  refine ⟨30238874830420844050769869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161273999095577834937439301 30238874830420844050769869)
                  ·
                    refine ⟨11339578061407816519038701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30238874830420844050769869 11339578061407816519038701)
                    ·
                      refine ⟨4252341773027931194639513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11339578061407816519038701 4252341773027931194639513)
                      ·
                        rfl

theorem cell23_8281406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_8281406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281406 prefixEnd_8281406 := by exact prefixLift 8281406
  have htrace : WordTrace (prefixWord ++ tailWord_8281406) baseStart_8281406 baseEnd_8281406 := by
    simpa [prefixWord, tailWord_8281406, baseEnd_8281406] using wordTrace_append hprefix tailTrace_8281406
  have hstable : (prefixWord ++ tailWord_8281406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281406).length < 2 ^ (prefixWord ++ tailWord_8281406).sum := by decide
  have hdescent : baseEnd_8281406 < baseStart_8281406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281466 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_8281466 : Nat := 118140960795 + 8281466 * 2 ^ 59
def prefixEnd_8281466 : Nat := 4983230072969 + 3 ^ 40 * 8281466 * 2
def baseEnd_8281466 : Nat := 4252372581867200959889237

theorem tailTrace_8281466 : CollatzResearch.WordTrace tailWord_8281466 prefixEnd_8281466 4252372581867200959889237 := by
  unfold tailWord_8281466
  simp only [CollatzResearch.WordTrace]
  refine ⟨75512469853917629658704063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201366586277113679089877501 75512469853917629658704063)
  ·
    refine ⟨113268704780876444488056095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75512469853917629658704063 113268704780876444488056095)
    ·
      refine ⟨169903057171314666732084143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113268704780876444488056095 169903057171314666732084143)
      ·
        refine ⟨254854585756972000098126215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169903057171314666732084143 254854585756972000098126215)
        ·
          refine ⟨382281878635458000147189323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254854585756972000098126215 382281878635458000147189323)
          ·
            refine ⟨573422817953187000220783985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382281878635458000147189323 573422817953187000220783985)
            ·
              refine ⟨430067113464890250165587989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573422817953187000220783985 430067113464890250165587989)
              ·
                refine ⟨20159395943666730476511937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430067113464890250165587989 20159395943666730476511937)
                ·
                  refine ⟨15119546957750047857383953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20159395943666730476511937 15119546957750047857383953)
                  ·
                    refine ⟨11339660218312535893037965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15119546957750047857383953 11339660218312535893037965)
                    ·
                      refine ⟨4252372581867200959889237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11339660218312535893037965 4252372581867200959889237)
                      ·
                        rfl

theorem cell23_8281466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_8281466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281466 prefixEnd_8281466 := by exact prefixLift 8281466
  have htrace : WordTrace (prefixWord ++ tailWord_8281466) baseStart_8281466 baseEnd_8281466 := by
    simpa [prefixWord, tailWord_8281466, baseEnd_8281466] using wordTrace_append hprefix tailTrace_8281466
  have hstable : (prefixWord ++ tailWord_8281466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281466).length < 2 ^ (prefixWord ++ tailWord_8281466).sum := by decide
  have hdescent : baseEnd_8281466 < baseStart_8281466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281469 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 8]
def baseStart_8281469 : Nat := 118140960795 + 8281469 * 2 ^ 59
def prefixEnd_8281469 : Nat := 4983230072969 + 3 ^ 40 * 8281469 * 2
def baseEnd_8281469 : Nat := 472486013589907160905747

theorem tailTrace_8281469 : CollatzResearch.WordTrace tailWord_8281469 prefixEnd_8281469 472486013589907160905747 := by
  unfold tailWord_8281469
  simp only [CollatzResearch.WordTrace]
  refine ⟨302049988834659650147175461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201366659223106433431450307 302049988834659650147175461)
  ·
    refine ⟨56634372906498684402595399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302049988834659650147175461 56634372906498684402595399)
    ·
      refine ⟨84951559359748026603893099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56634372906498684402595399 84951559359748026603893099)
      ·
        refine ⟨127427339039622039905839649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84951559359748026603893099 127427339039622039905839649)
        ·
          refine ⟨95570504279716529929379737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127427339039622039905839649 95570504279716529929379737)
          ·
            refine ⟨71677878209787397447034803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95570504279716529929379737 71677878209787397447034803)
            ·
              refine ⟨107516817314681096170552205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71677878209787397447034803 107516817314681096170552205)
              ·
                refine ⟨40318806493005411063957077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107516817314681096170552205 40318806493005411063957077)
                ·
                  refine ⟨472486013589907160905747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40318806493005411063957077 472486013589907160905747)
                  ·
                    rfl

theorem cell23_8281469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_8281469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281469 prefixEnd_8281469 := by exact prefixLift 8281469
  have htrace : WordTrace (prefixWord ++ tailWord_8281469) baseStart_8281469 baseEnd_8281469 := by
    simpa [prefixWord, tailWord_8281469, baseEnd_8281469] using wordTrace_append hprefix tailTrace_8281469
  have hstable : (prefixWord ++ tailWord_8281469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281469).length < 2 ^ (prefixWord ++ tailWord_8281469).sum := by decide
  have hdescent : baseEnd_8281469 < baseStart_8281469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281470 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8281470 : Nat := 118140960795 + 8281470 * 2 ^ 59
def prefixEnd_8281470 : Nat := 4983230072969 + 3 ^ 40 * 8281470 * 2
def baseEnd_8281470 : Nat := 4252374635789818944239219

theorem tailTrace_8281470 : CollatzResearch.WordTrace tailWord_8281470 prefixEnd_8281470 4252374635789818944239219 := by
  unfold tailWord_8281470
  simp only [CollatzResearch.WordTrace]
  refine ⟨37756253163457003414745233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201366683538437351545307909 37756253163457003414745233)
  ·
    refine ⟨28317189872592752561058925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37756253163457003414745233 28317189872592752561058925)
    ·
      refine ⟨10618946202222282210397097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28317189872592752561058925 10618946202222282210397097)
      ·
        refine ⟨7964209651666711657797823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10618946202222282210397097 7964209651666711657797823)
        ·
          refine ⟨11946314477500067486696735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964209651666711657797823 11946314477500067486696735)
          ·
            refine ⟨17919471716250101230045103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946314477500067486696735 17919471716250101230045103)
            ·
              refine ⟨26879207574375151845067655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919471716250101230045103 26879207574375151845067655)
              ·
                refine ⟨40318811361562727767601483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26879207574375151845067655 40318811361562727767601483)
                ·
                  refine ⟨60478217042344091651402225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40318811361562727767601483 60478217042344091651402225)
                  ·
                    refine ⟨45358662781758068738551669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60478217042344091651402225 45358662781758068738551669)
                    ·
                      refine ⟨4252374635789818944239219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45358662781758068738551669 4252374635789818944239219)
                      ·
                        rfl

theorem cell23_8281470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8281470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281470 prefixEnd_8281470 := by exact prefixLift 8281470
  have htrace : WordTrace (prefixWord ++ tailWord_8281470) baseStart_8281470 baseEnd_8281470 := by
    simpa [prefixWord, tailWord_8281470, baseEnd_8281470] using wordTrace_append hprefix tailTrace_8281470
  have hstable : (prefixWord ++ tailWord_8281470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281470).length < 2 ^ (prefixWord ++ tailWord_8281470).sum := by decide
  have hdescent : baseEnd_8281470 < baseStart_8281470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281499 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 9, 5]
def baseStart_8281499 : Nat := 118140960795 + 8281499 * 2 ^ 59
def prefixEnd_8281499 : Nat := 4983230072969 + 3 ^ 40 * 8281499 * 2
def baseEnd_8281499 : Nat := 1417463175576266443592195

theorem tailTrace_8281499 : CollatzResearch.WordTrace tailWord_8281499 prefixEnd_8281499 1417463175576266443592195 := by
  unfold tailWord_8281499
  simp only [CollatzResearch.WordTrace]
  refine ⟨302051083024550965270767551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201367388683033976847178367 302051083024550965270767551)
  ·
    refine ⟨453076624536826447906151327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302051083024550965270767551 453076624536826447906151327)
    ·
      refine ⟨679614936805239671859226991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453076624536826447906151327 679614936805239671859226991)
      ·
        refine ⟨1019422405207859507788840487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679614936805239671859226991 1019422405207859507788840487)
        ·
          refine ⟨1529133607811789261683260731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019422405207859507788840487 1529133607811789261683260731)
          ·
            refine ⟨2293700411717683892524891097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529133607811789261683260731 2293700411717683892524891097)
            ·
              refine ⟨1720275308788262919393668323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2293700411717683892524891097 1720275308788262919393668323)
              ·
                refine ⟨2580412963182394379090502485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1720275308788262919393668323 2580412963182394379090502485)
                ·
                  refine ⟨15119607206146842064983413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2580412963182394379090502485 15119607206146842064983413)
                  ·
                    refine ⟨1417463175576266443592195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15119607206146842064983413 1417463175576266443592195)
                    ·
                      rfl

theorem cell23_8281499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 5].length) (baseStart_8281499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281499 prefixEnd_8281499 := by exact prefixLift 8281499
  have htrace : WordTrace (prefixWord ++ tailWord_8281499) baseStart_8281499 baseEnd_8281499 := by
    simpa [prefixWord, tailWord_8281499, baseEnd_8281499] using wordTrace_append hprefix tailTrace_8281499
  have hstable : (prefixWord ++ tailWord_8281499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281499).length < 2 ^ (prefixWord ++ tailWord_8281499).sum := by decide
  have hdescent : baseEnd_8281499 < baseStart_8281499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281509 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_8281509 : Nat := 118140960795 + 8281509 * 2 ^ 59
def prefixEnd_8281509 : Nat := 4983230072969 + 3 ^ 40 * 8281509 * 2
def baseEnd_8281509 : Nat := 4252394661535344291651539

theorem tailTrace_8281509 : CollatzResearch.WordTrace tailWord_8281509 prefixEnd_8281509 4252394661535344291651539 := by
  unfold tailWord_8281509
  simp only [CollatzResearch.WordTrace]
  refine ⟨302051447754514736978631581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201367631836343157985754387 302051447754514736978631581)
  ·
    refine ⟨113269292907943026366986843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302051447754514736978631581 113269292907943026366986843)
    ·
      refine ⟨169903939361914539550480265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113269292907943026366986843 169903939361914539550480265)
      ·
        refine ⟨127427954521435904662860199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169903939361914539550480265 127427954521435904662860199)
        ·
          refine ⟨191141931782153856994290299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127427954521435904662860199 191141931782153856994290299)
          ·
            refine ⟨286712897673230785491435449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191141931782153856994290299 286712897673230785491435449)
            ·
              refine ⟨215034673254923089118576587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286712897673230785491435449 215034673254923089118576587)
              ·
                refine ⟨322552009882384633677864881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215034673254923089118576587 322552009882384633677864881)
                ·
                  refine ⟨241914007411788475258398661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322552009882384633677864881 241914007411788475258398661)
                  ·
                    refine ⟨45358876389710339110949749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241914007411788475258398661 45358876389710339110949749)
                    ·
                      refine ⟨4252394661535344291651539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45358876389710339110949749 4252394661535344291651539)
                      ·
                        rfl

theorem cell23_8281509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_8281509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281509 prefixEnd_8281509 := by exact prefixLift 8281509
  have htrace : WordTrace (prefixWord ++ tailWord_8281509) baseStart_8281509 baseEnd_8281509 := by
    simpa [prefixWord, tailWord_8281509, baseEnd_8281509] using wordTrace_append hprefix tailTrace_8281509
  have hstable : (prefixWord ++ tailWord_8281509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281509).length < 2 ^ (prefixWord ++ tailWord_8281509).sum := by decide
  have hdescent : baseEnd_8281509 < baseStart_8281509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281516 : List Nat := [2, 2, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_8281516 : Nat := 118140960795 + 8281516 * 2 ^ 59
def prefixEnd_8281516 : Nat := 4983230072969 + 3 ^ 40 * 8281516 * 2
def baseEnd_8281516 : Nat := 1417466085299975254754669

theorem tailTrace_8281516 : CollatzResearch.WordTrace tailWord_8281516 prefixEnd_8281516 1417466085299975254754669 := by
  unfold tailWord_8281516
  simp only [CollatzResearch.WordTrace]
  refine ⟨151025851532744688587068201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201367802043659584782757601 151025851532744688587068201)
  ·
    refine ⟨113269388649558516440301151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151025851532744688587068201 113269388649558516440301151)
    ·
      refine ⟨169904082974337774660451727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113269388649558516440301151 169904082974337774660451727)
      ·
        refine ⟨254856124461506661990677591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169904082974337774660451727 254856124461506661990677591)
        ·
          refine ⟨382284186692259992986016387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254856124461506661990677591 382284186692259992986016387)
          ·
            refine ⟨573426280038389989479024581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382284186692259992986016387 573426280038389989479024581)
            ·
              refine ⟨107517427507198123027317109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573426280038389989479024581 107517427507198123027317109)
              ·
                refine ⟨10079758828799824033810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107517427507198123027317109 10079758828799824033810979)
                ·
                  refine ⟨15119638243199736050716469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10079758828799824033810979 15119638243199736050716469)
                  ·
                    refine ⟨1417466085299975254754669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15119638243199736050716469 1417466085299975254754669)
                    ·
                      rfl

theorem cell23_8281516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_8281516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281516 prefixEnd_8281516 := by exact prefixLift 8281516
  have htrace : WordTrace (prefixWord ++ tailWord_8281516) baseStart_8281516 baseEnd_8281516 := by
    simpa [prefixWord, tailWord_8281516, baseEnd_8281516] using wordTrace_append hprefix tailTrace_8281516
  have hstable : (prefixWord ++ tailWord_8281516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281516).length < 2 ^ (prefixWord ++ tailWord_8281516).sum := by decide
  have hdescent : baseEnd_8281516 < baseStart_8281516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281536 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_8281536 : Nat := 118140960795 + 8281536 * 2 ^ 59
def prefixEnd_8281536 : Nat := 4983230072969 + 3 ^ 40 * 8281536 * 2
def baseEnd_8281536 : Nat := 4252408525513015686013915

theorem tailTrace_8281536 : CollatzResearch.WordTrace tailWord_8281536 prefixEnd_8281536 4252408525513015686013915 := by
  unfold tailWord_8281536
  simp only [CollatzResearch.WordTrace]
  refine ⟨151026216262708460294932231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201368288350277947059909641 151026216262708460294932231)
  ·
    refine ⟨226539324394062690442398347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151026216262708460294932231 226539324394062690442398347)
    ·
      refine ⟨339808986591094035663597521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226539324394062690442398347 339808986591094035663597521)
      ·
        refine ⟨254856739943320526747698141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339808986591094035663597521 254856739943320526747698141)
        ·
          refine ⟨95571277478745197530386803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254856739943320526747698141 95571277478745197530386803)
          ·
            refine ⟨143356916218117796295580205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95571277478745197530386803 143356916218117796295580205)
            ·
              refine ⟨53758843581794173610842577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143356916218117796295580205 53758843581794173610842577)
              ·
                refine ⟨40319132686345630208131933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53758843581794173610842577 40319132686345630208131933)
                ·
                  refine ⟨15119674757379611328049475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40319132686345630208131933 15119674757379611328049475)
                  ·
                    refine ⟨22679512136069416992074213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15119674757379611328049475 22679512136069416992074213)
                    ·
                      refine ⟨4252408525513015686013915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22679512136069416992074213 4252408525513015686013915)
                      ·
                        rfl

theorem cell23_8281536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_8281536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281536 prefixEnd_8281536 := by exact prefixLift 8281536
  have htrace : WordTrace (prefixWord ++ tailWord_8281536) baseStart_8281536 baseEnd_8281536 := by
    simpa [prefixWord, tailWord_8281536, baseEnd_8281536] using wordTrace_append hprefix tailTrace_8281536
  have hstable : (prefixWord ++ tailWord_8281536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281536).length < 2 ^ (prefixWord ++ tailWord_8281536).sum := by decide
  have hdescent : baseEnd_8281536 < baseStart_8281536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281546 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_8281546 : Nat := 118140960795 + 8281546 * 2 ^ 59
def prefixEnd_8281546 : Nat := 4983230072969 + 3 ^ 40 * 8281546 * 2
def baseEnd_8281546 : Nat := 1417471220106520215629623

theorem tailTrace_8281546 : CollatzResearch.WordTrace tailWord_8281546 prefixEnd_8281546 1417471220106520215629623 := by
  unfold tailWord_8281546
  simp only [CollatzResearch.WordTrace]
  refine ⟨75513199313845173074432123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201368531503587128198485661 75513199313845173074432123)
  ·
    refine ⟨113269798970767759611648185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75513199313845173074432123 113269798970767759611648185)
    ·
      refine ⟨84952349228075819708736139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113269798970767759611648185 84952349228075819708736139)
      ·
        refine ⟨127428523842113729563104209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84952349228075819708736139 127428523842113729563104209)
        ·
          refine ⟨95571392881585297172328157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127428523842113729563104209 95571392881585297172328157)
          ·
            refine ⟨35839272330594486439623059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95571392881585297172328157 35839272330594486439623059)
            ·
              refine ⟨53758908495891729659434589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35839272330594486439623059 53758908495891729659434589)
              ·
                refine ⟨20159590685959398622287971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53758908495891729659434589 20159590685959398622287971)
                ·
                  refine ⟨30239386028939097933431957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20159590685959398622287971 30239386028939097933431957)
                  ·
                    refine ⟨1417471220106520215629623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30239386028939097933431957 1417471220106520215629623)
                    ·
                      rfl

theorem cell23_8281546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_8281546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281546 prefixEnd_8281546 := by exact prefixLift 8281546
  have htrace : WordTrace (prefixWord ++ tailWord_8281546) baseStart_8281546 baseEnd_8281546 := by
    simpa [prefixWord, tailWord_8281546, baseEnd_8281546] using wordTrace_append hprefix tailTrace_8281546
  have hstable : (prefixWord ++ tailWord_8281546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281546).length < 2 ^ (prefixWord ++ tailWord_8281546).sum := by decide
  have hdescent : baseEnd_8281546 < baseStart_8281546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281559 : List Nat := [1, 1, 3, 2, 1, 1, 1, 13]
def baseStart_8281559 : Nat := 118140960795 + 8281559 * 2 ^ 59
def prefixEnd_8281559 : Nat := 4983230072969 + 3 ^ 40 * 8281559 * 2
def baseEnd_8281559 : Nat := 157497049465484040593567

theorem tailTrace_8281559 : CollatzResearch.WordTrace tailWord_8281559 prefixEnd_8281559 157497049465484040593567 := by
  unfold tailWord_8281559
  simp only [CollatzResearch.WordTrace]
  refine ⟨302053271404333595517951731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201368847602889063678634487 302053271404333595517951731)
  ·
    refine ⟨453079907106500393276927597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302053271404333595517951731 453079907106500393276927597)
    ·
      refine ⟨169904965164937647478847849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453079907106500393276927597 169904965164937647478847849)
      ·
        refine ⟨127428723873703235609135887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169904965164937647478847849 127428723873703235609135887)
        ·
          refine ⟨191143085810554853413703831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127428723873703235609135887 191143085810554853413703831)
          ·
            refine ⟨286714628715832280120555747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191143085810554853413703831 286714628715832280120555747)
            ·
              refine ⟨430071943073748420180833621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286714628715832280120555747 430071943073748420180833621)
              ·
                refine ⟨157497049465484040593567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 430071943073748420180833621 157497049465484040593567)
                ·
                  rfl

theorem cell23_8281559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 13].length) (baseStart_8281559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281559 prefixEnd_8281559 := by exact prefixLift 8281559
  have htrace : WordTrace (prefixWord ++ tailWord_8281559) baseStart_8281559 baseEnd_8281559 := by
    simpa [prefixWord, tailWord_8281559, baseEnd_8281559] using wordTrace_append hprefix tailTrace_8281559
  have hstable : (prefixWord ++ tailWord_8281559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281559).length < 2 ^ (prefixWord ++ tailWord_8281559).sum := by decide
  have hdescent : baseEnd_8281559 < baseStart_8281559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281626 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_8281626 : Nat := 118140960795 + 8281626 * 2 ^ 59
def prefixEnd_8281626 : Nat := 4983230072969 + 3 ^ 40 * 8281626 * 2
def baseEnd_8281626 : Nat := 4252454738771920333888501

theorem tailTrace_8281626 : CollatzResearch.WordTrace tailWord_8281626 prefixEnd_8281626 4252454738771920333888501 := by
  unfold tailWord_8281626
  simp only [CollatzResearch.WordTrace]
  refine ⟨75513928773772716490160183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201370476730060577307093821 75513928773772716490160183)
  ·
    refine ⟨113270893160659074735240275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75513928773772716490160183 113270893160659074735240275)
    ·
      refine ⟨169906339740988612102860413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113270893160659074735240275 169906339740988612102860413)
      ·
        refine ⟨63714877402870729538572655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169906339740988612102860413 63714877402870729538572655)
        ·
          refine ⟨95572316104306094307858983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63714877402870729538572655 95572316104306094307858983)
          ·
            refine ⟨143358474156459141461788475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95572316104306094307858983 143358474156459141461788475)
            ·
              refine ⟨215037711234688712192682713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143358474156459141461788475 215037711234688712192682713)
              ·
                refine ⟨161278283426016534144512035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215037711234688712192682713 161278283426016534144512035)
                ·
                  refine ⟨241917425139024801216768053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161278283426016534144512035 241917425139024801216768053)
                  ·
                    refine ⟨22679758606783575114072005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241917425139024801216768053 22679758606783575114072005)
                    ·
                      refine ⟨4252454738771920333888501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22679758606783575114072005 4252454738771920333888501)
                      ·
                        rfl

theorem cell23_8281626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_8281626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281626 prefixEnd_8281626 := by exact prefixLift 8281626
  have htrace : WordTrace (prefixWord ++ tailWord_8281626) baseStart_8281626 baseEnd_8281626 := by
    simpa [prefixWord, tailWord_8281626, baseEnd_8281626] using wordTrace_append hprefix tailTrace_8281626
  have hstable : (prefixWord ++ tailWord_8281626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281626).length < 2 ^ (prefixWord ++ tailWord_8281626).sum := by decide
  have hdescent : baseEnd_8281626 < baseStart_8281626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281654 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_8281654 : Nat := 118140960795 + 8281654 * 2 ^ 59
def prefixEnd_8281654 : Nat := 4983230072969 + 3 ^ 40 * 8281654 * 2
def baseEnd_8281654 : Nat := 4252469116230246224338373

theorem tailTrace_8281654 : CollatzResearch.WordTrace tailWord_8281654 prefixEnd_8281654 4252469116230246224338373 := by
  unfold tailWord_8281654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18878546021186839171416251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201371157559326284495106677 18878546021186839171416251)
  ·
    refine ⟨28317819031780258757124377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18878546021186839171416251 28317819031780258757124377)
    ·
      refine ⟨21238364273835194067843283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28317819031780258757124377 21238364273835194067843283)
      ·
        refine ⟨31857546410752791101764925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21238364273835194067843283 31857546410752791101764925)
        ·
          refine ⟨11946579904032296663161847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31857546410752791101764925 11946579904032296663161847)
          ·
            refine ⟨17919869856048444994742771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946579904032296663161847 17919869856048444994742771)
            ·
              refine ⟨26879804784072667492114157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919869856048444994742771 26879804784072667492114157)
              ·
                refine ⟨10079926794027250309542809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26879804784072667492114157 10079926794027250309542809)
                ·
                  refine ⟨7559945095520437732157107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10079926794027250309542809 7559945095520437732157107)
                  ·
                    refine ⟨11339917643280656598235661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7559945095520437732157107 11339917643280656598235661)
                    ·
                      refine ⟨4252469116230246224338373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11339917643280656598235661 4252469116230246224338373)
                      ·
                        rfl

theorem cell23_8281654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_8281654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281654 prefixEnd_8281654 := by exact prefixLift 8281654
  have htrace : WordTrace (prefixWord ++ tailWord_8281654) baseStart_8281654 baseEnd_8281654 := by
    simpa [prefixWord, tailWord_8281654, baseEnd_8281654] using wordTrace_append hprefix tailTrace_8281654
  have hstable : (prefixWord ++ tailWord_8281654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281654).length < 2 ^ (prefixWord ++ tailWord_8281654).sum := by decide
  have hdescent : baseEnd_8281654 < baseStart_8281654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281696 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_8281696 : Nat := 118140960795 + 8281696 * 2 ^ 59
def prefixEnd_8281696 : Nat := 4983230072969 + 3 ^ 40 * 8281696 * 2
def baseEnd_8281696 : Nat := 1417496894139245020004393

theorem tailTrace_8281696 : CollatzResearch.WordTrace tailWord_8281696 prefixEnd_8281696 1417496894139245020004393 := by
  unfold tailWord_8281696
  simp only [CollatzResearch.WordTrace]
  refine ⟨151029134102418633957844471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201372178803224845277125961 151029134102418633957844471)
  ·
    refine ⟨226543701153627950936766707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151029134102418633957844471 226543701153627950936766707)
    ·
      refine ⟨339815551730441926405150061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226543701153627950936766707 339815551730441926405150061)
      ·
        refine ⟨127430831898915722401931273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339815551730441926405150061 127430831898915722401931273)
        ·
          refine ⟨95573123924186791801448455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127430831898915722401931273 95573123924186791801448455)
          ·
            refine ⟨143359685886280187702172683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95573123924186791801448455 143359685886280187702172683)
            ·
              refine ⟨215039528829420281553259025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143359685886280187702172683 215039528829420281553259025)
              ·
                refine ⟨161279646622065211164944269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215039528829420281553259025 161279646622065211164944269)
                ·
                  refine ⟨60479867483274454186854101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161279646622065211164944269 60479867483274454186854101)
                  ·
                    refine ⟨1417496894139245020004393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60479867483274454186854101 1417496894139245020004393)
                    ·
                      rfl

theorem cell23_8281696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_8281696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281696 prefixEnd_8281696 := by exact prefixLift 8281696
  have htrace : WordTrace (prefixWord ++ tailWord_8281696) baseStart_8281696 baseEnd_8281696 := by
    simpa [prefixWord, tailWord_8281696, baseEnd_8281696] using wordTrace_append hprefix tailTrace_8281696
  have hstable : (prefixWord ++ tailWord_8281696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281696).length < 2 ^ (prefixWord ++ tailWord_8281696).sum := by decide
  have hdescent : baseEnd_8281696 < baseStart_8281696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281700 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 5]
def baseStart_8281700 : Nat := 118140960795 + 8281700 * 2 ^ 59
def prefixEnd_8281700 : Nat := 4983230072969 + 3 ^ 40 * 8281700 * 2
def baseEnd_8281700 : Nat := 472499192926705893818129

theorem tailTrace_8281700 : CollatzResearch.WordTrace tailWord_8281700 prefixEnd_8281700 472499192926705893818129 := by
  unfold tailWord_8281700
  simp only [CollatzResearch.WordTrace]
  refine ⟨151029207048411388299417277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201372276064548517732556369 151029207048411388299417277)
  ·
    refine ⟨56635952643154270612281479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151029207048411388299417277 56635952643154270612281479)
    ·
      refine ⟨84953928964731405918422219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56635952643154270612281479 84953928964731405918422219)
      ·
        refine ⟨127430893447097108877633329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84953928964731405918422219 127430893447097108877633329)
        ·
          refine ⟨95573170085322831658224997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127430893447097108877633329 95573170085322831658224997)
          ·
            refine ⟨17919969390998030935917187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95573170085322831658224997 17919969390998030935917187)
            ·
              refine ⟨26879954086497046403875781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17919969390998030935917187 26879954086497046403875781)
              ·
                refine ⟨5039991391218196200726709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26879954086497046403875781 5039991391218196200726709)
                ·
                  refine ⟨472499192926705893818129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5039991391218196200726709 472499192926705893818129)
                  ·
                    rfl

theorem cell23_8281700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_8281700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281700 prefixEnd_8281700 := by exact prefixLift 8281700
  have htrace : WordTrace (prefixWord ++ tailWord_8281700) baseStart_8281700 baseEnd_8281700 := by
    simpa [prefixWord, tailWord_8281700, baseEnd_8281700] using wordTrace_append hprefix tailTrace_8281700
  have hstable : (prefixWord ++ tailWord_8281700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281700).length < 2 ^ (prefixWord ++ tailWord_8281700).sum := by decide
  have hdescent : baseEnd_8281700 < baseStart_8281700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281733 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_8281733 : Nat := 118140960795 + 8281733 * 2 ^ 59
def prefixEnd_8281733 : Nat := 4983230072969 + 3 ^ 40 * 8281733 * 2
def baseEnd_8281733 : Nat := 4252509681201951415250509

theorem tailTrace_8281733 : CollatzResearch.WordTrace tailWord_8281733 prefixEnd_8281733 4252509681201951415250509 := by
  unfold tailWord_8281733
  simp only [CollatzResearch.WordTrace]
  refine ⟨302059617705703223234785853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201373078470468815489857235 302059617705703223234785853)
  ·
    refine ⟨113272356639638708713044695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302059617705703223234785853 113272356639638708713044695)
    ·
      refine ⟨169908534959458063069567043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113272356639638708713044695 169908534959458063069567043)
      ·
        refine ⟨254862802439187094604350565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169908534959458063069567043 254862802439187094604350565)
        ·
          refine ⟨47786775457347580238315731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254862802439187094604350565 47786775457347580238315731)
          ·
            refine ⟨71680163186021370357473597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47786775457347580238315731 71680163186021370357473597)
            ·
              refine ⟨26880061194758013884052599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71680163186021370357473597 26880061194758013884052599)
              ·
                refine ⟨40320091792137020826078899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26880061194758013884052599 40320091792137020826078899)
                ·
                  refine ⟨60480137688205531239118349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40320091792137020826078899 60480137688205531239118349)
                  ·
                    refine ⟨22680051633077074214669381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60480137688205531239118349 22680051633077074214669381)
                    ·
                      refine ⟨4252509681201951415250509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22680051633077074214669381 4252509681201951415250509)
                      ·
                        rfl

theorem cell23_8281733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_8281733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281733 prefixEnd_8281733 := by exact prefixLift 8281733
  have htrace : WordTrace (prefixWord ++ tailWord_8281733) baseStart_8281733 baseEnd_8281733 := by
    simpa [prefixWord, tailWord_8281733, baseEnd_8281733] using wordTrace_append hprefix tailTrace_8281733
  have hstable : (prefixWord ++ tailWord_8281733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281733).length < 2 ^ (prefixWord ++ tailWord_8281733).sum := by decide
  have hdescent : baseEnd_8281733 < baseStart_8281733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281760 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_8281760 : Nat := 118140960795 + 8281760 * 2 ^ 59
def prefixEnd_8281760 : Nat := 4983230072969 + 3 ^ 40 * 8281760 * 2
def baseEnd_8281760 : Nat := 1417507848393207603204295

theorem tailTrace_8281760 : CollatzResearch.WordTrace tailWord_8281760 prefixEnd_8281760 1417507848393207603204295 := by
  unfold tailWord_8281760
  simp only [CollatzResearch.WordTrace]
  refine ⟨151030301238302703423009367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201373734984403604564012489 151030301238302703423009367)
  ·
    refine ⟨226545451857454055134514051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151030301238302703423009367 226545451857454055134514051)
    ·
      refine ⟨339818177786181082701771077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226545451857454055134514051 339818177786181082701771077)
      ·
        refine ⟨63715908334908953006582077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339818177786181082701771077 63715908334908953006582077)
        ·
          refine ⟨23893465625590857377468279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63715908334908953006582077 23893465625590857377468279)
          ·
            refine ⟨35840198438386286066202419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23893465625590857377468279 35840198438386286066202419)
            ·
              refine ⟨53760297657579429099303629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35840198438386286066202419 53760297657579429099303629)
              ·
                refine ⟨20160111621592285912238861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53760297657579429099303629 20160111621592285912238861)
                ·
                  refine ⟨7560041858097107217089573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20160111621592285912238861 7560041858097107217089573)
                  ·
                    refine ⟨1417507848393207603204295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560041858097107217089573 1417507848393207603204295)
                    ·
                      rfl

theorem cell23_8281760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_8281760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281760 prefixEnd_8281760 := by exact prefixLift 8281760
  have htrace : WordTrace (prefixWord ++ tailWord_8281760) baseStart_8281760 baseEnd_8281760 := by
    simpa [prefixWord, tailWord_8281760, baseEnd_8281760] using wordTrace_append hprefix tailTrace_8281760
  have hstable : (prefixWord ++ tailWord_8281760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281760).length < 2 ^ (prefixWord ++ tailWord_8281760).sum := by decide
  have hdescent : baseEnd_8281760 < baseStart_8281760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281817 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 3]
def baseStart_8281817 : Nat := 118140960795 + 8281817 * 2 ^ 59
def prefixEnd_8281817 : Nat := 4983230072969 + 3 ^ 40 * 8281817 * 2
def baseEnd_8281817 : Nat := 4252552813576929086600123

theorem tailTrace_8281817 : CollatzResearch.WordTrace tailWord_8281817 prefixEnd_8281817 4252552813576929086600123 := by
  unfold tailWord_8281817
  simp only [CollatzResearch.WordTrace]
  refine ⟨302062681437398905580843705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201375120958265937053895803 302062681437398905580843705)
  ·
    refine ⟨226547011078049179185632779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302062681437398905580843705 226547011078049179185632779)
    ·
      refine ⟨339820516617073768778449169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226547011078049179185632779 339820516617073768778449169)
      ·
        refine ⟨254865387462805326583836877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339820516617073768778449169 254865387462805326583836877)
        ·
          refine ⟨95574520298551997468938829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254865387462805326583836877 95574520298551997468938829)
          ·
            refine ⟨35840445111956999050852061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95574520298551997468938829 35840445111956999050852061)
            ·
              refine ⟨13440166916983874644069523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35840445111956999050852061 13440166916983874644069523)
              ·
                refine ⟨20160250375475811966104285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440166916983874644069523 20160250375475811966104285)
                ·
                  refine ⟨7560093890803429487289107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20160250375475811966104285 7560093890803429487289107)
                  ·
                    refine ⟨11340140836205144230933661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560093890803429487289107 11340140836205144230933661)
                    ·
                      refine ⟨4252552813576929086600123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340140836205144230933661 4252552813576929086600123)
                      ·
                        rfl

theorem cell23_8281817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_8281817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281817 prefixEnd_8281817 := by exact prefixLift 8281817
  have htrace : WordTrace (prefixWord ++ tailWord_8281817) baseStart_8281817 baseEnd_8281817 := by
    simpa [prefixWord, tailWord_8281817, baseEnd_8281817] using wordTrace_append hprefix tailTrace_8281817
  have hstable : (prefixWord ++ tailWord_8281817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281817).length < 2 ^ (prefixWord ++ tailWord_8281817).sum := by decide
  have hdescent : baseEnd_8281817 < baseStart_8281817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281833 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_8281833 : Nat := 118140960795 + 8281833 * 2 ^ 59
def prefixEnd_8281833 : Nat := 4983230072969 + 3 ^ 40 * 8281833 * 2
def baseEnd_8281833 : Nat := 1417520343089133674666683

theorem tailTrace_8281833 : CollatzResearch.WordTrace tailWord_8281833 prefixEnd_8281833 1417520343089133674666683 := by
  unfold tailWord_8281833
  simp only [CollatzResearch.WordTrace]
  refine ⟨302063265005340940313426153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201375510003560626875617435 302063265005340940313426153)
  ·
    refine ⟨226547448754005705235069615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302063265005340940313426153 226547448754005705235069615)
    ·
      refine ⟨339821173131008557852604423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226547448754005705235069615 339821173131008557852604423)
      ·
        refine ⟨509731759696512836778906635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339821173131008557852604423 509731759696512836778906635)
        ·
          refine ⟨764597639544769255168359953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509731759696512836778906635 764597639544769255168359953)
          ·
            refine ⟨573448229658576941376269965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764597639544769255168359953 573448229658576941376269965)
            ·
              refine ⟨215043086121966353016101237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573448229658576941376269965 215043086121966353016101237)
              ·
                refine ⟨20160289323934345595259491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215043086121966353016101237 20160289323934345595259491)
                ·
                  refine ⟨30240433985901518392889237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20160289323934345595259491 30240433985901518392889237)
                  ·
                    refine ⟨1417520343089133674666683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30240433985901518392889237 1417520343089133674666683)
                    ·
                      rfl

theorem cell23_8281833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_8281833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281833 prefixEnd_8281833 := by exact prefixLift 8281833
  have htrace : WordTrace (prefixWord ++ tailWord_8281833) baseStart_8281833 baseEnd_8281833 := by
    simpa [prefixWord, tailWord_8281833, baseEnd_8281833] using wordTrace_append hprefix tailTrace_8281833
  have hstable : (prefixWord ++ tailWord_8281833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281833).length < 2 ^ (prefixWord ++ tailWord_8281833).sum := by decide
  have hdescent : baseEnd_8281833 < baseStart_8281833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281837 : List Nat := [1, 5, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_8281837 : Nat := 118140960795 + 8281837 * 2 ^ 59
def prefixEnd_8281837 : Nat := 4983230072969 + 3 ^ 40 * 8281837 * 2
def baseEnd_8281837 : Nat := 1417521027730006336116677

theorem tailTrace_8281837 : CollatzResearch.WordTrace tailWord_8281837 prefixEnd_8281837 1417521027730006336116677 := by
  unfold tailWord_8281837
  simp only [CollatzResearch.WordTrace]
  refine ⟨302063410897326448996571765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201375607264884299331047843 302063410897326448996571765)
  ·
    refine ⟨28318444771624354593428603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302063410897326448996571765 28318444771624354593428603)
    ·
      refine ⟨42477667157436531890142905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28318444771624354593428603 42477667157436531890142905)
      ·
        refine ⟨31858250368077398917607179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42477667157436531890142905 31858250368077398917607179)
        ·
          refine ⟨47787375552116098376410769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31858250368077398917607179 47787375552116098376410769)
          ·
            refine ⟨35840531664087073782308077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47787375552116098376410769 35840531664087073782308077)
            ·
              refine ⟨13440199374032652668365529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35840531664087073782308077 13440199374032652668365529)
              ·
                refine ⟨10080149530524489501274147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13440199374032652668365529 10080149530524489501274147)
                ·
                  refine ⟨15120224295786734251911221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10080149530524489501274147 15120224295786734251911221)
                  ·
                    refine ⟨1417521027730006336116677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15120224295786734251911221 1417521027730006336116677)
                    ·
                      rfl

theorem cell23_8281837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_8281837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281837 prefixEnd_8281837 := by exact prefixLift 8281837
  have htrace : WordTrace (prefixWord ++ tailWord_8281837) baseStart_8281837 baseEnd_8281837 := by
    simpa [prefixWord, tailWord_8281837, baseEnd_8281837] using wordTrace_append hprefix tailTrace_8281837
  have hstable : (prefixWord ++ tailWord_8281837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281837).length < 2 ^ (prefixWord ++ tailWord_8281837).sum := by decide
  have hdescent : baseEnd_8281837 < baseStart_8281837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_8281840 : Nat := 118140960795 + 8281840 * 2 ^ 59
def prefixEnd_8281840 : Nat := 4983230072969 + 3 ^ 40 * 8281840 * 2
def baseEnd_8281840 : Nat := 4252564623631982496612517

theorem tailTrace_8281840 : CollatzResearch.WordTrace tailWord_8281840 prefixEnd_8281840 4252564623631982496612517 := by
  unfold tailWord_8281840
  simp only [CollatzResearch.WordTrace]
  refine ⟨151031760158157790254465487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201375680210877053672620649 151031760158157790254465487)
  ·
    refine ⟨226547640237236685381698231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151031760158157790254465487 226547640237236685381698231)
    ·
      refine ⟨339821460355855028072547347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226547640237236685381698231 339821460355855028072547347)
      ·
        refine ⟨509732190533782542108821021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339821460355855028072547347 509732190533782542108821021)
        ·
          refine ⟨191149571450168453290807883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509732190533782542108821021 191149571450168453290807883)
          ·
            refine ⟨286724357175252679936211825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191149571450168453290807883 286724357175252679936211825)
            ·
              refine ⟨215043267881439509952158869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286724357175252679936211825 215043267881439509952158869)
              ·
                refine ⟨10080153181942477029007447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215043267881439509952158869 10080153181942477029007447)
                ·
                  refine ⟨15120229772913715543511171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10080153181942477029007447 15120229772913715543511171)
                  ·
                    refine ⟨22680344659370573315266757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15120229772913715543511171 22680344659370573315266757)
                    ·
                      refine ⟨4252564623631982496612517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22680344659370573315266757 4252564623631982496612517)
                      ·
                        rfl

theorem cell23_8281840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_8281840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281840 prefixEnd_8281840 := by exact prefixLift 8281840
  have htrace : WordTrace (prefixWord ++ tailWord_8281840) baseStart_8281840 baseEnd_8281840 := by
    simpa [prefixWord, tailWord_8281840, baseEnd_8281840] using wordTrace_append hprefix tailTrace_8281840
  have hstable : (prefixWord ++ tailWord_8281840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281840).length < 2 ^ (prefixWord ++ tailWord_8281840).sum := by decide
  have hdescent : baseEnd_8281840 < baseStart_8281840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281843 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_8281843 : Nat := 118140960795 + 8281843 * 2 ^ 59
def prefixEnd_8281843 : Nat := 4983230072969 + 3 ^ 40 * 8281843 * 2
def baseEnd_8281843 : Nat := 4252566164073945984875003

theorem tailTrace_8281843 : CollatzResearch.WordTrace tailWord_8281843 prefixEnd_8281843 4252566164073945984875003 := by
  unfold tailWord_8281843
  simp only [CollatzResearch.WordTrace]
  refine ⟨302063629735304712021290183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201375753156869808014193455 302063629735304712021290183)
  ·
    refine ⟨453095444602957068031935275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302063629735304712021290183 453095444602957068031935275)
    ·
      refine ⟨679643166904435602047902913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453095444602957068031935275 679643166904435602047902913)
      ·
        refine ⟨509732375178326701535927185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679643166904435602047902913 509732375178326701535927185)
        ·
          refine ⟨382299281383745026151945389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509732375178326701535927185 382299281383745026151945389)
          ·
            refine ⟨143362230518904384806979521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382299281383745026151945389 143362230518904384806979521)
            ·
              refine ⟨107521672889178288605234641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143362230518904384806979521 107521672889178288605234641)
              ·
                refine ⟨80641254666883716453925981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107521672889178288605234641 80641254666883716453925981)
                ·
                  refine ⟨30240470500081393670222243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80641254666883716453925981 30240470500081393670222243)
                  ·
                    refine ⟨45360705750122090505333365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30240470500081393670222243 45360705750122090505333365)
                    ·
                      refine ⟨4252566164073945984875003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45360705750122090505333365 4252566164073945984875003)
                      ·
                        rfl

theorem cell23_8281843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_8281843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281843 prefixEnd_8281843 := by exact prefixLift 8281843
  have htrace : WordTrace (prefixWord ++ tailWord_8281843) baseStart_8281843 baseEnd_8281843 := by
    simpa [prefixWord, tailWord_8281843, baseEnd_8281843] using wordTrace_append hprefix tailTrace_8281843
  have hstable : (prefixWord ++ tailWord_8281843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281843).length < 2 ^ (prefixWord ++ tailWord_8281843).sum := by decide
  have hdescent : baseEnd_8281843 < baseStart_8281843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281853 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_8281853 : Nat := 118140960795 + 8281853 * 2 ^ 59
def prefixEnd_8281853 : Nat := 4983230072969 + 3 ^ 40 * 8281853 * 2
def baseEnd_8281853 : Nat := 4252571298880490945749957

theorem tailTrace_8281853 : CollatzResearch.WordTrace tailWord_8281853 prefixEnd_8281853 4252571298880490945749957 := by
  unfold tailWord_8281853
  simp only [CollatzResearch.WordTrace]
  refine ⟨302063994465268483729154213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201375996310178989152769475 302063994465268483729154213)
  ·
    refine ⟨56636998962237840699216415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302063994465268483729154213 56636998962237840699216415)
    ·
      refine ⟨84955498443356761048824623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56636998962237840699216415 84955498443356761048824623)
      ·
        refine ⟨127433247665035141573236935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84955498443356761048824623 127433247665035141573236935)
        ·
          refine ⟨191149871497552712359855403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127433247665035141573236935 191149871497552712359855403)
          ·
            refine ⟨286724807246329068539783105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191149871497552712359855403 286724807246329068539783105)
            ·
              refine ⟨215043605434746801404837329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286724807246329068539783105 215043605434746801404837329)
              ·
                refine ⟨161282704076060101053627997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215043605434746801404837329 161282704076060101053627997)
                ·
                  refine ⟨60481014028522537895110499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161282704076060101053627997 60481014028522537895110499)
                  ·
                    refine ⟨90721521042783806842665749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60481014028522537895110499 90721521042783806842665749)
                    ·
                      refine ⟨4252571298880490945749957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90721521042783806842665749 4252571298880490945749957)
                      ·
                        rfl

theorem cell23_8281853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_8281853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281853 prefixEnd_8281853 := by exact prefixLift 8281853
  have htrace : WordTrace (prefixWord ++ tailWord_8281853) baseStart_8281853 baseEnd_8281853 := by
    simpa [prefixWord, tailWord_8281853, baseEnd_8281853] using wordTrace_append hprefix tailTrace_8281853
  have hstable : (prefixWord ++ tailWord_8281853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281853).length < 2 ^ (prefixWord ++ tailWord_8281853).sum := by decide
  have hdescent : baseEnd_8281853 < baseStart_8281853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281862 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_8281862 : Nat := 118140960795 + 8281862 * 2 ^ 59
def prefixEnd_8281862 : Nat := 4983230072969 + 3 ^ 40 * 8281862 * 2
def baseEnd_8281862 : Nat := 1417525306735460470179139

theorem tailTrace_8281862 : CollatzResearch.WordTrace tailWord_8281862 prefixEnd_8281862 1417525306735460470179139 := by
  unfold tailWord_8281862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439510085069871195819745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201376215148157252177487893 9439510085069871195819745)
  ·
    refine ⟨7079632563802403396864809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9439510085069871195819745 7079632563802403396864809)
    ·
      refine ⟨5309724422851802547648607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7079632563802403396864809 5309724422851802547648607)
      ·
        refine ⟨7964586634277703821472911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309724422851802547648607 7964586634277703821472911)
        ·
          refine ⟨11946879951416555732209367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964586634277703821472911 11946879951416555732209367)
          ·
            refine ⟨17920319927124833598314051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946879951416555732209367 17920319927124833598314051)
            ·
              refine ⟨26880479890687250397471077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17920319927124833598314051 26880479890687250397471077)
              ·
                refine ⟨5040089979503859449525827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26880479890687250397471077 5040089979503859449525827)
                ·
                  refine ⟨7560134969255789174288741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040089979503859449525827 7560134969255789174288741)
                  ·
                    refine ⟨1417525306735460470179139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560134969255789174288741 1417525306735460470179139)
                    ·
                      rfl

theorem cell23_8281862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_8281862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281862 prefixEnd_8281862 := by exact prefixLift 8281862
  have htrace : WordTrace (prefixWord ++ tailWord_8281862) baseStart_8281862 baseEnd_8281862 := by
    simpa [prefixWord, tailWord_8281862, baseEnd_8281862] using wordTrace_append hprefix tailTrace_8281862
  have hstable : (prefixWord ++ tailWord_8281862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281862).length < 2 ^ (prefixWord ++ tailWord_8281862).sum := by decide
  have hdescent : baseEnd_8281862 < baseStart_8281862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281863 : List Nat := [1, 1, 4, 4, 13]
def baseStart_8281863 : Nat := 118140960795 + 8281863 * 2 ^ 59
def prefixEnd_8281863 : Nat := 4983230072969 + 3 ^ 40 * 8281863 * 2
def baseEnd_8281863 : Nat := 5833438180640652821159

theorem tailTrace_8281863 : CollatzResearch.WordTrace tailWord_8281863 prefixEnd_8281863 5833438180640652821159 := by
  unfold tailWord_8281863
  simp only [CollatzResearch.WordTrace]
  refine ⟨302064359195232255437018243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201376239463488170291345495 302064359195232255437018243)
  ·
    refine ⟨453096538792848383155527365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302064359195232255437018243 453096538792848383155527365)
    ·
      refine ⟨84955601023659071841661381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453096538792848383155527365 84955601023659071841661381)
      ·
        refine ⟨15929175191936075970311509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84955601023659071841661381 15929175191936075970311509)
        ·
          refine ⟨5833438180640652821159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15929175191936075970311509 5833438180640652821159)
          ·
            rfl

theorem cell23_8281863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 13].length) (baseStart_8281863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281863 prefixEnd_8281863 := by exact prefixLift 8281863
  have htrace : WordTrace (prefixWord ++ tailWord_8281863) baseStart_8281863 baseEnd_8281863 := by
    simpa [prefixWord, tailWord_8281863, baseEnd_8281863] using wordTrace_append hprefix tailTrace_8281863
  have hstable : (prefixWord ++ tailWord_8281863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281863).length < 2 ^ (prefixWord ++ tailWord_8281863).sum := by decide
  have hdescent : baseEnd_8281863 < baseStart_8281863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281903 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_8281903 : Nat := 118140960795 + 8281903 * 2 ^ 59
def prefixEnd_8281903 : Nat := 4983230072969 + 3 ^ 40 * 8281903 * 2
def baseEnd_8281903 : Nat := 4252596972913215750124727

theorem tailTrace_8281903 : CollatzResearch.WordTrace tailWord_8281903 prefixEnd_8281903 4252596972913215750124727 := by
  unfold tailWord_8281903
  simp only [CollatzResearch.WordTrace]
  refine ⟨302065818115087342268474363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201377212076724894845649575 302065818115087342268474363)
  ·
    refine ⟨453098727172631013402711545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302065818115087342268474363 453098727172631013402711545)
    ·
      refine ⟨339824045379473260052033659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453098727172631013402711545 339824045379473260052033659)
      ·
        refine ⟨509736068069209890078050489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339824045379473260052033659 509736068069209890078050489)
        ·
          refine ⟨382302051051907417558537867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509736068069209890078050489 382302051051907417558537867)
          ·
            refine ⟨573453076577861126337806801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382302051051907417558537867 573453076577861126337806801)
            ·
              refine ⟨430089807433395844753355101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573453076577861126337806801 430089807433395844753355101)
              ·
                refine ⟨161283677787523441782508163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430089807433395844753355101 161283677787523441782508163)
                ·
                  refine ⟨241925516681285162673762245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161283677787523441782508163 241925516681285162673762245)
                  ·
                    refine ⟨45361034377740968001330421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 241925516681285162673762245 45361034377740968001330421)
                    ·
                      refine ⟨4252596972913215750124727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45361034377740968001330421 4252596972913215750124727)
                      ·
                        rfl

theorem cell23_8281903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_8281903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281903 prefixEnd_8281903 := by exact prefixLift 8281903
  have htrace : WordTrace (prefixWord ++ tailWord_8281903) baseStart_8281903 baseEnd_8281903 := by
    simpa [prefixWord, tailWord_8281903, baseEnd_8281903] using wordTrace_append hprefix tailTrace_8281903
  have hstable : (prefixWord ++ tailWord_8281903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281903).length < 2 ^ (prefixWord ++ tailWord_8281903).sum := by decide
  have hdescent : baseEnd_8281903 < baseStart_8281903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281908 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_8281908 : Nat := 118140960795 + 8281908 * 2 ^ 59
def prefixEnd_8281908 : Nat := 4983230072969 + 3 ^ 40 * 8281908 * 2
def baseEnd_8281908 : Nat := 4252599540316488230562205

theorem tailTrace_8281908 : CollatzResearch.WordTrace tailWord_8281908 prefixEnd_8281908 4252599540316488230562205 := by
  unfold tailWord_8281908
  simp only [CollatzResearch.WordTrace]
  refine ⟨151033000240034614061203189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201377333653379485414937585 151033000240034614061203189)
  ·
    refine ⟨14159343772503245068237799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151033000240034614061203189 14159343772503245068237799)
    ·
      refine ⟨21239015658754867602356699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159343772503245068237799 21239015658754867602356699)
      ·
        refine ⟨31858523488132301403535049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21239015658754867602356699 31858523488132301403535049)
        ·
          refine ⟨23893892616099226052651287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31858523488132301403535049 23893892616099226052651287)
          ·
            refine ⟨35840838924148839078976931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23893892616099226052651287 35840838924148839078976931)
            ·
              refine ⟨53761258386223258618465397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35840838924148839078976931 53761258386223258618465397)
              ·
                refine ⟨5040117973708430495481131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53761258386223258618465397 5040117973708430495481131)
                ·
                  refine ⟨7560176960562645743221697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040117973708430495481131 7560176960562645743221697)
                  ·
                    refine ⟨5670132720421984307416273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560176960562645743221697 5670132720421984307416273)
                    ·
                      refine ⟨4252599540316488230562205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670132720421984307416273 4252599540316488230562205)
                      ·
                        rfl

theorem cell23_8281908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_8281908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281908 prefixEnd_8281908 := by exact prefixLift 8281908
  have htrace : WordTrace (prefixWord ++ tailWord_8281908) baseStart_8281908 baseEnd_8281908 := by
    simpa [prefixWord, tailWord_8281908, baseEnd_8281908] using wordTrace_append hprefix tailTrace_8281908
  have hstable : (prefixWord ++ tailWord_8281908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281908).length < 2 ^ (prefixWord ++ tailWord_8281908).sum := by decide
  have hdescent : baseEnd_8281908 < baseStart_8281908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281941 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_8281941 : Nat := 118140960795 + 8281941 * 2 ^ 59
def prefixEnd_8281941 : Nat := 4983230072969 + 3 ^ 40 * 8281941 * 2
def baseEnd_8281941 : Nat := 4252616485178086601449553

theorem tailTrace_8281941 : CollatzResearch.WordTrace tailWord_8281941 prefixEnd_8281941 4252616485178086601449553 := by
  unfold tailWord_8281941
  simp only [CollatzResearch.WordTrace]
  refine ⟨302067204088949674758357677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201378136059299783172238451 302067204088949674758357677)
  ·
    refine ⟨113275201533356128034384129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302067204088949674758357677 113275201533356128034384129)
    ·
      refine ⟨84956401150017096025788097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113275201533356128034384129 84956401150017096025788097)
      ·
        refine ⟨63717300862512822019341073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84956401150017096025788097 63717300862512822019341073)
        ·
          refine ⟨47787975646884616514505805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63717300862512822019341073 47787975646884616514505805)
          ·
            refine ⟨17920490867581731192939677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47787975646884616514505805 17920490867581731192939677)
            ·
              refine ⟨6720184075343149197352379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17920490867581731192939677 6720184075343149197352379)
              ·
                refine ⟨10080276113014723796028569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720184075343149197352379 10080276113014723796028569)
                ·
                  refine ⟨7560207084761042847021427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080276113014723796028569 7560207084761042847021427)
                  ·
                    refine ⟨11340310627141564270532141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560207084761042847021427 11340310627141564270532141)
                    ·
                      refine ⟨4252616485178086601449553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340310627141564270532141 4252616485178086601449553)
                      ·
                        rfl

theorem cell23_8281941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_8281941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281941 prefixEnd_8281941 := by exact prefixLift 8281941
  have htrace : WordTrace (prefixWord ++ tailWord_8281941) baseStart_8281941 baseEnd_8281941 := by
    simpa [prefixWord, tailWord_8281941, baseEnd_8281941] using wordTrace_append hprefix tailTrace_8281941
  have hstable : (prefixWord ++ tailWord_8281941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281941).length < 2 ^ (prefixWord ++ tailWord_8281941).sum := by decide
  have hdescent : baseEnd_8281941 < baseStart_8281941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281964 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_8281964 : Nat := 118140960795 + 8281964 * 2 ^ 59
def prefixEnd_8281964 : Nat := 4983230072969 + 3 ^ 40 * 8281964 * 2
def baseEnd_8281964 : Nat := 4252628295233140011461947

theorem tailTrace_8281964 : CollatzResearch.WordTrace tailWord_8281964 prefixEnd_8281964 4252628295233140011461947 := by
  unfold tailWord_8281964
  simp only [CollatzResearch.WordTrace]
  refine ⟨151034021483933174843222473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201378695311910899790963297 151034021483933174843222473)
  ·
    refine ⟨113275516112949881132416855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151034021483933174843222473 113275516112949881132416855)
    ·
      refine ⟨169913274169424821698625283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113275516112949881132416855 169913274169424821698625283)
      ·
        refine ⟨254869911254137232547937925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169913274169424821698625283 254869911254137232547937925)
        ·
          refine ⟨47788108360150731102738361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254869911254137232547937925 47788108360150731102738361)
          ·
            refine ⟨35841081270113048327053771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47788108360150731102738361 35841081270113048327053771)
            ·
              refine ⟨53761621905169572490580657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35841081270113048327053771 53761621905169572490580657)
              ·
                refine ⟨40321216428877179367935493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53761621905169572490580657 40321216428877179367935493)
                ·
                  refine ⟨7560228080414471131487905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40321216428877179367935493 7560228080414471131487905)
                  ·
                    refine ⟨5670171060310853348615929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560228080414471131487905 5670171060310853348615929)
                    ·
                      refine ⟨4252628295233140011461947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670171060310853348615929 4252628295233140011461947)
                      ·
                        rfl

theorem cell23_8281964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_8281964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281964 prefixEnd_8281964 := by exact prefixLift 8281964
  have htrace : WordTrace (prefixWord ++ tailWord_8281964) baseStart_8281964 baseEnd_8281964 := by
    simpa [prefixWord, tailWord_8281964, baseEnd_8281964] using wordTrace_append hprefix tailTrace_8281964
  have hstable : (prefixWord ++ tailWord_8281964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281964).length < 2 ^ (prefixWord ++ tailWord_8281964).sum := by decide
  have hdescent : baseEnd_8281964 < baseStart_8281964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8281987 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 7]
def baseStart_8281987 : Nat := 118140960795 + 8281987 * 2 ^ 59
def prefixEnd_8281987 : Nat := 4983230072969 + 3 ^ 40 * 8281987 * 2
def baseEnd_8281987 : Nat := 472515567254243713497149

theorem tailTrace_8281987 : CollatzResearch.WordTrace tailWord_8281987 prefixEnd_8281987 472515567254243713497149 := by
  unfold tailWord_8281987
  simp only [CollatzResearch.WordTrace]
  refine ⟨302068881846783024614532215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201379254564522016409688143 302068881846783024614532215)
  ·
    refine ⟨453103322770174536921798323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302068881846783024614532215 453103322770174536921798323)
    ·
      refine ⟨679654984155261805382697485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453103322770174536921798323 679654984155261805382697485)
      ·
        refine ⟨254870619058223177018511557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679654984155261805382697485 254870619058223177018511557)
        ·
          refine ⟨47788241073416845690970917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254870619058223177018511557 47788241073416845690970917)
          ·
            refine ⟨8960295201265658567057047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47788241073416845690970917 8960295201265658567057047)
            ·
              refine ⟨13440442801898487850585571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960295201265658567057047 13440442801898487850585571)
              ·
                refine ⟨20160664202847731775878357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440442801898487850585571 20160664202847731775878357)
                ·
                  refine ⟨472515567254243713497149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20160664202847731775878357 472515567254243713497149)
                  ·
                    rfl

theorem cell23_8281987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 7].length) (baseStart_8281987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8281987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8281987 prefixEnd_8281987 := by exact prefixLift 8281987
  have htrace : WordTrace (prefixWord ++ tailWord_8281987) baseStart_8281987 baseEnd_8281987 := by
    simpa [prefixWord, tailWord_8281987, baseEnd_8281987] using wordTrace_append hprefix tailTrace_8281987
  have hstable : (prefixWord ++ tailWord_8281987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8281987).length < 2 ^ (prefixWord ++ tailWord_8281987).sum := by decide
  have hdescent : baseEnd_8281987 < baseStart_8281987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8281987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282040 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_8282040 : Nat := 118140960795 + 8282040 * 2 ^ 59
def prefixEnd_8282040 : Nat := 4983230072969 + 3 ^ 40 * 8282040 * 2
def baseEnd_8282040 : Nat := 4252667319762881714111597

theorem tailTrace_8282040 : CollatzResearch.WordTrace tailWord_8282040 prefixEnd_8282040 4252667319762881714111597 := by
  unfold tailWord_8282040
  simp only [CollatzResearch.WordTrace]
  refine ⟨151035407457795507333105787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201380543277060676444141049 151035407457795507333105787)
  ·
    refine ⟨226553111186693260999658681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151035407457795507333105787 226553111186693260999658681)
    ·
      refine ⟨169914833390019945749744011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226553111186693260999658681 169914833390019945749744011)
      ·
        refine ⟨254872250085029918624616017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169914833390019945749744011 254872250085029918624616017)
        ·
          refine ⟨191154187563772438968462013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254872250085029918624616017 191154187563772438968462013)
          ·
            refine ⟨71682820336414664613173255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191154187563772438968462013 71682820336414664613173255)
            ·
              refine ⟨107524230504621996919759883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71682820336414664613173255 107524230504621996919759883)
              ·
                refine ⟨161286345756932995379639825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107524230504621996919759883 161286345756932995379639825)
                ·
                  refine ⟨120964759317699746534729869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161286345756932995379639825 120964759317699746534729869)
                  ·
                    refine ⟨45361784744137404950523701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120964759317699746534729869 45361784744137404950523701)
                    ·
                      refine ⟨4252667319762881714111597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45361784744137404950523701 4252667319762881714111597)
                      ·
                        rfl

theorem cell23_8282040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_8282040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282040 prefixEnd_8282040 := by exact prefixLift 8282040
  have htrace : WordTrace (prefixWord ++ tailWord_8282040) baseStart_8282040 baseEnd_8282040 := by
    simpa [prefixWord, tailWord_8282040, baseEnd_8282040] using wordTrace_append hprefix tailTrace_8282040
  have hstable : (prefixWord ++ tailWord_8282040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282040).length < 2 ^ (prefixWord ++ tailWord_8282040).sum := by decide
  have hdescent : baseEnd_8282040 < baseStart_8282040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282047 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 3, 4]
def baseStart_8282047 : Nat := 118140960795 + 8282047 * 2 ^ 59
def prefixEnd_8282047 : Nat := 4983230072969 + 3 ^ 40 * 8282047 * 2
def baseEnd_8282047 : Nat := 1417556971375821062241355

theorem tailTrace_8282047 : CollatzResearch.WordTrace tailWord_8282047 prefixEnd_8282047 1417556971375821062241355 := by
  unfold tailWord_8282047
  simp only [CollatzResearch.WordTrace]
  refine ⟨302071070226565654861716395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201380713484377103241144263 302071070226565654861716395)
  ·
    refine ⟨453106605339848482292574593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302071070226565654861716395 453106605339848482292574593)
    ·
      refine ⟨339829954004886361719430945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453106605339848482292574593 339829954004886361719430945)
      ·
        refine ⟨254872465503664771289573209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339829954004886361719430945 254872465503664771289573209)
        ·
          refine ⟨191154349127748578467179907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254872465503664771289573209 191154349127748578467179907)
          ·
            refine ⟨286731523691622867700769861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191154349127748578467179907 286731523691622867700769861)
            ·
              refine ⟨53762160692179287693894349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286731523691622867700769861 53762160692179287693894349)
              ·
                refine ⟨20160810259567232885210381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53762160692179287693894349 20160810259567232885210381)
                ·
                  refine ⟨7560303847337712331953893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20160810259567232885210381 7560303847337712331953893)
                  ·
                    refine ⟨1417556971375821062241355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560303847337712331953893 1417556971375821062241355)
                    ·
                      rfl

theorem cell23_8282047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_8282047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282047 prefixEnd_8282047 := by exact prefixLift 8282047
  have htrace : WordTrace (prefixWord ++ tailWord_8282047) baseStart_8282047 baseEnd_8282047 := by
    simpa [prefixWord, tailWord_8282047, baseEnd_8282047] using wordTrace_append hprefix tailTrace_8282047
  have hstable : (prefixWord ++ tailWord_8282047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282047).length < 2 ^ (prefixWord ++ tailWord_8282047).sum := by decide
  have hdescent : baseEnd_8282047 < baseStart_8282047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282074 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_8282074 : Nat := 118140960795 + 8282074 * 2 ^ 59
def prefixEnd_8282074 : Nat := 4983230072969 + 3 ^ 40 * 8282074 * 2
def baseEnd_8282074 : Nat := 4252684778105134581086441

theorem tailTrace_8282074 : CollatzResearch.WordTrace tailWord_8282074 prefixEnd_8282074 4252684778105134581086441 := by
  unfold tailWord_8282074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75518013749366959618237319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201381369998311892315299517 75518013749366959618237319)
  ·
    refine ⟨113277020624050439427355979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75518013749366959618237319 113277020624050439427355979)
    ·
      refine ⟨169915530936075659141033969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113277020624050439427355979 169915530936075659141033969)
      ·
        refine ⟨127436648202056744355775477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169915530936075659141033969 127436648202056744355775477)
        ·
          refine ⟨11947185768942819783353951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127436648202056744355775477 11947185768942819783353951)
          ·
            refine ⟨17920778653414229675030927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947185768942819783353951 17920778653414229675030927)
            ·
              refine ⟨26881167980121344512546391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17920778653414229675030927 26881167980121344512546391)
              ·
                refine ⟨40321751970182016768819587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26881167980121344512546391 40321751970182016768819587)
                ·
                  refine ⟨60482627955273025153229381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40321751970182016768819587 60482627955273025153229381)
                  ·
                    refine ⟨11340492741613692216230509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60482627955273025153229381 11340492741613692216230509)
                    ·
                      refine ⟨4252684778105134581086441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340492741613692216230509 4252684778105134581086441)
                      ·
                        rfl

theorem cell23_8282074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_8282074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282074 prefixEnd_8282074 := by exact prefixLift 8282074
  have htrace : WordTrace (prefixWord ++ tailWord_8282074) baseStart_8282074 baseEnd_8282074 := by
    simpa [prefixWord, tailWord_8282074, baseEnd_8282074] using wordTrace_append hprefix tailTrace_8282074
  have hstable : (prefixWord ++ tailWord_8282074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282074).length < 2 ^ (prefixWord ++ tailWord_8282074).sum := by decide
  have hdescent : baseEnd_8282074 < baseStart_8282074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282080 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_8282080 : Nat := 118140960795 + 8282080 * 2 ^ 59
def prefixEnd_8282080 : Nat := 4983230072969 + 3 ^ 40 * 8282080 * 2
def baseEnd_8282080 : Nat := 4252687858989061557611413

theorem tailTrace_8282080 : CollatzResearch.WordTrace tailWord_8282080 prefixEnd_8282080 4252687858989061557611413 := by
  unfold tailWord_8282080
  simp only [CollatzResearch.WordTrace]
  refine ⟨151036136917723050748833847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201381515890297400998445129 151036136917723050748833847)
  ·
    refine ⟨226554205376584576123250771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151036136917723050748833847 226554205376584576123250771)
    ·
      refine ⟨339831308064876864184876157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226554205376584576123250771 339831308064876864184876157)
      ·
        refine ⟨127436740524328824069328559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339831308064876864184876157 127436740524328824069328559)
        ·
          refine ⟨191155110786493236103992839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127436740524328824069328559 191155110786493236103992839)
          ·
            refine ⟨286732666179739854155989259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191155110786493236103992839 286732666179739854155989259)
            ·
              refine ⟨430098999269609781233983889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286732666179739854155989259 430098999269609781233983889)
              ·
                refine ⟨322574249452207335925487917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430098999269609781233983889 322574249452207335925487917)
                ·
                  refine ⟨120965343544577750972057969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322574249452207335925487917 120965343544577750972057969)
                  ·
                    refine ⟨90724007658433313229043477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120965343544577750972057969 90724007658433313229043477)
                    ·
                      refine ⟨4252687858989061557611413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90724007658433313229043477 4252687858989061557611413)
                      ·
                        rfl

theorem cell23_8282080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_8282080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282080 prefixEnd_8282080 := by exact prefixLift 8282080
  have htrace : WordTrace (prefixWord ++ tailWord_8282080) baseStart_8282080 baseEnd_8282080 := by
    simpa [prefixWord, tailWord_8282080, baseEnd_8282080] using wordTrace_append hprefix tailTrace_8282080
  have hstable : (prefixWord ++ tailWord_8282080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282080).length < 2 ^ (prefixWord ++ tailWord_8282080).sum := by decide
  have hdescent : baseEnd_8282080 < baseStart_8282080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282094 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 6]
def baseStart_8282094 : Nat := 118140960795 + 8282094 * 2 ^ 59
def prefixEnd_8282094 : Nat := 4983230072969 + 3 ^ 40 * 8282094 * 2
def baseEnd_8282094 : Nat := 472521671968691611426261

theorem tailTrace_8282094 : CollatzResearch.WordTrace tailWord_8282094 prefixEnd_8282094 472521671968691611426261 := by
  unfold tailWord_8282094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759098057174422736084667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201381856304930254592451557 37759098057174422736084667)
  ·
    refine ⟨56638647085761634104127001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37759098057174422736084667 56638647085761634104127001)
    ·
      refine ⟨42478985314321225578095251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56638647085761634104127001 42478985314321225578095251)
      ·
        refine ⟨63718477971481838367142877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42478985314321225578095251 63718477971481838367142877)
        ·
          refine ⟨23894429239305689387678579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63718477971481838367142877 23894429239305689387678579)
          ·
            refine ⟨35841643858958534081517869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23894429239305689387678579 35841643858958534081517869)
            ·
              refine ⟨13440616447109450280569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35841643858958534081517869 13440616447109450280569201)
              ·
                refine ⟨10080462335332087710426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13440616447109450280569201 10080462335332087710426901)
                ·
                  refine ⟨472521671968691611426261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10080462335332087710426901 472521671968691611426261)
                  ·
                    rfl

theorem cell23_8282094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_8282094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282094 prefixEnd_8282094 := by exact prefixLift 8282094
  have htrace : WordTrace (prefixWord ++ tailWord_8282094) baseStart_8282094 baseEnd_8282094 := by
    simpa [prefixWord, tailWord_8282094, baseEnd_8282094] using wordTrace_append hprefix tailTrace_8282094
  have hstable : (prefixWord ++ tailWord_8282094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282094).length < 2 ^ (prefixWord ++ tailWord_8282094).sum := by decide
  have hdescent : baseEnd_8282094 < baseStart_8282094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282104 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_8282104 : Nat := 118140960795 + 8282104 * 2 ^ 59
def prefixEnd_8282104 : Nat := 4983230072969 + 3 ^ 40 * 8282104 * 2
def baseEnd_8282104 : Nat := 4252700182524769463711303

theorem tailTrace_8282104 : CollatzResearch.WordTrace tailWord_8282104 prefixEnd_8282104 4252700182524769463711303 := by
  unfold tailWord_8282104
  simp only [CollatzResearch.WordTrace]
  refine ⟨151036574593679576798270683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201382099458239435731027577 151036574593679576798270683)
  ·
    refine ⟨226554861890519365197406025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151036574593679576798270683 226554861890519365197406025)
    ·
      refine ⟨169916146417889523898054519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226554861890519365197406025 169916146417889523898054519)
      ·
        refine ⟨254874219626834285847081779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169916146417889523898054519 254874219626834285847081779)
        ·
          refine ⟨382311329440251428770622669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254874219626834285847081779 382311329440251428770622669)
          ·
            refine ⟨143366748540094285788983501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382311329440251428770622669 143366748540094285788983501)
            ·
              refine ⟨53762530702535357170868813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143366748540094285788983501 53762530702535357170868813)
              ·
                refine ⟨20160949013450758939075805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53762530702535357170868813 20160949013450758939075805)
                ·
                  refine ⟨7560355880044034602153427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20160949013450758939075805 7560355880044034602153427)
                  ·
                    refine ⟨11340533820066051903230141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560355880044034602153427 11340533820066051903230141)
                    ·
                      refine ⟨4252700182524769463711303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340533820066051903230141 4252700182524769463711303)
                      ·
                        rfl

theorem cell23_8282104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_8282104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282104 prefixEnd_8282104 := by exact prefixLift 8282104
  have htrace : WordTrace (prefixWord ++ tailWord_8282104) baseStart_8282104 baseEnd_8282104 := by
    simpa [prefixWord, tailWord_8282104, baseEnd_8282104] using wordTrace_append hprefix tailTrace_8282104
  have hstable : (prefixWord ++ tailWord_8282104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282104).length < 2 ^ (prefixWord ++ tailWord_8282104).sum := by decide
  have hdescent : baseEnd_8282104 < baseStart_8282104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282124 : List Nat := [2, 2, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_8282124 : Nat := 118140960795 + 8282124 * 2 ^ 59
def prefixEnd_8282124 : Nat := 4983230072969 + 3 ^ 40 * 8282124 * 2
def baseEnd_8282124 : Nat := 1417570150712619795153737

theorem tailTrace_8282124 : CollatzResearch.WordTrace tailWord_8282124 prefixEnd_8282124 1417570150712619795153737 := by
  unfold tailWord_8282124
  simp only [CollatzResearch.WordTrace]
  refine ⟨151036939323643348506134713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201382585764857798008179617 151036939323643348506134713)
  ·
    refine ⟨113277704492732511379601035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151036939323643348506134713 113277704492732511379601035)
    ·
      refine ⟨169916556739098767069401553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113277704492732511379601035 169916556739098767069401553)
      ·
        refine ⟨127437417554324075302051165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169916556739098767069401553 127437417554324075302051165)
        ·
          refine ⟨47789031582871528238269187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127437417554324075302051165 47789031582871528238269187)
          ·
            refine ⟨71683547374307292357403781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47789031582871528238269187 71683547374307292357403781)
            ·
              refine ⟨13440665132682617317013209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71683547374307292357403781 13440665132682617317013209)
              ·
                refine ⟨10080498849511962987759907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13440665132682617317013209 10080498849511962987759907)
                ·
                  refine ⟨15120748274267944481639861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10080498849511962987759907 15120748274267944481639861)
                  ·
                    refine ⟨1417570150712619795153737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15120748274267944481639861 1417570150712619795153737)
                    ·
                      rfl

theorem cell23_8282124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_8282124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282124 prefixEnd_8282124 := by exact prefixLift 8282124
  have htrace : WordTrace (prefixWord ++ tailWord_8282124) baseStart_8282124 baseEnd_8282124 := by
    simpa [prefixWord, tailWord_8282124, baseEnd_8282124] using wordTrace_append hprefix tailTrace_8282124
  have hstable : (prefixWord ++ tailWord_8282124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282124).length < 2 ^ (prefixWord ++ tailWord_8282124).sum := by decide
  have hdescent : baseEnd_8282124 < baseStart_8282124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282132 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_8282132 : Nat := 118140960795 + 8282132 * 2 ^ 59
def prefixEnd_8282132 : Nat := 4983230072969 + 3 ^ 40 * 8282132 * 2
def baseEnd_8282132 : Nat := 1417571519994365118053725

theorem tailTrace_8282132 : CollatzResearch.WordTrace tailWord_8282132 prefixEnd_8282132 1417571519994365118053725 := by
  unfold tailWord_8282132
  simp only [CollatzResearch.WordTrace]
  refine ⟨151037085215628857189280325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201382780287505142919040433 151037085215628857189280325)
  ·
    refine ⟨28319453477930410722990061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151037085215628857189280325 28319453477930410722990061)
    ·
      refine ⟨10619795054223904021121273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28319453477930410722990061 10619795054223904021121273)
      ·
        refine ⟨7964846290667928015840955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10619795054223904021121273 7964846290667928015840955)
        ·
          refine ⟨11947269436001892023761433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964846290667928015840955 11947269436001892023761433)
          ·
            refine ⟨8960452077001419017821075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11947269436001892023761433 8960452077001419017821075)
            ·
              refine ⟨13440678115502128526731613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960452077001419017821075 13440678115502128526731613)
              ·
                refine ⟨5040254293313298197524355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13440678115502128526731613 5040254293313298197524355)
                ·
                  refine ⟨7560381439969947296286533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040254293313298197524355 7560381439969947296286533)
                  ·
                    refine ⟨1417571519994365118053725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560381439969947296286533 1417571519994365118053725)
                    ·
                      rfl

theorem cell23_8282132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_8282132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282132 prefixEnd_8282132 := by exact prefixLift 8282132
  have htrace : WordTrace (prefixWord ++ tailWord_8282132) baseStart_8282132 baseEnd_8282132 := by
    simpa [prefixWord, tailWord_8282132, baseEnd_8282132] using wordTrace_append hprefix tailTrace_8282132
  have hstable : (prefixWord ++ tailWord_8282132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282132).length < 2 ^ (prefixWord ++ tailWord_8282132).sum := by decide
  have hdescent : baseEnd_8282132 < baseStart_8282132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282138 : List Nat := [3, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3]
def baseStart_8282138 : Nat := 118140960795 + 8282138 * 2 ^ 59
def prefixEnd_8282138 : Nat := 4983230072969 + 3 ^ 40 * 8282138 * 2
def baseEnd_8282138 : Nat := 4252717640867022330686147

theorem tailTrace_8282138 : CollatzResearch.WordTrace tailWord_8282138 prefixEnd_8282138 4252717640867022330686147 := by
  unfold tailWord_8282138
  simp only [CollatzResearch.WordTrace]
  refine ⟨75518597317308994350819767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201382926179490651602186045 75518597317308994350819767)
  ·
    refine ⟨113277895975963491526229651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75518597317308994350819767 113277895975963491526229651)
    ·
      refine ⟨169916843963945237289344477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113277895975963491526229651 169916843963945237289344477)
      ·
        refine ⟨63718816486479463983504179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169916843963945237289344477 63718816486479463983504179)
        ·
          refine ⟨95578224729719195975256269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63718816486479463983504179 95578224729719195975256269)
          ·
            refine ⟨35841834273644698490721101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95578224729719195975256269 35841834273644698490721101)
            ·
              refine ⟨13440687852616761934020413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35841834273644698490721101 13440687852616761934020413)
              ·
                refine ⟨5040257944731285725257655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13440687852616761934020413 5040257944731285725257655)
                ·
                  refine ⟨7560386917096928587886483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040257944731285725257655 7560386917096928587886483)
                  ·
                    refine ⟨11340580375645392881829725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560386917096928587886483 11340580375645392881829725)
                    ·
                      refine ⟨4252717640867022330686147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340580375645392881829725 4252717640867022330686147)
                      ·
                        rfl

theorem cell23_8282138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_8282138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282138 prefixEnd_8282138 := by exact prefixLift 8282138
  have htrace : WordTrace (prefixWord ++ tailWord_8282138) baseStart_8282138 baseEnd_8282138 := by
    simpa [prefixWord, tailWord_8282138, baseEnd_8282138] using wordTrace_append hprefix tailTrace_8282138
  have hstable : (prefixWord ++ tailWord_8282138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282138).length < 2 ^ (prefixWord ++ tailWord_8282138).sum := by decide
  have hdescent : baseEnd_8282138 < baseStart_8282138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282148 : List Nat := [2, 3, 1, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_8282148 : Nat := 118140960795 + 8282148 * 2 ^ 59
def prefixEnd_8282148 : Nat := 4983230072969 + 3 ^ 40 * 8282148 * 2
def baseEnd_8282148 : Nat := 4252722775673567291561101

theorem tailTrace_8282148 : CollatzResearch.WordTrace tailWord_8282148 prefixEnd_8282148 4252722775673567291561101 := by
  unfold tailWord_8282148
  simp only [CollatzResearch.WordTrace]
  refine ⟨151037376999599874555571549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201383169332799832740762065 151037376999599874555571549)
  ·
    refine ⟨56639016374849952958339331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151037376999599874555571549 56639016374849952958339331)
    ·
      refine ⟨84958524562274929437508997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56639016374849952958339331 84958524562274929437508997)
      ·
        refine ⟨15929723355426549269532937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84958524562274929437508997 15929723355426549269532937)
        ·
          refine ⟨11947292516569911952149703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15929723355426549269532937 11947292516569911952149703)
          ·
            refine ⟨17920938774854867928224555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947292516569911952149703 17920938774854867928224555)
            ·
              refine ⟨26881408162282301892336833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17920938774854867928224555 26881408162282301892336833)
              ·
                refine ⟨20161056121711726419252625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26881408162282301892336833 20161056121711726419252625)
                ·
                  refine ⟨15120792091283794814439469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20161056121711726419252625 15120792091283794814439469)
                  ·
                    refine ⟨5670297034231423055414801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15120792091283794814439469 5670297034231423055414801)
                    ·
                      refine ⟨4252722775673567291561101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670297034231423055414801 4252722775673567291561101)
                      ·
                        rfl

theorem cell23_8282148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_8282148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282148 prefixEnd_8282148 := by exact prefixLift 8282148
  have htrace : WordTrace (prefixWord ++ tailWord_8282148) baseStart_8282148 baseEnd_8282148 := by
    simpa [prefixWord, tailWord_8282148, baseEnd_8282148] using wordTrace_append hprefix tailTrace_8282148
  have hstable : (prefixWord ++ tailWord_8282148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282148).length < 2 ^ (prefixWord ++ tailWord_8282148).sum := by decide
  have hdescent : baseEnd_8282148 < baseStart_8282148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282198 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_8282198 : Nat := 118140960795 + 8282198 * 2 ^ 59
def prefixEnd_8282198 : Nat := 4983230072969 + 3 ^ 40 * 8282198 * 2
def baseEnd_8282198 : Nat := 4252748449706292095935871

theorem tailTrace_8282198 : CollatzResearch.WordTrace tailWord_8282198 prefixEnd_8282198 4252748449706292095935871 := by
  unfold tailWord_8282198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879786103063662978153953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201384385099345738433642165 18879786103063662978153953)
  ·
    refine ⟨14159839577297747233615465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18879786103063662978153953 14159839577297747233615465)
    ·
      refine ⟨10619879682973310425211599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14159839577297747233615465 10619879682973310425211599)
      ·
        refine ⟨15929819524459965637817399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619879682973310425211599 15929819524459965637817399)
        ·
          refine ⟨23894729286689948456726099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15929819524459965637817399 23894729286689948456726099)
          ·
            refine ⟨35842093930034922685089149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23894729286689948456726099 35842093930034922685089149)
            ·
              refine ⟨13440785223763096006908431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35842093930034922685089149 13440785223763096006908431)
              ·
                refine ⟨20161177835644644010362647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440785223763096006908431 20161177835644644010362647)
                ·
                  refine ⟨30241766753466966015543971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20161177835644644010362647 30241766753466966015543971)
                  ·
                    refine ⟨45362650130200449023315957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30241766753466966015543971 45362650130200449023315957)
                    ·
                      refine ⟨4252748449706292095935871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45362650130200449023315957 4252748449706292095935871)
                      ·
                        rfl

theorem cell23_8282198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_8282198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282198 prefixEnd_8282198 := by exact prefixLift 8282198
  have htrace : WordTrace (prefixWord ++ tailWord_8282198) baseStart_8282198 baseEnd_8282198 := by
    simpa [prefixWord, tailWord_8282198, baseEnd_8282198] using wordTrace_append hprefix tailTrace_8282198
  have hstable : (prefixWord ++ tailWord_8282198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282198).length < 2 ^ (prefixWord ++ tailWord_8282198).sum := by decide
  have hdescent : baseEnd_8282198 < baseStart_8282198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282206 : List Nat := [4, 4, 1, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_8282206 : Nat := 118140960795 + 8282206 * 2 ^ 59
def prefixEnd_8282206 : Nat := 4983230072969 + 3 ^ 40 * 8282206 * 2
def baseEnd_8282206 : Nat := 4252752557551528064635835

theorem tailTrace_8282206 : CollatzResearch.WordTrace tailWord_8282206 prefixEnd_8282206 4252752557551528064635835 := by
  unfold tailWord_8282206
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759608679123703127094309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201384579621993083344502981 37759608679123703127094309)
  ·
    refine ⟨7079926627335694336330183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37759608679123703127094309 7079926627335694336330183)
    ·
      refine ⟨10619889941003541504495275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079926627335694336330183 10619889941003541504495275)
      ·
        refine ⟨15929834911505312256742913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10619889941003541504495275 15929834911505312256742913)
        ·
          refine ⟨11947376183628984192557185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15929834911505312256742913 11947376183628984192557185)
          ·
            refine ⟨8960532137721738144417889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11947376183628984192557185 8960532137721738144417889)
            ·
              refine ⟨6720399103291303608313417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8960532137721738144417889 6720399103291303608313417)
              ·
                refine ⟨5040299327468477706235063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720399103291303608313417 5040299327468477706235063)
                ·
                  refine ⟨7560448991202716559352595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040299327468477706235063 7560448991202716559352595)
                  ·
                    refine ⟨11340673486804074839028893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560448991202716559352595 11340673486804074839028893)
                    ·
                      refine ⟨4252752557551528064635835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340673486804074839028893 4252752557551528064635835)
                      ·
                        rfl

theorem cell23_8282206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_8282206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282206 prefixEnd_8282206 := by exact prefixLift 8282206
  have htrace : WordTrace (prefixWord ++ tailWord_8282206) baseStart_8282206 baseEnd_8282206 := by
    simpa [prefixWord, tailWord_8282206, baseEnd_8282206] using wordTrace_append hprefix tailTrace_8282206
  have hstable : (prefixWord ++ tailWord_8282206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282206).length < 2 ^ (prefixWord ++ tailWord_8282206).sum := by decide
  have hdescent : baseEnd_8282206 < baseStart_8282206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282211 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 3]
def baseStart_8282211 : Nat := 118140960795 + 8282211 * 2 ^ 59
def prefixEnd_8282211 : Nat := 4983230072969 + 3 ^ 40 * 8282211 * 2
def baseEnd_8282211 : Nat := 4252755124954800545073311

theorem tailTrace_8282211 : CollatzResearch.WordTrace tailWord_8282211 prefixEnd_8282211 4252755124954800545073311 := by
  unfold tailWord_8282211
  simp only [CollatzResearch.WordTrace]
  refine ⟨302077051797971510870686487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201384701198647673913790991 302077051797971510870686487)
  ·
    refine ⟨453115577696957266306029731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302077051797971510870686487 453115577696957266306029731)
    ·
      refine ⟨679673366545435899459044597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453115577696957266306029731 679673366545435899459044597)
      ·
        refine ⟨63719378113634615574285431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 679673366545435899459044597 63719378113634615574285431)
        ·
          refine ⟨95579067170451923361428147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63719378113634615574285431 95579067170451923361428147)
          ·
            refine ⟨143368600755677885042142221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95579067170451923361428147 143368600755677885042142221)
            ·
              refine ⟨53763225283379206890803333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143368600755677885042142221 53763225283379206890803333)
              ·
                refine ⟨10080604740633601292025625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53763225283379206890803333 10080604740633601292025625)
                ·
                  refine ⟨7560453555475200969019219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10080604740633601292025625 7560453555475200969019219)
                  ·
                    refine ⟨11340680333212801453528829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7560453555475200969019219 11340680333212801453528829)
                    ·
                      refine ⟨4252755124954800545073311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11340680333212801453528829 4252755124954800545073311)
                      ·
                        rfl

theorem cell23_8282211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_8282211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282211 prefixEnd_8282211 := by exact prefixLift 8282211
  have htrace : WordTrace (prefixWord ++ tailWord_8282211) baseStart_8282211 baseEnd_8282211 := by
    simpa [prefixWord, tailWord_8282211, baseEnd_8282211] using wordTrace_append hprefix tailTrace_8282211
  have hstable : (prefixWord ++ tailWord_8282211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282211).length < 2 ^ (prefixWord ++ tailWord_8282211).sum := by decide
  have hdescent : baseEnd_8282211 < baseStart_8282211 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282217 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_8282217 : Nat := 118140960795 + 8282217 * 2 ^ 59
def prefixEnd_8282217 : Nat := 4983230072969 + 3 ^ 40 * 8282217 * 2
def baseEnd_8282217 : Nat := 4252758205838727521598283

theorem tailTrace_8282217 : CollatzResearch.WordTrace tailWord_8282217 prefixEnd_8282217 4252758205838727521598283 := by
  unfold tailWord_8282217
  simp only [CollatzResearch.WordTrace]
  refine ⟨302077270635949773895404905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201384847090633182596936603 302077270635949773895404905)
  ·
    refine ⟨226557952976962330421553679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302077270635949773895404905 226557952976962330421553679)
    ·
      refine ⟨339836929465443495632330519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226557952976962330421553679 339836929465443495632330519)
      ·
        refine ⟨509755394198165243448495779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339836929465443495632330519 509755394198165243448495779)
        ·
          refine ⟨764633091297247865172743669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509755394198165243448495779 764633091297247865172743669)
          ·
            refine ⟨71684352309116987359944719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 764633091297247865172743669 71684352309116987359944719)
            ·
              refine ⟨107526528463675481039917079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71684352309116987359944719 107526528463675481039917079)
              ·
                refine ⟨161289792695513221559875619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107526528463675481039917079 161289792695513221559875619)
                ·
                  refine ⟨241934689043269832339813429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161289792695513221559875619 241934689043269832339813429)
                  ·
                    refine ⟨22681377097806546781857509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 241934689043269832339813429 22681377097806546781857509)
                    ·
                      refine ⟨4252758205838727521598283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22681377097806546781857509 4252758205838727521598283)
                      ·
                        rfl

theorem cell23_8282217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_8282217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282217 prefixEnd_8282217 := by exact prefixLift 8282217
  have htrace : WordTrace (prefixWord ++ tailWord_8282217) baseStart_8282217 baseEnd_8282217 := by
    simpa [prefixWord, tailWord_8282217, baseEnd_8282217] using wordTrace_append hprefix tailTrace_8282217
  have hstable : (prefixWord ++ tailWord_8282217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282217).length < 2 ^ (prefixWord ++ tailWord_8282217).sum := by decide
  have hdescent : baseEnd_8282217 < baseStart_8282217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282221 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_8282221 : Nat := 118140960795 + 8282221 * 2 ^ 59
def prefixEnd_8282221 : Nat := 4983230072969 + 3 ^ 40 * 8282221 * 2
def baseEnd_8282221 : Nat := 4252760259761345505948265

theorem tailTrace_8282221 : CollatzResearch.WordTrace tailWord_8282221 prefixEnd_8282221 4252760259761345505948265 := by
  unfold tailWord_8282221
  simp only [CollatzResearch.WordTrace]
  refine ⟨302077416527935282578550517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201384944351956855052367011 302077416527935282578550517)
  ·
    refine ⟨28319757799493932741739111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302077416527935282578550517 28319757799493932741739111)
    ·
      refine ⟨42479636699240899112608667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28319757799493932741739111 42479636699240899112608667)
      ·
        refine ⟨63719455048861348668913001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42479636699240899112608667 63719455048861348668913001)
        ·
          refine ⟨47789591286646011501684751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63719455048861348668913001 47789591286646011501684751)
          ·
            refine ⟨71684386929969017252527127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47789591286646011501684751 71684386929969017252527127)
            ·
              refine ⟨107526580394953525878790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71684386929969017252527127 107526580394953525878790691)
              ·
                refine ⟨161289870592430288818186037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107526580394953525878790691 161289870592430288818186037)
                ·
                  refine ⟨15120925368040339576704941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161289870592430288818186037 15120925368040339576704941)
                  ·
                    refine ⟨5670347013015127341264353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15120925368040339576704941 5670347013015127341264353)
                    ·
                      refine ⟨4252760259761345505948265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670347013015127341264353 4252760259761345505948265)
                      ·
                        rfl

theorem cell23_8282221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_8282221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282221 prefixEnd_8282221 := by exact prefixLift 8282221
  have htrace : WordTrace (prefixWord ++ tailWord_8282221) baseStart_8282221 baseEnd_8282221 := by
    simpa [prefixWord, tailWord_8282221, baseEnd_8282221] using wordTrace_append hprefix tailTrace_8282221
  have hstable : (prefixWord ++ tailWord_8282221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282221).length < 2 ^ (prefixWord ++ tailWord_8282221).sum := by decide
  have hdescent : baseEnd_8282221 < baseStart_8282221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282268 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_8282268 : Nat := 118140960795 + 8282268 * 2 ^ 59
def prefixEnd_8282268 : Nat := 4983230072969 + 3 ^ 40 * 8282268 * 2
def baseEnd_8282268 : Nat := 4252784393352106822060549

theorem tailTrace_8282268 : CollatzResearch.WordTrace tailWord_8282268 prefixEnd_8282268 4252784393352106822060549 := by
  unfold tailWord_8282268
  simp only [CollatzResearch.WordTrace]
  refine ⟨151039565379382504802755729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201386087172510006403674305 151039565379382504802755729)
  ·
    refine ⟨113279674034536878602066797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151039565379382504802755729 113279674034536878602066797)
    ·
      refine ⟨42479877762951329475775049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113279674034536878602066797 42479877762951329475775049)
      ·
        refine ⟨31859908322213497106831287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42479877762951329475775049 31859908322213497106831287)
        ·
          refine ⟨47789862483320245660246931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31859908322213497106831287 47789862483320245660246931)
          ·
            refine ⟨71684793724980368490370397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47789862483320245660246931 71684793724980368490370397)
            ·
              refine ⟨26881797646867638183888899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71684793724980368490370397 26881797646867638183888899)
              ·
                refine ⟨40322696470301457275833349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26881797646867638183888899 40322696470301457275833349)
                ·
                  refine ⟨7560505588181523239218753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40322696470301457275833349 7560505588181523239218753)
                  ·
                    refine ⟨5670379191136142429414065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560505588181523239218753 5670379191136142429414065)
                    ·
                      refine ⟨4252784393352106822060549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670379191136142429414065 4252784393352106822060549)
                      ·
                        rfl

theorem cell23_8282268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_8282268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282268 prefixEnd_8282268 := by exact prefixLift 8282268
  have htrace : WordTrace (prefixWord ++ tailWord_8282268) baseStart_8282268 baseEnd_8282268 := by
    simpa [prefixWord, tailWord_8282268, baseEnd_8282268] using wordTrace_append hprefix tailTrace_8282268
  have hstable : (prefixWord ++ tailWord_8282268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282268).length < 2 ^ (prefixWord ++ tailWord_8282268).sum := by decide
  have hdescent : baseEnd_8282268 < baseStart_8282268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282285 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_8282285 : Nat := 118140960795 + 8282285 * 2 ^ 59
def prefixEnd_8282285 : Nat := 4983230072969 + 3 ^ 40 * 8282285 * 2
def baseEnd_8282285 : Nat := 4252793122523233255547971

theorem tailTrace_8282285 : CollatzResearch.WordTrace tailWord_8282285 prefixEnd_8282285 4252793122523233255547971 := by
  unfold tailWord_8282285
  simp only [CollatzResearch.WordTrace]
  refine ⟨302079750799703421508880309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201386500533135614339253539 302079750799703421508880309)
  ·
    refine ⟨28319976637472195766457529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302079750799703421508880309 28319976637472195766457529)
    ·
      refine ⟨21239982478104146824843147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28319976637472195766457529 21239982478104146824843147)
      ·
        refine ⟨31859973717156220237264721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21239982478104146824843147 31859973717156220237264721)
        ·
          refine ⟨23894980287867165177948541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31859973717156220237264721 23894980287867165177948541)
          ·
            refine ⟨8960617607950186941730703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23894980287867165177948541 8960617607950186941730703)
            ·
              refine ⟨13440926411925280412596055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960617607950186941730703 13440926411925280412596055)
              ·
                refine ⟨20161389617887920618894083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13440926411925280412596055 20161389617887920618894083)
                ·
                  refine ⟨30242084426831880928341125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20161389617887920618894083 30242084426831880928341125)
                  ·
                    refine ⟨5670390830030977674063961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30242084426831880928341125 5670390830030977674063961)
                    ·
                      refine ⟨4252793122523233255547971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670390830030977674063961 4252793122523233255547971)
                      ·
                        rfl

theorem cell23_8282285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_8282285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282285 prefixEnd_8282285 := by exact prefixLift 8282285
  have htrace : WordTrace (prefixWord ++ tailWord_8282285) baseStart_8282285 baseEnd_8282285 := by
    simpa [prefixWord, tailWord_8282285, baseEnd_8282285] using wordTrace_append hprefix tailTrace_8282285
  have hstable : (prefixWord ++ tailWord_8282285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282285).length < 2 ^ (prefixWord ++ tailWord_8282285).sum := by decide
  have hdescent : baseEnd_8282285 < baseStart_8282285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282304 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_8282304 : Nat := 118140960795 + 8282304 * 2 ^ 59
def prefixEnd_8282304 : Nat := 4983230072969 + 3 ^ 40 * 8282304 * 2
def baseEnd_8282304 : Nat := 1417600959551889560403461

theorem tailTrace_8282304 : CollatzResearch.WordTrace tailWord_8282304 prefixEnd_8282304 1417600959551889560403461 := by
  unfold tailWord_8282304
  simp only [CollatzResearch.WordTrace]
  refine ⟨151040221893317293876910983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201386962524423058502547977 151040221893317293876910983)
  ·
    refine ⟨226560332839975940815366475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151040221893317293876910983 226560332839975940815366475)
    ·
      refine ⟨339840499259963911223049713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226560332839975940815366475 339840499259963911223049713)
      ·
        refine ⟨254880374444972933417287285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339840499259963911223049713 254880374444972933417287285)
        ·
          refine ⟨23895035104216212507870683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254880374444972933417287285 23895035104216212507870683)
          ·
            refine ⟨35842552656324318761806025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895035104216212507870683 35842552656324318761806025)
            ·
              refine ⟨26881914492243239071354519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35842552656324318761806025 26881914492243239071354519)
              ·
                refine ⟨40322871738364858607031779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26881914492243239071354519 40322871738364858607031779)
                ·
                  refine ⟨60484307607547287910547669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40322871738364858607031779 60484307607547287910547669)
                  ·
                    refine ⟨1417600959551889560403461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60484307607547287910547669 1417600959551889560403461)
                    ·
                      rfl

theorem cell23_8282304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_8282304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282304 prefixEnd_8282304 := by exact prefixLift 8282304
  have htrace : WordTrace (prefixWord ++ tailWord_8282304) baseStart_8282304 baseEnd_8282304 := by
    simpa [prefixWord, tailWord_8282304, baseEnd_8282304] using wordTrace_append hprefix tailTrace_8282304
  have hstable : (prefixWord ++ tailWord_8282304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282304).length < 2 ^ (prefixWord ++ tailWord_8282304).sum := by decide
  have hdescent : baseEnd_8282304 < baseStart_8282304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282307 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_8282307 : Nat := 118140960795 + 8282307 * 2 ^ 59
def prefixEnd_8282307 : Nat := 4983230072969 + 3 ^ 40 * 8282307 * 2
def baseEnd_8282307 : Nat := 4252804419097632169472869

theorem tailTrace_8282307 : CollatzResearch.WordTrace tailWord_8282307 prefixEnd_8282307 4252804419097632169472869 := by
  unfold tailWord_8282307
  simp only [CollatzResearch.WordTrace]
  refine ⟨302080553205623719266181175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201387035470415812844120783 302080553205623719266181175)
  ·
    refine ⟨453120829808435578899271763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302080553205623719266181175 453120829808435578899271763)
    ·
      refine ⟨679681244712653368348907645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453120829808435578899271763 679681244712653368348907645)
      ·
        refine ⟨254880466767245013130840367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679681244712653368348907645 254880466767245013130840367)
        ·
          refine ⟨382320700150867519696260551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254880466767245013130840367 382320700150867519696260551)
          ·
            refine ⟨573481050226301279544390827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382320700150867519696260551 573481050226301279544390827)
            ·
              refine ⟨860221575339451919316586241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573481050226301279544390827 860221575339451919316586241)
              ·
                refine ⟨645166181504588939487439681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 860221575339451919316586241 645166181504588939487439681)
                ·
                  refine ⟨483874636128441704615579761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645166181504588939487439681 483874636128441704615579761)
                  ·
                    refine ⟨362905977096331278461684821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 483874636128441704615579761 362905977096331278461684821)
                    ·
                      refine ⟨4252804419097632169472869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 362905977096331278461684821 4252804419097632169472869)
                      ·
                        rfl

theorem cell23_8282307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_8282307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282307 prefixEnd_8282307 := by exact prefixLift 8282307
  have htrace : WordTrace (prefixWord ++ tailWord_8282307) baseStart_8282307 baseEnd_8282307 := by
    simpa [prefixWord, tailWord_8282307, baseEnd_8282307] using wordTrace_append hprefix tailTrace_8282307
  have hstable : (prefixWord ++ tailWord_8282307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282307).length < 2 ^ (prefixWord ++ tailWord_8282307).sum := by decide
  have hdescent : baseEnd_8282307 < baseStart_8282307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282308 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 5]
def baseStart_8282308 : Nat := 118140960795 + 8282308 * 2 ^ 59
def prefixEnd_8282308 : Nat := 4983230072969 + 3 ^ 40 * 8282308 * 2
def baseEnd_8282308 : Nat := 472533881397587407284485

theorem tailTrace_8282308 : CollatzResearch.WordTrace tailWord_8282308 prefixEnd_8282308 472533881397587407284485 := by
  unfold tailWord_8282308
  simp only [CollatzResearch.WordTrace]
  refine ⟨151040294839310048218483789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201387059785746730957978385 151040294839310048218483789)
  ·
    refine ⟨56640110564741268081931421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151040294839310048218483789 56640110564741268081931421)
    ·
      refine ⟨21240041461777975530724283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56640110564741268081931421 21240041461777975530724283)
      ·
        refine ⟨31860062192666963296086425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21240041461777975530724283 31860062192666963296086425)
        ·
          refine ⟨23895046644500222472064819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31860062192666963296086425 23895046644500222472064819)
          ·
            refine ⟨35842569966750333708097229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895046644500222472064819 35842569966750333708097229)
            ·
              refine ⟨13440963737531375140536461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35842569966750333708097229 13440963737531375140536461)
              ·
                refine ⟨5040361401574265677701173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13440963737531375140536461 5040361401574265677701173)
                ·
                  refine ⟨472533881397587407284485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040361401574265677701173 472533881397587407284485)
                  ·
                    rfl

theorem cell23_8282308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_8282308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282308 prefixEnd_8282308 := by exact prefixLift 8282308
  have htrace : WordTrace (prefixWord ++ tailWord_8282308) baseStart_8282308 baseEnd_8282308 := by
    simpa [prefixWord, tailWord_8282308, baseEnd_8282308] using wordTrace_append hprefix tailTrace_8282308
  have hstable : (prefixWord ++ tailWord_8282308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282308).length < 2 ^ (prefixWord ++ tailWord_8282308).sum := by decide
  have hdescent : baseEnd_8282308 < baseStart_8282308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282314 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_8282314 : Nat := 118140960795 + 8282314 * 2 ^ 59
def prefixEnd_8282314 : Nat := 4983230072969 + 3 ^ 40 * 8282314 * 2
def baseEnd_8282314 : Nat := 4252808013462213642085337

theorem tailTrace_8282314 : CollatzResearch.WordTrace tailWord_8282314 prefixEnd_8282314 4252808013462213642085337 := by
  unfold tailWord_8282314
  simp only [CollatzResearch.WordTrace]
  refine ⟨75520202129149589865421499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201387205677732239641123997 75520202129149589865421499)
  ·
    refine ⟨113280303193724384798132249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75520202129149589865421499 113280303193724384798132249)
    ·
      refine ⟨84960227395293288598599187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113280303193724384798132249 84960227395293288598599187)
      ·
        refine ⟨127440341092939932897898781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84960227395293288598599187 127440341092939932897898781)
        ·
          refine ⟨47790127909852474836712043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127440341092939932897898781 47790127909852474836712043)
          ·
            refine ⟨71685191864778712255068065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47790127909852474836712043 71685191864778712255068065)
            ·
              refine ⟨53763893898584034191301049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71685191864778712255068065 53763893898584034191301049)
              ·
                refine ⟨40322920423938025643475787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53763893898584034191301049 40322920423938025643475787)
                ·
                  refine ⟨60484380635907038465213681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40322920423938025643475787 60484380635907038465213681)
                  ·
                    refine ⟨45363285476930278848910261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60484380635907038465213681 45363285476930278848910261)
                    ·
                      refine ⟨4252808013462213642085337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45363285476930278848910261 4252808013462213642085337)
                      ·
                        rfl

theorem cell23_8282314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_8282314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282314 prefixEnd_8282314 := by exact prefixLift 8282314
  have htrace : WordTrace (prefixWord ++ tailWord_8282314) baseStart_8282314 baseEnd_8282314 := by
    simpa [prefixWord, tailWord_8282314, baseEnd_8282314] using wordTrace_append hprefix tailTrace_8282314
  have hstable : (prefixWord ++ tailWord_8282314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282314).length < 2 ^ (prefixWord ++ tailWord_8282314).sum := by decide
  have hdescent : baseEnd_8282314 < baseStart_8282314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282325 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 5]
def baseStart_8282325 : Nat := 118140960795 + 8282325 * 2 ^ 59
def prefixEnd_8282325 : Nat := 4983230072969 + 3 ^ 40 * 8282325 * 2
def baseEnd_8282325 : Nat := 472534851305490344338643

theorem tailTrace_8282325 : CollatzResearch.WordTrace tailWord_8282325 prefixEnd_8282325 472534851305490344338643 := by
  unfold tailWord_8282325
  simp only [CollatzResearch.WordTrace]
  refine ⟨302081209719558508340336429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201387473146372338893557619 302081209719558508340336429)
  ·
    refine ⟨113280453644834440627626161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302081209719558508340336429 113280453644834440627626161)
    ·
      refine ⟨84960340233625830470719621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113280453644834440627626161 84960340233625830470719621)
      ·
        refine ⟨15930063793804843213259929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84960340233625830470719621 15930063793804843213259929)
        ·
          refine ⟨11947547845353632409944947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15930063793804843213259929 11947547845353632409944947)
          ·
            refine ⟨17921321768030448614917421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947547845353632409944947 17921321768030448614917421)
            ·
              refine ⟨6720495663011418230594033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17921321768030448614917421 6720495663011418230594033)
              ·
                refine ⟨5040371747258563672945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720495663011418230594033 5040371747258563672945525)
                ·
                  refine ⟨472534851305490344338643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040371747258563672945525 472534851305490344338643)
                  ·
                    rfl

theorem cell23_8282325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_8282325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282325 prefixEnd_8282325 := by exact prefixLift 8282325
  have htrace : WordTrace (prefixWord ++ tailWord_8282325) baseStart_8282325 baseEnd_8282325 := by
    simpa [prefixWord, tailWord_8282325, baseEnd_8282325] using wordTrace_append hprefix tailTrace_8282325
  have hstable : (prefixWord ++ tailWord_8282325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282325).length < 2 ^ (prefixWord ++ tailWord_8282325).sum := by decide
  have hdescent : baseEnd_8282325 < baseStart_8282325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282385 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 1, 4]
def baseStart_8282385 : Nat := 118140960795 + 8282385 * 2 ^ 59
def prefixEnd_8282385 : Nat := 4983230072969 + 3 ^ 40 * 8282385 * 2
def baseEnd_8282385 : Nat := 1417614823529560954765837

theorem tailTrace_8282385 : CollatzResearch.WordTrace tailWord_8282385 prefixEnd_8282385 1417614823529560954765837 := by
  unfold tailWord_8282385
  simp only [CollatzResearch.WordTrace]
  refine ⟨302083398099341138587520609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201388932066227425725013739 302083398099341138587520609)
  ·
    refine ⟨226562548574505853940640457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302083398099341138587520609 226562548574505853940640457)
    ·
      refine ⟨169921911430879390455480343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226562548574505853940640457 169921911430879390455480343)
      ·
        refine ⟨254882867146319085683220515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169921911430879390455480343 254882867146319085683220515)
        ·
          refine ⟨382324300719478628524830773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254882867146319085683220515 382324300719478628524830773)
          ·
            refine ⟨35842903192451121424202885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 382324300719478628524830773 35842903192451121424202885)
            ·
              refine ⟨6720544348584585267038041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35842903192451121424202885 6720544348584585267038041)
              ·
                refine ⟨5040408261438438950278531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6720544348584585267038041 5040408261438438950278531)
                ·
                  refine ⟨7560612392157658425417797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5040408261438438950278531 7560612392157658425417797)
                  ·
                    refine ⟨1417614823529560954765837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7560612392157658425417797 1417614823529560954765837)
                    ·
                      rfl

theorem cell23_8282385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_8282385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282385 prefixEnd_8282385 := by exact prefixLift 8282385
  have htrace : WordTrace (prefixWord ++ tailWord_8282385) baseStart_8282385 baseEnd_8282385 := by
    simpa [prefixWord, tailWord_8282385, baseEnd_8282385] using wordTrace_append hprefix tailTrace_8282385
  have hstable : (prefixWord ++ tailWord_8282385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282385).length < 2 ^ (prefixWord ++ tailWord_8282385).sum := by decide
  have hdescent : baseEnd_8282385 < baseStart_8282385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282451 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3]
def baseStart_8282451 : Nat := 118140960795 + 8282451 * 2 ^ 59
def prefixEnd_8282451 : Nat := 4983230072969 + 3 ^ 40 * 8282451 * 2
def baseEnd_8282451 : Nat := 4252878360311879606072207

theorem tailTrace_8282451 : CollatzResearch.WordTrace tailWord_8282451 prefixEnd_8282451 4252878360311879606072207 := by
  unfold tailWord_8282451
  simp only [CollatzResearch.WordTrace]
  refine ⟨302085805317102031859423207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201390536878068021239615471 302085805317102031859423207)
  ·
    refine ⟨453128707975653047789134811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302085805317102031859423207 453128707975653047789134811)
    ·
      refine ⟨679693061963479571683702217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453128707975653047789134811 679693061963479571683702217)
      ·
        refine ⟨509769796472609678762776663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679693061963479571683702217 509769796472609678762776663)
        ·
          refine ⟨764654694708914518144164995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509769796472609678762776663 764654694708914518144164995)
          ·
            refine ⟨1146982042063371777216247493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764654694708914518144164995 1146982042063371777216247493)
            ·
              refine ⟨215059132886882208228046405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1146982042063371777216247493 215059132886882208228046405)
              ·
                refine ⟨40323587416290414042758701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215059132886882208228046405 40323587416290414042758701)
                ·
                  refine ⟨15121345281108905266034513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40323587416290414042758701 15121345281108905266034513)
                  ·
                    refine ⟨11341008960831678949525885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15121345281108905266034513 11341008960831678949525885)
                    ·
                      refine ⟨4252878360311879606072207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341008960831678949525885 4252878360311879606072207)
                      ·
                        rfl

theorem cell23_8282451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_8282451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282451 prefixEnd_8282451 := by exact prefixLift 8282451
  have htrace : WordTrace (prefixWord ++ tailWord_8282451) baseStart_8282451 baseEnd_8282451 := by
    simpa [prefixWord, tailWord_8282451, baseEnd_8282451] using wordTrace_append hprefix tailTrace_8282451
  have hstable : (prefixWord ++ tailWord_8282451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282451).length < 2 ^ (prefixWord ++ tailWord_8282451).sum := by decide
  have hdescent : baseEnd_8282451 < baseStart_8282451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282471 : List Nat := [1, 1, 5, 1, 3, 2, 1, 9]
def baseStart_8282471 : Nat := 118140960795 + 8282471 * 2 ^ 59
def prefixEnd_8282471 : Nat := 4983230072969 + 3 ^ 40 * 8282471 * 2
def baseEnd_8282471 : Nat := 157514393700924797326745

theorem tailTrace_8282471 : CollatzResearch.WordTrace tailWord_8282471 prefixEnd_8282471 157514393700924797326745 := by
  unfold tailWord_8282471
  simp only [CollatzResearch.WordTrace]
  refine ⟨302086534777029575275151267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201391023184686383516767511 302086534777029575275151267)
  ·
    refine ⟨453129802165544362912726901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302086534777029575275151267 453129802165544362912726901)
    ·
      refine ⟨42480918953019784023068147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453129802165544362912726901 42480918953019784023068147)
      ·
        refine ⟨63721378429529676034602221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42480918953019784023068147 63721378429529676034602221)
        ·
          refine ⟨23895516911073628512975833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63721378429529676034602221 23895516911073628512975833)
          ·
            refine ⟨17921637683305221384731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23895516911073628512975833 17921637683305221384731875)
            ·
              refine ⟨26882456524957832077097813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921637683305221384731875 26882456524957832077097813)
              ·
                refine ⟨157514393700924797326745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26882456524957832077097813 157514393700924797326745)
                ·
                  rfl

theorem cell23_8282471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 9].length) (baseStart_8282471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282471 prefixEnd_8282471 := by exact prefixLift 8282471
  have htrace : WordTrace (prefixWord ++ tailWord_8282471) baseStart_8282471 baseEnd_8282471 := by
    simpa [prefixWord, tailWord_8282471, baseEnd_8282471] using wordTrace_append hprefix tailTrace_8282471
  have hstable : (prefixWord ++ tailWord_8282471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282471).length < 2 ^ (prefixWord ++ tailWord_8282471).sum := by decide
  have hdescent : baseEnd_8282471 < baseStart_8282471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282481 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_8282481 : Nat := 118140960795 + 8282481 * 2 ^ 59
def prefixEnd_8282481 : Nat := 4983230072969 + 3 ^ 40 * 8282481 * 2
def baseEnd_8282481 : Nat := 4252893764731514488697069

theorem tailTrace_8282481 : CollatzResearch.WordTrace tailWord_8282481 prefixEnd_8282481 4252893764731514488697069 := by
  unfold tailWord_8282481
  simp only [CollatzResearch.WordTrace]
  refine ⟨302086899506993346983015297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201391266337995564655343531 302086899506993346983015297)
  ·
    refine ⟨226565174630245010237261473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302086899506993346983015297 226565174630245010237261473)
    ·
      refine ⟨169923880972683757677946105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226565174630245010237261473 169923880972683757677946105)
      ·
        refine ⟨127442910729512818258459579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169923880972683757677946105 127442910729512818258459579)
        ·
          refine ⟨191164366094269227387689369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127442910729512818258459579 191164366094269227387689369)
          ·
            refine ⟨143373274570701920540767027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191164366094269227387689369 143373274570701920540767027)
            ·
              refine ⟨215059911856052880811150541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143373274570701920540767027 215059911856052880811150541)
              ·
                refine ⟨80647466946019830304181453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215059911856052880811150541 80647466946019830304181453)
                ·
                  refine ⟨30242800104757436364068045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80647466946019830304181453 30242800104757436364068045)
                  ·
                    refine ⟨11341050039284038636525517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30242800104757436364068045 11341050039284038636525517)
                    ·
                      refine ⟨4252893764731514488697069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341050039284038636525517 4252893764731514488697069)
                      ·
                        rfl

theorem cell23_8282481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_8282481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282481 prefixEnd_8282481 := by exact prefixLift 8282481
  have htrace : WordTrace (prefixWord ++ tailWord_8282481) baseStart_8282481 baseEnd_8282481 := by
    simpa [prefixWord, tailWord_8282481, baseEnd_8282481] using wordTrace_append hprefix tailTrace_8282481
  have hstable : (prefixWord ++ tailWord_8282481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282481).length < 2 ^ (prefixWord ++ tailWord_8282481).sum := by decide
  have hdescent : baseEnd_8282481 < baseStart_8282481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282485 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_8282485 : Nat := 118140960795 + 8282485 * 2 ^ 59
def prefixEnd_8282485 : Nat := 4983230072969 + 3 ^ 40 * 8282485 * 2
def baseEnd_8282485 : Nat := 4252895818654132473047051

theorem tailTrace_8282485 : CollatzResearch.WordTrace tailWord_8282485 prefixEnd_8282485 4252895818654132473047051 := by
  unfold tailWord_8282485
  simp only [CollatzResearch.WordTrace]
  refine ⟨302087045398978855666160909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201391363599319237110773939 302087045398978855666160909)
  ·
    refine ⟨113282642024617070874810341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302087045398978855666160909 113282642024617070874810341)
    ·
      refine ⟨21240495379615700789026939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113282642024617070874810341 21240495379615700789026939)
      ·
        refine ⟨31860743069423551183540409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21240495379615700789026939 31860743069423551183540409)
        ·
          refine ⟨23895557302067663387655307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31860743069423551183540409 23895557302067663387655307)
          ·
            refine ⟨35843335953101495081482961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895557302067663387655307 35843335953101495081482961)
            ·
              refine ⟨26882501964826121311112221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35843335953101495081482961 26882501964826121311112221)
              ·
                refine ⟨10080938236809795491667083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26882501964826121311112221 10080938236809795491667083)
                ·
                  refine ⟨15121407355214693237500625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10080938236809795491667083 15121407355214693237500625)
                  ·
                    refine ⟨11341055516411019928125469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15121407355214693237500625 11341055516411019928125469)
                    ·
                      refine ⟨4252895818654132473047051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341055516411019928125469 4252895818654132473047051)
                      ·
                        rfl

theorem cell23_8282485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_8282485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282485 prefixEnd_8282485 := by exact prefixLift 8282485
  have htrace : WordTrace (prefixWord ++ tailWord_8282485) baseStart_8282485 baseEnd_8282485 := by
    simpa [prefixWord, tailWord_8282485, baseEnd_8282485] using wordTrace_append hprefix tailTrace_8282485
  have hstable : (prefixWord ++ tailWord_8282485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282485).length < 2 ^ (prefixWord ++ tailWord_8282485).sum := by decide
  have hdescent : baseEnd_8282485 < baseStart_8282485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282499 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 3, 2, 2]
def baseStart_8282499 : Nat := 118140960795 + 8282499 * 2 ^ 59
def prefixEnd_8282499 : Nat := 4983230072969 + 3 ^ 40 * 8282499 * 2
def baseEnd_8282499 : Nat := 4252903007383295418271987

theorem tailTrace_8282499 : CollatzResearch.WordTrace tailWord_8282499 prefixEnd_8282499 4252903007383295418271987 := by
  unfold tailWord_8282499
  simp only [CollatzResearch.WordTrace]
  refine ⟨302087556020928136057170551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201391704013952090704780367 302087556020928136057170551)
  ·
    refine ⟨453131334031392204085755827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302087556020928136057170551 453131334031392204085755827)
    ·
      refine ⟨679697001047088306128633741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453131334031392204085755827 679697001047088306128633741)
      ·
        refine ⟨254886375392658114798237653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679697001047088306128633741 254886375392658114798237653)
        ·
          refine ⟨5973899423265424565583695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 254886375392658114798237653 5973899423265424565583695)
          ·
            refine ⟨8960849134898136848375543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5973899423265424565583695 8960849134898136848375543)
            ·
              refine ⟨13441273702347205272563315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960849134898136848375543 13441273702347205272563315)
              ·
                refine ⟨20161910553520807908844973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13441273702347205272563315 20161910553520807908844973)
                ·
                  refine ⟨7560716457570302965816865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20161910553520807908844973 7560716457570302965816865)
                  ·
                    refine ⟨5670537343177727224362649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560716457570302965816865 5670537343177727224362649)
                    ·
                      refine ⟨4252903007383295418271987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670537343177727224362649 4252903007383295418271987)
                      ·
                        rfl

theorem cell23_8282499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_8282499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282499 prefixEnd_8282499 := by exact prefixLift 8282499
  have htrace : WordTrace (prefixWord ++ tailWord_8282499) baseStart_8282499 baseEnd_8282499 := by
    simpa [prefixWord, tailWord_8282499, baseEnd_8282499] using wordTrace_append hprefix tailTrace_8282499
  have hstable : (prefixWord ++ tailWord_8282499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282499).length < 2 ^ (prefixWord ++ tailWord_8282499).sum := by decide
  have hdescent : baseEnd_8282499 < baseStart_8282499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282558 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_8282558 : Nat := 118140960795 + 8282558 * 2 ^ 59
def prefixEnd_8282558 : Nat := 4983230072969 + 3 ^ 40 * 8282558 * 2
def baseEnd_8282558 : Nat := 4252933302741910687434215

theorem tailTrace_8282558 : CollatzResearch.WordTrace tailWord_8282558 prefixEnd_8282558 4252933302741910687434215 := by
  unfold tailWord_8282558
  simp only [CollatzResearch.WordTrace]
  refine ⟨37761213490964298641696041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201393138618476259422378885 37761213490964298641696041)
  ·
    refine ⟨28320910118223223981272031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37761213490964298641696041 28320910118223223981272031)
    ·
      refine ⟨42481365177334835971908047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28320910118223223981272031 42481365177334835971908047)
      ·
        refine ⟨63722047766002253957862071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42481365177334835971908047 63722047766002253957862071)
        ·
          refine ⟨95583071649003380936793107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63722047766002253957862071 95583071649003380936793107)
          ·
            refine ⟨143374607473505071405189661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95583071649003380936793107 143374607473505071405189661)
            ·
              refine ⟨53765477802564401776946123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143374607473505071405189661 53765477802564401776946123)
              ·
                refine ⟨80648216703846602665419185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53765477802564401776946123 80648216703846602665419185)
                ·
                  refine ⟨60486162527884951999064389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80648216703846602665419185 60486162527884951999064389)
                  ·
                    refine ⟨11341155473978428499824573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60486162527884951999064389 11341155473978428499824573)
                    ·
                      refine ⟨4252933302741910687434215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341155473978428499824573 4252933302741910687434215)
                      ·
                        rfl

theorem cell23_8282558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_8282558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282558 prefixEnd_8282558 := by exact prefixLift 8282558
  have htrace : WordTrace (prefixWord ++ tailWord_8282558) baseStart_8282558 baseEnd_8282558 := by
    simpa [prefixWord, tailWord_8282558, baseEnd_8282558] using wordTrace_append hprefix tailTrace_8282558
  have hstable : (prefixWord ++ tailWord_8282558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282558).length < 2 ^ (prefixWord ++ tailWord_8282558).sum := by decide
  have hdescent : baseEnd_8282558 < baseStart_8282558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282568 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_8282568 : Nat := 118140960795 + 8282568 * 2 ^ 59
def prefixEnd_8282568 : Nat := 4983230072969 + 3 ^ 40 * 8282568 * 2
def baseEnd_8282568 : Nat := 4252938437548455648309169

theorem tailTrace_8282568 : CollatzResearch.WordTrace tailWord_8282568 prefixEnd_8282568 4252938437548455648309169 := by
  unfold tailWord_8282568
  simp only [CollatzResearch.WordTrace]
  refine ⟨151045036328839080420716179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201393381771785440560954905 151045036328839080420716179)
  ·
    refine ⟨226567554493258620631074269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151045036328839080420716179 226567554493258620631074269)
    ·
      refine ⟨84962832934971982736652851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226567554493258620631074269 84962832934971982736652851)
      ·
        refine ⟨127444249402457974104979277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84962832934971982736652851 127444249402457974104979277)
        ·
          refine ⟨47791593525921740289367229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127444249402457974104979277 47791593525921740289367229)
          ·
            refine ⟨17921847572220652608512711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47791593525921740289367229 17921847572220652608512711)
            ·
              refine ⟨26882771358330978912769067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921847572220652608512711 26882771358330978912769067)
              ·
                refine ⟨40324157037496468369153601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26882771358330978912769067 40324157037496468369153601)
                ·
                  refine ⟨30243117778122351276865201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40324157037496468369153601 30243117778122351276865201)
                  ·
                    refine ⟨22682338333591763457648901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30243117778122351276865201 22682338333591763457648901)
                    ·
                      refine ⟨4252938437548455648309169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22682338333591763457648901 4252938437548455648309169)
                      ·
                        rfl

theorem cell23_8282568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_8282568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282568 prefixEnd_8282568 := by exact prefixLift 8282568
  have htrace : WordTrace (prefixWord ++ tailWord_8282568) baseStart_8282568 baseEnd_8282568 := by
    simpa [prefixWord, tailWord_8282568, baseEnd_8282568] using wordTrace_append hprefix tailTrace_8282568
  have hstable : (prefixWord ++ tailWord_8282568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282568).length < 2 ^ (prefixWord ++ tailWord_8282568).sum := by decide
  have hdescent : baseEnd_8282568 < baseStart_8282568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282572 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_8282572 : Nat := 118140960795 + 8282572 * 2 ^ 59
def prefixEnd_8282572 : Nat := 4983230072969 + 3 ^ 40 * 8282572 * 2
def baseEnd_8282572 : Nat := 4252940491471073632659151

theorem tailTrace_8282572 : CollatzResearch.WordTrace tailWord_8282572 prefixEnd_8282572 4252940491471073632659151 := by
  unfold tailWord_8282572
  simp only [CollatzResearch.WordTrace]
  refine ⟨151045109274831834762288985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201393479033109113016385313 151045109274831834762288985)
  ·
    refine ⟨113283831956123876071716739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151045109274831834762288985 113283831956123876071716739)
    ·
      refine ⟨169925747934185814107575109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113283831956123876071716739 169925747934185814107575109)
      ·
        refine ⟨31861077737659840145170333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169925747934185814107575109 31861077737659840145170333)
        ·
          refine ⟨11947904151622440054438875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31861077737659840145170333 11947904151622440054438875)
          ·
            refine ⟨17921856227433660081658313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947904151622440054438875 17921856227433660081658313)
            ·
              refine ⟨13441392170575245061243735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17921856227433660081658313 13441392170575245061243735)
              ·
                refine ⟨20162088255862867591865603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13441392170575245061243735 20162088255862867591865603)
                ·
                  refine ⟨30243132383794301387798405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20162088255862867591865603 30243132383794301387798405)
                  ·
                    refine ⟨5670587321961431510212201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30243132383794301387798405 5670587321961431510212201)
                    ·
                      refine ⟨4252940491471073632659151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670587321961431510212201 4252940491471073632659151)
                      ·
                        rfl

theorem cell23_8282572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_8282572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282572 prefixEnd_8282572 := by exact prefixLift 8282572
  have htrace : WordTrace (prefixWord ++ tailWord_8282572) baseStart_8282572 baseEnd_8282572 := by
    simpa [prefixWord, tailWord_8282572, baseEnd_8282572] using wordTrace_append hprefix tailTrace_8282572
  have hstable : (prefixWord ++ tailWord_8282572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282572).length < 2 ^ (prefixWord ++ tailWord_8282572).sum := by decide
  have hdescent : baseEnd_8282572 < baseStart_8282572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282601 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_8282601 : Nat := 118140960795 + 8282601 * 2 ^ 59
def prefixEnd_8282601 : Nat := 4983230072969 + 3 ^ 40 * 8282601 * 2
def baseEnd_8282601 : Nat := 4252955382410054019196517

theorem tailTrace_8282601 : CollatzResearch.WordTrace tailWord_8282601 prefixEnd_8282601 4252955382410054019196517 := by
  unfold tailWord_8282601
  simp only [CollatzResearch.WordTrace]
  refine ⟨302091276266558607477383657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201394184177705738318255771 302091276266558607477383657)
  ·
    refine ⟨226568457199918955608037743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302091276266558607477383657 226568457199918955608037743)
    ·
      refine ⟨339852685799878433412056615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226568457199918955608037743 339852685799878433412056615)
      ·
        refine ⟨509779028699817650118084923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339852685799878433412056615 509779028699817650118084923)
        ·
          refine ⟨764668543049726475177127385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509779028699817650118084923 764668543049726475177127385)
          ·
            refine ⟨573501407287294856382845539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764668543049726475177127385 573501407287294856382845539)
            ·
              refine ⟨860252110930942284574268309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573501407287294856382845539 860252110930942284574268309)
              ·
                refine ⟨40324317699887919589418827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 860252110930942284574268309 40324317699887919589418827)
                ·
                  refine ⟨60486476549831879384128241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40324317699887919589418827 60486476549831879384128241)
                  ·
                    refine ⟨45364857412373909538096181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60486476549831879384128241 45364857412373909538096181)
                    ·
                      refine ⟨4252955382410054019196517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45364857412373909538096181 4252955382410054019196517)
                      ·
                        rfl

theorem cell23_8282601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_8282601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282601 prefixEnd_8282601 := by exact prefixLift 8282601
  have htrace : WordTrace (prefixWord ++ tailWord_8282601) baseStart_8282601 baseEnd_8282601 := by
    simpa [prefixWord, tailWord_8282601, baseEnd_8282601] using wordTrace_append hprefix tailTrace_8282601
  have hstable : (prefixWord ++ tailWord_8282601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282601).length < 2 ^ (prefixWord ++ tailWord_8282601).sum := by decide
  have hdescent : baseEnd_8282601 < baseStart_8282601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282605 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_8282605 : Nat := 118140960795 + 8282605 * 2 ^ 59
def prefixEnd_8282605 : Nat := 4983230072969 + 3 ^ 40 * 8282605 * 2
def baseEnd_8282605 : Nat := 4252957436332672003546499

theorem tailTrace_8282605 : CollatzResearch.WordTrace tailWord_8282605 prefixEnd_8282605 4252957436332672003546499 := by
  unfold tailWord_8282605
  simp only [CollatzResearch.WordTrace]
  refine ⟨302091422158544116160529269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201394281439029410773686179 302091422158544116160529269)
  ·
    refine ⟨28321070827363510890049619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302091422158544116160529269 28321070827363510890049619)
    ·
      refine ⟨42481606241045266335074429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28321070827363510890049619 42481606241045266335074429)
      ·
        refine ⟨15930602340391974875652911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42481606241045266335074429 15930602340391974875652911)
        ·
          refine ⟨23895903510587962313479367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930602340391974875652911 23895903510587962313479367)
          ·
            refine ⟨35843855265881943470219051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23895903510587962313479367 35843855265881943470219051)
            ·
              refine ⟨53765782898822915205328577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35843855265881943470219051 53765782898822915205328577)
              ·
                refine ⟨40324337174117186403996433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53765782898822915205328577 40324337174117186403996433)
                ·
                  refine ⟨30243252880587889802997325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40324337174117186403996433 30243252880587889802997325)
                  ·
                    refine ⟨11341219830220458676123997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30243252880587889802997325 11341219830220458676123997)
                    ·
                      refine ⟨4252957436332672003546499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341219830220458676123997 4252957436332672003546499)
                      ·
                        rfl

theorem cell23_8282605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_8282605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282605 prefixEnd_8282605 := by exact prefixLift 8282605
  have htrace : WordTrace (prefixWord ++ tailWord_8282605) baseStart_8282605 baseEnd_8282605 := by
    simpa [prefixWord, tailWord_8282605, baseEnd_8282605] using wordTrace_append hprefix tailTrace_8282605
  have hstable : (prefixWord ++ tailWord_8282605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282605).length < 2 ^ (prefixWord ++ tailWord_8282605).sum := by decide
  have hdescent : baseEnd_8282605 < baseStart_8282605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282641 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_8282641 : Nat := 118140960795 + 8282641 * 2 ^ 59
def prefixEnd_8282641 : Nat := 4983230072969 + 3 ^ 40 * 8282641 * 2
def baseEnd_8282641 : Nat := 4252975921636233862696333

theorem tailTrace_8282641 : CollatzResearch.WordTrace tailWord_8282641 prefixEnd_8282641 4252975921636233862696333 := by
  unfold tailWord_8282641
  simp only [CollatzResearch.WordTrace]
  refine ⟨302092735186413694308839777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201395156790942462872559851 302092735186413694308839777)
  ·
    refine ⟨226569551389810270731629833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302092735186413694308839777 226569551389810270731629833)
    ·
      refine ⟨169927163542357703048722375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226569551389810270731629833 169927163542357703048722375)
      ·
        refine ⟨254890745313536554573083563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169927163542357703048722375 254890745313536554573083563)
        ·
          refine ⟨382336117970304831859625345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254890745313536554573083563 382336117970304831859625345)
          ·
            refine ⟨286752088477728623894719009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382336117970304831859625345 286752088477728623894719009)
            ·
              refine ⟨215064066358296467921039257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286752088477728623894719009 215064066358296467921039257)
              ·
                refine ⟨161298049768722350940779443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215064066358296467921039257 161298049768722350940779443)
                ·
                  refine ⟨241947074653083526411169165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161298049768722350940779443 241947074653083526411169165)
                  ·
                    refine ⟨90730152994906322404188437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 241947074653083526411169165 90730152994906322404188437)
                    ·
                      refine ⟨4252975921636233862696333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90730152994906322404188437 4252975921636233862696333)
                      ·
                        rfl

theorem cell23_8282641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_8282641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282641 prefixEnd_8282641 := by exact prefixLift 8282641
  have htrace : WordTrace (prefixWord ++ tailWord_8282641) baseStart_8282641 baseEnd_8282641 := by
    simpa [prefixWord, tailWord_8282641, baseEnd_8282641] using wordTrace_append hprefix tailTrace_8282641
  have hstable : (prefixWord ++ tailWord_8282641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282641).length < 2 ^ (prefixWord ++ tailWord_8282641).sum := by decide
  have hdescent : baseEnd_8282641 < baseStart_8282641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282669 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8282669 : Nat := 118140960795 + 8282669 * 2 ^ 59
def prefixEnd_8282669 : Nat := 4983230072969 + 3 ^ 40 * 8282669 * 2
def baseEnd_8282669 : Nat := 4252990299094559753146205

theorem tailTrace_8282669 : CollatzResearch.WordTrace tailWord_8282669 prefixEnd_8282669 4252990299094559753146205 := by
  unfold tailWord_8282669
  simp only [CollatzResearch.WordTrace]
  refine ⟨302093756430312255090859061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201395837620208170060572707 302093756430312255090859061)
  ·
    refine ⟨28321289665341773914768037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302093756430312255090859061 28321289665341773914768037)
    ·
      refine ⟨5310241812251582609019007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28321289665341773914768037 5310241812251582609019007)
      ·
        refine ⟨7965362718377373913528511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310241812251582609019007 7965362718377373913528511)
        ·
          refine ⟨11948044077566060870292767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965362718377373913528511 11948044077566060870292767)
          ·
            refine ⟨17922066116349091305439151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11948044077566060870292767 17922066116349091305439151)
            ·
              refine ⟨26883099174523636958158727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17922066116349091305439151 26883099174523636958158727)
              ·
                refine ⟨40324648761785455437238091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26883099174523636958158727 40324648761785455437238091)
                ·
                  refine ⟨60486973142678183155857137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40324648761785455437238091 60486973142678183155857137)
                  ·
                    refine ⟨45365229857008637366892853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60486973142678183155857137 45365229857008637366892853)
                    ·
                      refine ⟨4252990299094559753146205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45365229857008637366892853 4252990299094559753146205)
                      ·
                        rfl

theorem cell23_8282669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8282669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282669 prefixEnd_8282669 := by exact prefixLift 8282669
  have htrace : WordTrace (prefixWord ++ tailWord_8282669) baseStart_8282669 baseEnd_8282669 := by
    simpa [prefixWord, tailWord_8282669, baseEnd_8282669] using wordTrace_append hprefix tailTrace_8282669
  have hstable : (prefixWord ++ tailWord_8282669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282669).length < 2 ^ (prefixWord ++ tailWord_8282669).sum := by decide
  have hdescent : baseEnd_8282669 < baseStart_8282669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282685 : List Nat := [1, 4, 1, 3, 2, 2, 1, 3, 6]
def baseStart_8282685 : Nat := 118140960795 + 8282685 * 2 ^ 59
def prefixEnd_8282685 : Nat := 4983230072969 + 3 ^ 40 * 8282685 * 2
def baseEnd_8282685 : Nat := 472555390531670187838459

theorem tailTrace_8282685 : CollatzResearch.WordTrace tailWord_8282685 prefixEnd_8282685 472555390531670187838459 := by
  unfold tailWord_8282685
  simp only [CollatzResearch.WordTrace]
  refine ⟨302094339998254289823441509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201396226665502859882294339 302094339998254289823441509)
  ·
    refine ⟨56642688749672679341895283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302094339998254289823441509 56642688749672679341895283)
    ·
      refine ⟨84964033124509019012842925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56642688749672679341895283 84964033124509019012842925)
      ·
        refine ⟨31861512421690882129816097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84964033124509019012842925 31861512421690882129816097)
        ·
          refine ⟨23896134316268161597362073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31861512421690882129816097 23896134316268161597362073)
          ·
            refine ⟨17922100737201121198021555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23896134316268161597362073 17922100737201121198021555)
            ·
              refine ⟨26883151105801681797032333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17922100737201121198021555 26883151105801681797032333)
              ·
                refine ⟨10081181664675630673887125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26883151105801681797032333 10081181664675630673887125)
                ·
                  refine ⟨472555390531670187838459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10081181664675630673887125 472555390531670187838459)
                  ·
                    rfl

theorem cell23_8282685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_8282685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282685 prefixEnd_8282685 := by exact prefixLift 8282685
  have htrace : WordTrace (prefixWord ++ tailWord_8282685) baseStart_8282685 baseEnd_8282685 := by
    simpa [prefixWord, tailWord_8282685, baseEnd_8282685] using wordTrace_append hprefix tailTrace_8282685
  have hstable : (prefixWord ++ tailWord_8282685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282685).length < 2 ^ (prefixWord ++ tailWord_8282685).sum := by decide
  have hdescent : baseEnd_8282685 < baseStart_8282685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282745 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_8282745 : Nat := 118140960795 + 8282745 * 2 ^ 59
def prefixEnd_8282745 : Nat := 4983230072969 + 3 ^ 40 * 8282745 * 2
def baseEnd_8282745 : Nat := 1417676441208100485265285

theorem tailTrace_8282745 : CollatzResearch.WordTrace tailWord_8282745 prefixEnd_8282745 1417676441208100485265285 := by
  unfold tailWord_8282745
  simp only [CollatzResearch.WordTrace]
  refine ⟨302096528378036920070625689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201397685585357946713750459 302096528378036920070625689)
  ·
    refine ⟨226572396283527690052969267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302096528378036920070625689 226572396283527690052969267)
    ·
      refine ⟨339858594425291535079453901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226572396283527690052969267 339858594425291535079453901)
      ·
        refine ⟨127446972909484325654795213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339858594425291535079453901 127446972909484325654795213)
        ·
          refine ⟨47792614841056622120548205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127446972909484325654795213 47792614841056622120548205)
          ·
            refine ⟨17922230565396233295205577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47792614841056622120548205 17922230565396233295205577)
            ·
              refine ⟨13441672924047174971404183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17922230565396233295205577 13441672924047174971404183)
              ·
                refine ⟨20162509386070762457106275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13441672924047174971404183 20162509386070762457106275)
                ·
                  refine ⟨30243764079106143685659413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20162509386070762457106275 30243764079106143685659413)
                  ·
                    refine ⟨1417676441208100485265285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30243764079106143685659413 1417676441208100485265285)
                    ·
                      rfl

theorem cell23_8282745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_8282745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282745 prefixEnd_8282745 := by exact prefixLift 8282745
  have htrace : WordTrace (prefixWord ++ tailWord_8282745) baseStart_8282745 baseEnd_8282745 := by
    simpa [prefixWord, tailWord_8282745, baseEnd_8282745] using wordTrace_append hprefix tailTrace_8282745
  have hstable : (prefixWord ++ tailWord_8282745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282745).length < 2 ^ (prefixWord ++ tailWord_8282745).sum := by decide
  have hdescent : baseEnd_8282745 < baseStart_8282745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282748 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_8282748 : Nat := 118140960795 + 8282748 * 2 ^ 59
def prefixEnd_8282748 : Nat := 4983230072969 + 3 ^ 40 * 8282748 * 2
def baseEnd_8282748 : Nat := 4253030864066264944058341

theorem tailTrace_8282748 : CollatzResearch.WordTrace tailWord_8282748 prefixEnd_8282748 4253030864066264944058341 := by
  unfold tailWord_8282748
  simp only [CollatzResearch.WordTrace]
  refine ⟨151048318898513025791492449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201397758531350701055323265 151048318898513025791492449)
  ·
    refine ⟨113286239173884769343619337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151048318898513025791492449 113286239173884769343619337)
    ·
      refine ⟨84964679380413577007714503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113286239173884769343619337 84964679380413577007714503)
      ·
        refine ⟨127447019070620365511571755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84964679380413577007714503 127447019070620365511571755)
        ·
          refine ⟨191170528605930548267357633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127447019070620365511571755 191170528605930548267357633)
          ·
            refine ⟨143377896454447911200518225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191170528605930548267357633 143377896454447911200518225)
            ·
              refine ⟨107533422340835933400388669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143377896454447911200518225 107533422340835933400388669)
              ·
                refine ⟨40325033377813475025145751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107533422340835933400388669 40325033377813475025145751)
                ·
                  refine ⟨60487550066720212537718627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40325033377813475025145751 60487550066720212537718627)
                  ·
                    refine ⟨90731325100080318806577941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60487550066720212537718627 90731325100080318806577941)
                    ·
                      refine ⟨4253030864066264944058341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90731325100080318806577941 4253030864066264944058341)
                      ·
                        rfl

theorem cell23_8282748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_8282748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282748 prefixEnd_8282748 := by exact prefixLift 8282748
  have htrace : WordTrace (prefixWord ++ tailWord_8282748) baseStart_8282748 baseEnd_8282748 := by
    simpa [prefixWord, tailWord_8282748, baseEnd_8282748] using wordTrace_append hprefix tailTrace_8282748
  have hstable : (prefixWord ++ tailWord_8282748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282748).length < 2 ^ (prefixWord ++ tailWord_8282748).sum := by decide
  have hdescent : baseEnd_8282748 < baseStart_8282748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282752 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2]
def baseStart_8282752 : Nat := 118140960795 + 8282752 * 2 ^ 59
def prefixEnd_8282752 : Nat := 4983230072969 + 3 ^ 40 * 8282752 * 2
def baseEnd_8282752 : Nat := 4253032917988882928408323

theorem tailTrace_8282752 : CollatzResearch.WordTrace tailWord_8282752 prefixEnd_8282752 4253032917988882928408323 := by
  unfold tailWord_8282752
  simp only [CollatzResearch.WordTrace]
  refine ⟨151048391844505780133065255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201397855792674373510753673 151048391844505780133065255)
  ·
    refine ⟨226572587766758670199597883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151048391844505780133065255 226572587766758670199597883)
    ·
      refine ⟨339858881650138005299396825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226572587766758670199597883 339858881650138005299396825)
      ·
        refine ⟨254894161237603503974547619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339858881650138005299396825 254894161237603503974547619)
        ·
          refine ⟨382341241856405255961821429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254894161237603503974547619 382341241856405255961821429)
          ·
            refine ⟨35844491424037992746420759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 382341241856405255961821429 35844491424037992746420759)
            ·
              refine ⟨53766737136056989119631139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35844491424037992746420759 53766737136056989119631139)
              ·
                refine ⟨80650105704085483679446709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53766737136056989119631139 80650105704085483679446709)
                ·
                  refine ⟨7560947409758014094948129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80650105704085483679446709 7560947409758014094948129)
                  ·
                    refine ⟨5670710557318510571211097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7560947409758014094948129 5670710557318510571211097)
                    ·
                      refine ⟨4253032917988882928408323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5670710557318510571211097 4253032917988882928408323)
                      ·
                        rfl

theorem cell23_8282752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_8282752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282752 prefixEnd_8282752 := by exact prefixLift 8282752
  have htrace : WordTrace (prefixWord ++ tailWord_8282752) baseStart_8282752 baseEnd_8282752 := by
    simpa [prefixWord, tailWord_8282752, baseEnd_8282752] using wordTrace_append hprefix tailTrace_8282752
  have hstable : (prefixWord ++ tailWord_8282752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282752).length < 2 ^ (prefixWord ++ tailWord_8282752).sum := by decide
  have hdescent : baseEnd_8282752 < baseStart_8282752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282755 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3]
def baseStart_8282755 : Nat := 118140960795 + 8282755 * 2 ^ 59
def prefixEnd_8282755 : Nat := 4983230072969 + 3 ^ 40 * 8282755 * 2
def baseEnd_8282755 : Nat := 4253034458430846416670809

theorem tailTrace_8282755 : CollatzResearch.WordTrace tailWord_8282755 prefixEnd_8282755 4253034458430846416670809 := by
  unfold tailWord_8282755
  simp only [CollatzResearch.WordTrace]
  refine ⟨302096893108000691778489719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201397928738667127852326479 302096893108000691778489719)
  ·
    refine ⟨453145339662001037667734579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302096893108000691778489719 453145339662001037667734579)
    ·
      refine ⟨679718009493001556501601869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453145339662001037667734579 679718009493001556501601869)
      ·
        refine ⟨254894253559875583688100701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679718009493001556501601869 254894253559875583688100701)
        ·
          refine ⟨95585345084953343883037763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254894253559875583688100701 95585345084953343883037763)
          ·
            refine ⟨143378017627430015824556645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95585345084953343883037763 143378017627430015824556645)
            ·
              refine ⟨26883378305143127967104371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143378017627430015824556645 26883378305143127967104371)
              ·
                refine ⟨40325067457714691950656557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26883378305143127967104371 40325067457714691950656557)
                ·
                  refine ⟨15121900296643009481496209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40325067457714691950656557 15121900296643009481496209)
                  ·
                    refine ⟨11341425222482257111122157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15121900296643009481496209 11341425222482257111122157)
                    ·
                      refine ⟨4253034458430846416670809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341425222482257111122157 4253034458430846416670809)
                      ·
                        rfl

theorem cell23_8282755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_8282755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282755 prefixEnd_8282755 := by exact prefixLift 8282755
  have htrace : WordTrace (prefixWord ++ tailWord_8282755) baseStart_8282755 baseEnd_8282755 := by
    simpa [prefixWord, tailWord_8282755, baseEnd_8282755] using wordTrace_append hprefix tailTrace_8282755
  have hstable : (prefixWord ++ tailWord_8282755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282755).length < 2 ^ (prefixWord ++ tailWord_8282755).sum := by decide
  have hdescent : baseEnd_8282755 < baseStart_8282755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282895 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 2, 5]
def baseStart_8282895 : Nat := 118140960795 + 8282895 * 2 ^ 59
def prefixEnd_8282895 : Nat := 4983230072969 + 3 ^ 40 * 8282895 * 2
def baseEnd_8282895 : Nat := 1417702115240825289640055

theorem tailTrace_8282895 : CollatzResearch.WordTrace tailWord_8282895 prefixEnd_8282895 1417702115240825289640055 := by
  unfold tailWord_8282895
  simp only [CollatzResearch.WordTrace]
  refine ⟨302101999327493495688586139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201401332884995663792390759 302101999327493495688586139)
  ·
    refine ⟨453152998991240243532879209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302101999327493495688586139 453152998991240243532879209)
    ·
      refine ⟨339864749243430182649659407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453152998991240243532879209 339864749243430182649659407)
      ·
        refine ⟨509797123865145273974489111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339864749243430182649659407 509797123865145273974489111)
        ·
          refine ⟨764695685797717910961733667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509797123865145273974489111 764695685797717910961733667)
          ·
            refine ⟨1147043528696576866442600501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764695685797717910961733667 1147043528696576866442600501)
            ·
              refine ⟨107535330815304081228993797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1147043528696576866442600501 107535330815304081228993797)
              ·
                refine ⟨20162874527869515230436337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107535330815304081228993797 20162874527869515230436337)
                ·
                  refine ⟨15122155895902136422827253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20162874527869515230436337 15122155895902136422827253)
                  ·
                    refine ⟨1417702115240825289640055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15122155895902136422827253 1417702115240825289640055)
                    ·
                      rfl

theorem cell23_8282895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_8282895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282895 prefixEnd_8282895 := by exact prefixLift 8282895
  have htrace : WordTrace (prefixWord ++ tailWord_8282895) baseStart_8282895 baseEnd_8282895 := by
    simpa [prefixWord, tailWord_8282895, baseEnd_8282895] using wordTrace_append hprefix tailTrace_8282895
  have hstable : (prefixWord ++ tailWord_8282895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282895).length < 2 ^ (prefixWord ++ tailWord_8282895).sum := by decide
  have hdescent : baseEnd_8282895 < baseStart_8282895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282915 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4]
def baseStart_8282915 : Nat := 118140960795 + 8282915 * 2 ^ 59
def prefixEnd_8282915 : Nat := 4983230072969 + 3 ^ 40 * 8282915 * 2
def baseEnd_8282915 : Nat := 4253116615335565790670073

theorem tailTrace_8282915 : CollatzResearch.WordTrace tailWord_8282915 prefixEnd_8282915 4253116615335565790670073 := by
  unfold tailWord_8282915
  simp only [CollatzResearch.WordTrace]
  refine ⟨302102728787421039104314199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201401819191614026069542799 302102728787421039104314199)
  ·
    refine ⟨453154093181131558656471299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302102728787421039104314199 453154093181131558656471299)
    ·
      refine ⟨679731139771697337984706949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453154093181131558656471299 679731139771697337984706949)
      ·
        refine ⟨127449588707193250872132553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 679731139771697337984706949 127449588707193250872132553)
        ·
          refine ⟨95587191530394938154099415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127449588707193250872132553 95587191530394938154099415)
          ·
            refine ⟨143380787295592407231149123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95587191530394938154099415 143380787295592407231149123)
            ·
              refine ⟨215071180943388610846723685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143380787295592407231149123 215071180943388610846723685)
              ·
                refine ⟨40325846426885364533760691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215071180943388610846723685 40325846426885364533760691)
                ·
                  refine ⟨60488769640328046800641037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40325846426885364533760691 60488769640328046800641037)
                  ·
                    refine ⟨22683288615123017550240389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60488769640328046800641037 22683288615123017550240389)
                    ·
                      refine ⟨4253116615335565790670073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22683288615123017550240389 4253116615335565790670073)
                      ·
                        rfl

theorem cell23_8282915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_8282915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282915 prefixEnd_8282915 := by exact prefixLift 8282915
  have htrace : WordTrace (prefixWord ++ tailWord_8282915) baseStart_8282915 baseEnd_8282915 := by
    simpa [prefixWord, tailWord_8282915, baseEnd_8282915] using wordTrace_append hprefix tailTrace_8282915
  have hstable : (prefixWord ++ tailWord_8282915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282915).length < 2 ^ (prefixWord ++ tailWord_8282915).sum := by decide
  have hdescent : baseEnd_8282915 < baseStart_8282915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282952 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_8282952 : Nat := 118140960795 + 8282952 * 2 ^ 59
def prefixEnd_8282952 : Nat := 4983230072969 + 3 ^ 40 * 8282952 * 2
def baseEnd_8282952 : Nat := 4253135614119782145907403

theorem tailTrace_8282952 : CollatzResearch.WordTrace tailWord_8282952 prefixEnd_8282952 4253135614119782145907403 := by
  unfold tailWord_8282952
  simp only [CollatzResearch.WordTrace]
  refine ⟨151052039144143497211705555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201402718858857996282274073 151052039144143497211705555)
  ·
    refine ⟨226578058716215245817558333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151052039144143497211705555 226578058716215245817558333)
    ·
      refine ⟨84966772018580717181584375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226578058716215245817558333 84966772018580717181584375)
      ·
        refine ⟨127450158027871075772376563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84966772018580717181584375 127450158027871075772376563)
        ·
          refine ⟨191175237041806613658564845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127450158027871075772376563 191175237041806613658564845)
          ·
            refine ⟨71690713890677480121961817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191175237041806613658564845 71690713890677480121961817)
            ·
              refine ⟨53768035418008110091471363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71690713890677480121961817 53768035418008110091471363)
              ·
                refine ⟨80652053127012165137207045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53768035418008110091471363 80652053127012165137207045)
                ·
                  refine ⟨15122259961314780963226321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80652053127012165137207045 15122259961314780963226321)
                  ·
                    refine ⟨11341694970986085722419741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15122259961314780963226321 11341694970986085722419741)
                    ·
                      refine ⟨4253135614119782145907403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341694970986085722419741 4253135614119782145907403)
                      ·
                        rfl

theorem cell23_8282952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_8282952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282952 prefixEnd_8282952 := by exact prefixLift 8282952
  have htrace : WordTrace (prefixWord ++ tailWord_8282952) baseStart_8282952 baseEnd_8282952 := by
    simpa [prefixWord, tailWord_8282952, baseEnd_8282952] using wordTrace_append hprefix tailTrace_8282952
  have hstable : (prefixWord ++ tailWord_8282952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282952).length < 2 ^ (prefixWord ++ tailWord_8282952).sum := by decide
  have hdescent : baseEnd_8282952 < baseStart_8282952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8282975 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_8282975 : Nat := 118140960795 + 8282975 * 2 ^ 59
def prefixEnd_8282975 : Nat := 4983230072969 + 3 ^ 40 * 8282975 * 2
def baseEnd_8282975 : Nat := 4253147424174835555919797

theorem tailTrace_8282975 : CollatzResearch.WordTrace tailWord_8282975 prefixEnd_8282975 4253147424174835555919797 := by
  unfold tailWord_8282975
  simp only [CollatzResearch.WordTrace]
  refine ⟨302104917167203669351498379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201403278111469112900998919 302104917167203669351498379)
  ·
    refine ⟨453157375750805504027247569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302104917167203669351498379 453157375750805504027247569)
    ·
      refine ⟨339868031813104128020435677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453157375750805504027247569 339868031813104128020435677)
      ·
        refine ⟨127450511929914048007663379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339868031813104128020435677 127450511929914048007663379)
        ·
          refine ⟨191175767894871072011495069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127450511929914048007663379 191175767894871072011495069)
          ·
            refine ⟨71690912960576652004310651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191175767894871072011495069 71690912960576652004310651)
            ·
              refine ⟨107536369440864978006465977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71690912960576652004310651 107536369440864978006465977)
              ·
                refine ⟨80652277080648733504849483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107536369440864978006465977 80652277080648733504849483)
                ·
                  refine ⟨120978415620973100257274225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80652277080648733504849483 120978415620973100257274225)
                  ·
                    refine ⟨90733811715729825192955669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120978415620973100257274225 90733811715729825192955669)
                    ·
                      refine ⟨4253147424174835555919797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90733811715729825192955669 4253147424174835555919797)
                      ·
                        rfl

theorem cell23_8282975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_8282975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8282975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8282975 prefixEnd_8282975 := by exact prefixLift 8282975
  have htrace : WordTrace (prefixWord ++ tailWord_8282975) baseStart_8282975 baseEnd_8282975 := by
    simpa [prefixWord, tailWord_8282975, baseEnd_8282975] using wordTrace_append hprefix tailTrace_8282975
  have hstable : (prefixWord ++ tailWord_8282975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8282975).length < 2 ^ (prefixWord ++ tailWord_8282975).sum := by decide
  have hdescent : baseEnd_8282975 < baseStart_8282975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8282975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283010 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_8283010 : Nat := 118140960795 + 8283010 * 2 ^ 59
def prefixEnd_8283010 : Nat := 4983230072969 + 3 ^ 40 * 8283010 * 2
def baseEnd_8283010 : Nat := 1417721798665914306327379

theorem tailTrace_8283010 : CollatzResearch.WordTrace tailWord_8283010 prefixEnd_8283010 1417721798665914306327379 := by
  unfold tailWord_8283010
  simp only [CollatzResearch.WordTrace]
  refine ⟨75526548430519217582255621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201404129148051246886014989 75526548430519217582255621)
  ·
    refine ⟨14161227830722353296672929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75526548430519217582255621 14161227830722353296672929)
    ·
      refine ⟨10620920873041764972504697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14161227830722353296672929 10620920873041764972504697)
      ·
        refine ⟨7965690654781323729378523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10620920873041764972504697 7965690654781323729378523)
        ·
          refine ⟨11948535982171985594067785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965690654781323729378523 11948535982171985594067785)
          ·
            refine ⟨8961401986628989195550839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11948535982171985594067785 8961401986628989195550839)
            ·
              refine ⟨13442102979943483793326259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961401986628989195550839 13442102979943483793326259)
              ·
                refine ⟨20163154469915225689989389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442102979943483793326259 20163154469915225689989389)
                ·
                  refine ⟨7561182926218209633746021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20163154469915225689989389 7561182926218209633746021)
                  ·
                    refine ⟨1417721798665914306327379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561182926218209633746021 1417721798665914306327379)
                    ·
                      rfl

theorem cell23_8283010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_8283010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283010 prefixEnd_8283010 := by exact prefixLift 8283010
  have htrace : WordTrace (prefixWord ++ tailWord_8283010) baseStart_8283010 baseEnd_8283010 := by
    simpa [prefixWord, tailWord_8283010, baseEnd_8283010] using wordTrace_append hprefix tailTrace_8283010
  have hstable : (prefixWord ++ tailWord_8283010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283010).length < 2 ^ (prefixWord ++ tailWord_8283010).sum := by decide
  have hdescent : baseEnd_8283010 < baseStart_8283010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283016 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_8283016 : Nat := 118140960795 + 8283016 * 2 ^ 59
def prefixEnd_8283016 : Nat := 4983230072969 + 3 ^ 40 * 8283016 * 2
def baseEnd_8283016 : Nat := 4253168476881669895507109

theorem tailTrace_8283016 : CollatzResearch.WordTrace tailWord_8283016 prefixEnd_8283016 4253168476881669895507109 := by
  unfold tailWord_8283016
  simp only [CollatzResearch.WordTrace]
  refine ⟨151053206280027566676870451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201404275040036755569160601 151053206280027566676870451)
  ·
    refine ⟨226579809420041350015305677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151053206280027566676870451 226579809420041350015305677)
    ·
      refine ⟨84967428532515506255739629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226579809420041350015305677 84967428532515506255739629)
      ·
        refine ⟨31862785699693314845902361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84967428532515506255739629 31862785699693314845902361)
        ·
          refine ⟨23897089274769986134426771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31862785699693314845902361 23897089274769986134426771)
          ·
            refine ⟨35845633912154979201640157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23897089274769986134426771 35845633912154979201640157)
            ·
              refine ⟨13442112717058117200615059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35845633912154979201640157 13442112717058117200615059)
              ·
                refine ⟨20163169075587175800922589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442112717058117200615059 20163169075587175800922589)
                ·
                  refine ⟨7561188403345190925345971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20163169075587175800922589 7561188403345190925345971)
                  ·
                    refine ⟨11341782605017786388018957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7561188403345190925345971 11341782605017786388018957)
                    ·
                      refine ⟨4253168476881669895507109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341782605017786388018957 4253168476881669895507109)
                      ·
                        rfl

theorem cell23_8283016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_8283016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283016 prefixEnd_8283016 := by exact prefixLift 8283016
  have htrace : WordTrace (prefixWord ++ tailWord_8283016) baseStart_8283016 baseEnd_8283016 := by
    simpa [prefixWord, tailWord_8283016, baseEnd_8283016] using wordTrace_append hprefix tailTrace_8283016
  have hstable : (prefixWord ++ tailWord_8283016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283016).length < 2 ^ (prefixWord ++ tailWord_8283016).sum := by decide
  have hdescent : baseEnd_8283016 < baseStart_8283016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283039 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_8283039 : Nat := 118140960795 + 8283039 * 2 ^ 59
def prefixEnd_8283039 : Nat := 4983230072969 + 3 ^ 40 * 8283039 * 2
def baseEnd_8283039 : Nat := 4253180286936723305519503

theorem tailTrace_8283039 : CollatzResearch.WordTrace tailWord_8283039 prefixEnd_8283039 4253180286936723305519503 := by
  unfold tailWord_8283039
  simp only [CollatzResearch.WordTrace]
  refine ⟨302107251438971808281828171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201404834292647872187885447 302107251438971808281828171)
  ·
    refine ⟨453160877158457712422742257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302107251438971808281828171 453160877158457712422742257)
    ·
      refine ⟨339870657868843284317056693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453160877158457712422742257 339870657868843284317056693)
      ·
        refine ⟨31862874175204057904724065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339870657868843284317056693 31862874175204057904724065)
        ·
          refine ⟨23897155631403043428543049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31862874175204057904724065 23897155631403043428543049)
          ·
            refine ⟨17922866723552282571407287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23897155631403043428543049 17922866723552282571407287)
            ·
              refine ⟨26884300085328423857110931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17922866723552282571407287 26884300085328423857110931)
              ·
                refine ⟨40326450127992635785666397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26884300085328423857110931 40326450127992635785666397)
                ·
                  refine ⟨15122418797997238419624899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40326450127992635785666397 15122418797997238419624899)
                  ·
                    refine ⟨22683628196995857629437349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15122418797997238419624899 22683628196995857629437349)
                    ·
                      refine ⟨4253180286936723305519503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22683628196995857629437349 4253180286936723305519503)
                      ·
                        rfl

theorem cell23_8283039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_8283039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283039 prefixEnd_8283039 := by exact prefixLift 8283039
  have htrace : WordTrace (prefixWord ++ tailWord_8283039) baseStart_8283039 baseEnd_8283039 := by
    simpa [prefixWord, tailWord_8283039, baseEnd_8283039] using wordTrace_append hprefix tailTrace_8283039
  have hstable : (prefixWord ++ tailWord_8283039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283039).length < 2 ^ (prefixWord ++ tailWord_8283039).sum := by decide
  have hdescent : baseEnd_8283039 < baseStart_8283039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283052 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_8283052 : Nat := 118140960795 + 8283052 * 2 ^ 59
def prefixEnd_8283052 : Nat := 4983230072969 + 3 ^ 40 * 8283052 * 2
def baseEnd_8283052 : Nat := 4253186962185231754656943

theorem tailTrace_8283052 : CollatzResearch.WordTrace tailWord_8283052 prefixEnd_8283052 4253186962185231754656943 := by
  unfold tailWord_8283052
  simp only [CollatzResearch.WordTrace]
  refine ⟨151053862793962355751025705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201405150391949807668034273 151053862793962355751025705)
  ·
    refine ⟨113290397095471766813269279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151053862793962355751025705 113290397095471766813269279)
    ·
      refine ⟨169935595643207650219903919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113290397095471766813269279 169935595643207650219903919)
      ·
        refine ⟨254903393464811475329855879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169935595643207650219903919 254903393464811475329855879)
        ·
          refine ⟨382355090197217212994783819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254903393464811475329855879 382355090197217212994783819)
          ·
            refine ⟨573532635295825819492175729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382355090197217212994783819 573532635295825819492175729)
            ·
              refine ⟨430149476471869364619131797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573532635295825819492175729 430149476471869364619131797)
              ·
                refine ⟨20163256709618876466521803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430149476471869364619131797 20163256709618876466521803)
                ·
                  refine ⟨30244885064428314699782705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20163256709618876466521803 30244885064428314699782705)
                  ·
                    refine ⟨22683663798321236024837029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30244885064428314699782705 22683663798321236024837029)
                    ·
                      refine ⟨4253186962185231754656943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22683663798321236024837029 4253186962185231754656943)
                      ·
                        rfl

theorem cell23_8283052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_8283052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283052 prefixEnd_8283052 := by exact prefixLift 8283052
  have htrace : WordTrace (prefixWord ++ tailWord_8283052) baseStart_8283052 baseEnd_8283052 := by
    simpa [prefixWord, tailWord_8283052, baseEnd_8283052] using wordTrace_append hprefix tailTrace_8283052
  have hstable : (prefixWord ++ tailWord_8283052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283052).length < 2 ^ (prefixWord ++ tailWord_8283052).sum := by decide
  have hdescent : baseEnd_8283052 < baseStart_8283052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283089 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_8283089 : Nat := 118140960795 + 8283089 * 2 ^ 59
def prefixEnd_8283089 : Nat := 4983230072969 + 3 ^ 40 * 8283089 * 2
def baseEnd_8283089 : Nat := 4253205960969448109894273

theorem tailTrace_8283089 : CollatzResearch.WordTrace tailWord_8283089 prefixEnd_8283089 4253205960969448109894273 := by
  unfold tailWord_8283089
  simp only [CollatzResearch.WordTrace]
  refine ⟨302109075088790666821148321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201406050059193777880765547 302109075088790666821148321)
  ·
    refine ⟨226581806316593000115861241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302109075088790666821148321 226581806316593000115861241)
    ·
      refine ⟨169936354737444750086895931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226581806316593000115861241 169936354737444750086895931)
      ·
        refine ⟨254904532106167125130343897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169936354737444750086895931 254904532106167125130343897)
        ·
          refine ⟨191178399079625343847757923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254904532106167125130343897 191178399079625343847757923)
          ·
            refine ⟨286767598619438015771636885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191178399079625343847757923 286767598619438015771636885)
            ·
              refine ⟨13442231185286156989295479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286767598619438015771636885 13442231185286156989295479)
              ·
                refine ⟨20163346777929235483943219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442231185286156989295479 20163346777929235483943219)
                ·
                  refine ⟨30245020166893853225914829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20163346777929235483943219 30245020166893853225914829)
                  ·
                    refine ⟨11341882562585194959718061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30245020166893853225914829 11341882562585194959718061)
                    ·
                      refine ⟨4253205960969448109894273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11341882562585194959718061 4253205960969448109894273)
                      ·
                        rfl

theorem cell23_8283089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_8283089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283089 prefixEnd_8283089 := by exact prefixLift 8283089
  have htrace : WordTrace (prefixWord ++ tailWord_8283089) baseStart_8283089 baseEnd_8283089 := by
    simpa [prefixWord, tailWord_8283089, baseEnd_8283089] using wordTrace_append hprefix tailTrace_8283089
  have hstable : (prefixWord ++ tailWord_8283089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283089).length < 2 ^ (prefixWord ++ tailWord_8283089).sum := by decide
  have hdescent : baseEnd_8283089 < baseStart_8283089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283197 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_8283197 : Nat := 118140960795 + 8283197 * 2 ^ 59
def prefixEnd_8283197 : Nat := 4983230072969 + 3 ^ 40 * 8283197 * 2
def baseEnd_8283197 : Nat := 4253261416880133687343777

theorem tailTrace_8283197 : CollatzResearch.WordTrace tailWord_8283197 prefixEnd_8283197 4253261416880133687343777 := by
  unfold tailWord_8283197
  simp only [CollatzResearch.WordTrace]
  refine ⟨302113014172399401266079845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201408676114932934177386563 302113014172399401266079845)
  ·
    refine ⟨56646190157324887737389971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302113014172399401266079845 56646190157324887737389971)
    ·
      refine ⟨84969285235987331606084957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56646190157324887737389971 84969285235987331606084957)
      ·
        refine ⟨31863481963495249352281859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84969285235987331606084957 31863481963495249352281859)
        ·
          refine ⟨47795222945242874028422789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31863481963495249352281859 47795222945242874028422789)
          ·
            refine ⟨8961604302233038880329273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47795222945242874028422789 8961604302233038880329273)
            ·
              refine ⟨6721203226674779160246955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8961604302233038880329273 6721203226674779160246955)
              ·
                refine ⟨10081804840012168740370433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721203226674779160246955 10081804840012168740370433)
                ·
                  refine ⟨7561353630009126555277825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10081804840012168740370433 7561353630009126555277825)
                  ·
                    refine ⟨5671015222506844916458369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561353630009126555277825 5671015222506844916458369)
                    ·
                      refine ⟨4253261416880133687343777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671015222506844916458369 4253261416880133687343777)
                      ·
                        rfl

theorem cell23_8283197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_8283197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283197 prefixEnd_8283197 := by exact prefixLift 8283197
  have htrace : WordTrace (prefixWord ++ tailWord_8283197) baseStart_8283197 baseEnd_8283197 := by
    simpa [prefixWord, tailWord_8283197, baseEnd_8283197] using wordTrace_append hprefix tailTrace_8283197
  have hstable : (prefixWord ++ tailWord_8283197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283197).length < 2 ^ (prefixWord ++ tailWord_8283197).sum := by decide
  have hdescent : baseEnd_8283197 < baseStart_8283197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283219 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4]
def baseStart_8283219 : Nat := 118140960795 + 8283219 * 2 ^ 59
def prefixEnd_8283219 : Nat := 4983230072969 + 3 ^ 40 * 8283219 * 2
def baseEnd_8283219 : Nat := 4253272713454532601268675

theorem tailTrace_8283219 : CollatzResearch.WordTrace tailWord_8283219 prefixEnd_8283219 4253272713454532601268675 := by
  unfold tailWord_8283219
  simp only [CollatzResearch.WordTrace]
  refine ⟨302113816578319699023380711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201409211052213132682253807 302113816578319699023380711)
  ·
    refine ⟨453170724867479548535071067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302113816578319699023380711 453170724867479548535071067)
    ·
      refine ⟨679756087301219322802606601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453170724867479548535071067 679756087301219322802606601)
      ·
        refine ⟨509817065475914492101954951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679756087301219322802606601 509817065475914492101954951)
        ·
          refine ⟨764725598213871738152932427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509817065475914492101954951 764725598213871738152932427)
          ·
            refine ⟨1147088397320807607229398641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764725598213871738152932427 1147088397320807607229398641)
            ·
              refine ⟨860316297990605705422048981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147088397320807607229398641 860316297990605705422048981)
              ·
                refine ⟨20163663234154821220829273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 860316297990605705422048981 20163663234154821220829273)
                ·
                  refine ⟨15122747425616115915621955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20163663234154821220829273 15122747425616115915621955)
                  ·
                    refine ⟨22684121138424173873432933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15122747425616115915621955 22684121138424173873432933)
                    ·
                      refine ⟨4253272713454532601268675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22684121138424173873432933 4253272713454532601268675)
                      ·
                        rfl

theorem cell23_8283219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_8283219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283219 prefixEnd_8283219 := by exact prefixLift 8283219
  have htrace : WordTrace (prefixWord ++ tailWord_8283219) baseStart_8283219 baseEnd_8283219 := by
    simpa [prefixWord, tailWord_8283219, baseEnd_8283219] using wordTrace_append hprefix tailTrace_8283219
  have hstable : (prefixWord ++ tailWord_8283219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283219).length < 2 ^ (prefixWord ++ tailWord_8283219).sum := by decide
  have hdescent : baseEnd_8283219 < baseStart_8283219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283236 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_8283236 : Nat := 118140960795 + 8283236 * 2 ^ 59
def prefixEnd_8283236 : Nat := 4983230072969 + 3 ^ 40 * 8283236 * 2
def baseEnd_8283236 : Nat := 4253281442625659034756097

theorem tailTrace_8283236 : CollatzResearch.WordTrace tailWord_8283236 prefixEnd_8283236 4253281442625659034756097 := by
  unfold tailWord_8283236
  simp only [CollatzResearch.WordTrace]
  refine ⟨151057218309629055463374781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201409624412838740617833041 151057218309629055463374781)
  ·
    refine ⟨56646456866110895798765543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151057218309629055463374781 56646456866110895798765543)
    ·
      refine ⟨84969685299166343698148315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56646456866110895798765543 84969685299166343698148315)
      ·
        refine ⟨127454527948749515547222473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84969685299166343698148315 127454527948749515547222473)
        ·
          refine ⟨95590895961562136660416855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127454527948749515547222473 95590895961562136660416855)
          ·
            refine ⟨143386343942343204990625283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95590895961562136660416855 143386343942343204990625283)
            ·
              refine ⟨215079515913514807485937925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143386343942343204990625283 215079515913514807485937925)
              ·
                refine ⟨40327409233784026403613361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215079515913514807485937925 40327409233784026403613361)
                ·
                  refine ⟨30245556925338019802710021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40327409233784026403613361 30245556925338019802710021)
                  ·
                    refine ⟨5671041923500878713008129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30245556925338019802710021 5671041923500878713008129)
                    ·
                      refine ⟨4253281442625659034756097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671041923500878713008129 4253281442625659034756097)
                      ·
                        rfl

theorem cell23_8283236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_8283236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283236 prefixEnd_8283236 := by exact prefixLift 8283236
  have htrace : WordTrace (prefixWord ++ tailWord_8283236) baseStart_8283236 baseEnd_8283236 := by
    simpa [prefixWord, tailWord_8283236, baseEnd_8283236] using wordTrace_append hprefix tailTrace_8283236
  have hstable : (prefixWord ++ tailWord_8283236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283236).length < 2 ^ (prefixWord ++ tailWord_8283236).sum := by decide
  have hdescent : baseEnd_8283236 < baseStart_8283236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283273 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_8283273 : Nat := 118140960795 + 8283273 * 2 ^ 59
def prefixEnd_8283273 : Nat := 4983230072969 + 3 ^ 40 * 8283273 * 2
def baseEnd_8283273 : Nat := 4253300441409875389993427

theorem tailTrace_8283273 : CollatzResearch.WordTrace tailWord_8283273 prefixEnd_8283273 4253300441409875389993427 := by
  unfold tailWord_8283273
  simp only [CollatzResearch.WordTrace]
  refine ⟨302115786120124066245846473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201410524080082710830564315 302115786120124066245846473)
  ·
    refine ⟨226586839590093049684384855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302115786120124066245846473 226586839590093049684384855)
    ·
      refine ⟨339880259385139574526577283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226586839590093049684384855 339880259385139574526577283)
      ·
        refine ⟨509820389077709361789865925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339880259385139574526577283 509820389077709361789865925)
        ·
          refine ⟨95591322952070505335599861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509820389077709361789865925 95591322952070505335599861)
          ·
            refine ⟨8961686526756609875212487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95591322952070505335599861 8961686526756609875212487)
            ·
              refine ⟨13442529790134914812818731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961686526756609875212487 13442529790134914812818731)
              ·
                refine ⟨20163794685202372219228097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442529790134914812818731 20163794685202372219228097)
                ·
                  refine ⟨15122846013901779164421073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20163794685202372219228097 15122846013901779164421073)
                  ·
                    refine ⟨11342134510426334373315805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15122846013901779164421073 11342134510426334373315805)
                    ·
                      refine ⟨4253300441409875389993427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342134510426334373315805 4253300441409875389993427)
                      ·
                        rfl

theorem cell23_8283273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_8283273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283273 prefixEnd_8283273 := by exact prefixLift 8283273
  have htrace : WordTrace (prefixWord ++ tailWord_8283273) baseStart_8283273 baseEnd_8283273 := by
    simpa [prefixWord, tailWord_8283273, baseEnd_8283273] using wordTrace_append hprefix tailTrace_8283273
  have hstable : (prefixWord ++ tailWord_8283273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283273).length < 2 ^ (prefixWord ++ tailWord_8283273).sum := by decide
  have hdescent : baseEnd_8283273 < baseStart_8283273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283313 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_8283313 : Nat := 118140960795 + 8283313 * 2 ^ 59
def prefixEnd_8283313 : Nat := 4983230072969 + 3 ^ 40 * 8283313 * 2
def baseEnd_8283313 : Nat := 4253320980636055233493243

theorem tailTrace_8283313 : CollatzResearch.WordTrace tailWord_8283313 prefixEnd_8283313 4253320980636055233493243 := by
  unfold tailWord_8283313
  simp only [CollatzResearch.WordTrace]
  refine ⟨302117245039979153077302593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201411496693319435384868395 302117245039979153077302593)
  ·
    refine ⟨226587933779984364807976945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302117245039979153077302593 226587933779984364807976945)
    ·
      refine ⟨169940950334988273605982709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226587933779984364807976945 169940950334988273605982709)
      ·
        refine ⟨15931964093905150650560879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169940950334988273605982709 15931964093905150650560879)
        ·
          refine ⟨23897946140857725975841319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15931964093905150650560879 23897946140857725975841319)
          ·
            refine ⟨35846919211286588963761979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23897946140857725975841319 35846919211286588963761979)
            ·
              refine ⟨53770378816929883445642969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35846919211286588963761979 53770378816929883445642969)
              ·
                refine ⟨40327784112697412584232227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53770378816929883445642969 40327784112697412584232227)
                ·
                  refine ⟨60491676169046118876348341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40327784112697412584232227 60491676169046118876348341)
                  ·
                    refine ⟨5671094640848073644657657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60491676169046118876348341 5671094640848073644657657)
                    ·
                      refine ⟨4253320980636055233493243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671094640848073644657657 4253320980636055233493243)
                      ·
                        rfl

theorem cell23_8283313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_8283313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283313 prefixEnd_8283313 := by exact prefixLift 8283313
  have htrace : WordTrace (prefixWord ++ tailWord_8283313) baseStart_8283313 baseEnd_8283313 := by
    simpa [prefixWord, tailWord_8283313, baseEnd_8283313] using wordTrace_append hprefix tailTrace_8283313
  have hstable : (prefixWord ++ tailWord_8283313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283313).length < 2 ^ (prefixWord ++ tailWord_8283313).sum := by decide
  have hdescent : baseEnd_8283313 < baseStart_8283313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283336 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_8283336 : Nat := 118140960795 + 8283336 * 2 ^ 59
def prefixEnd_8283336 : Nat := 4983230072969 + 3 ^ 40 * 8283336 * 2
def baseEnd_8283336 : Nat := 1417777596897036214501879

theorem tailTrace_8283336 : CollatzResearch.WordTrace tailWord_8283336 prefixEnd_8283336 1417777596897036214501879 := by
  unfold tailWord_8283336
  simp only [CollatzResearch.WordTrace]
  refine ⟨151059041959447914002694931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201412055945930552003593241 151059041959447914002694931)
  ·
    refine ⟨226588562939171871004042397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151059041959447914002694931 226588562939171871004042397)
    ·
      refine ⟨84970711102189451626515899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226588562939171871004042397 84970711102189451626515899)
      ·
        refine ⟨127456066653284177439773849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84970711102189451626515899 127456066653284177439773849)
        ·
          refine ⟨95592049989963133079830387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127456066653284177439773849 95592049989963133079830387)
          ·
            refine ⟨143388074984944699619745581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95592049989963133079830387 143388074984944699619745581)
            ·
              refine ⟨53770528119354262357404593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143388074984944699619745581 53770528119354262357404593)
              ·
                refine ⟨40327896089515696768053445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53770528119354262357404593 40327896089515696768053445)
                ·
                  refine ⟨7561480516784193144010021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40327896089515696768053445 7561480516784193144010021)
                  ·
                    refine ⟨1417777596897036214501879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561480516784193144010021 1417777596897036214501879)
                    ·
                      rfl

theorem cell23_8283336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_8283336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283336 prefixEnd_8283336 := by exact prefixLift 8283336
  have htrace : WordTrace (prefixWord ++ tailWord_8283336) baseStart_8283336 baseEnd_8283336 := by
    simpa [prefixWord, tailWord_8283336, baseEnd_8283336] using wordTrace_append hprefix tailTrace_8283336
  have hstable : (prefixWord ++ tailWord_8283336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283336).length < 2 ^ (prefixWord ++ tailWord_8283336).sum := by decide
  have hdescent : baseEnd_8283336 < baseStart_8283336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283360 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2]
def baseStart_8283360 : Nat := 118140960795 + 8283360 * 2 ^ 59
def prefixEnd_8283360 : Nat := 4983230072969 + 3 ^ 40 * 8283360 * 2
def baseEnd_8283360 : Nat := 4253345114226816549605527

theorem tailTrace_8283360 : CollatzResearch.WordTrace tailWord_8283360 prefixEnd_8283360 4253345114226816549605527 := by
  unfold tailWord_8283360
  simp only [CollatzResearch.WordTrace]
  refine ⟨151059479635404440052131767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201412639513872586736175689 151059479635404440052131767)
  ·
    refine ⟨226589219453106660078197651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151059479635404440052131767 226589219453106660078197651)
    ·
      refine ⟨339883829179659990117296477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226589219453106660078197651 339883829179659990117296477)
      ·
        refine ⟨127456435942372496293986179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339883829179659990117296477 127456435942372496293986179)
        ·
          refine ⟨191184653913558744440979269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127456435942372496293986179 191184653913558744440979269)
          ·
            refine ⟨35847122608792264582683613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191184653913558744440979269 35847122608792264582683613)
            ·
              refine ⟨13442670978297099218506355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35847122608792264582683613 13442670978297099218506355)
              ·
                refine ⟨20164006467445648827759533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442670978297099218506355 20164006467445648827759533)
                ·
                  refine ⟨7561502425292118310409825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20164006467445648827759533 7561502425292118310409825)
                  ·
                    refine ⟨5671126818969088732807369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561502425292118310409825 5671126818969088732807369)
                    ·
                      refine ⟨4253345114226816549605527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671126818969088732807369 4253345114226816549605527)
                      ·
                        rfl

theorem cell23_8283360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_8283360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283360 prefixEnd_8283360 := by exact prefixLift 8283360
  have htrace : WordTrace (prefixWord ++ tailWord_8283360) baseStart_8283360 baseEnd_8283360 := by
    simpa [prefixWord, tailWord_8283360, baseEnd_8283360] using wordTrace_append hprefix tailTrace_8283360
  have hstable : (prefixWord ++ tailWord_8283360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283360).length < 2 ^ (prefixWord ++ tailWord_8283360).sum := by decide
  have hdescent : baseEnd_8283360 < baseStart_8283360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283370 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_8283370 : Nat := 118140960795 + 8283370 * 2 ^ 59
def prefixEnd_8283370 : Nat := 4983230072969 + 3 ^ 40 * 8283370 * 2
def baseEnd_8283370 : Nat := 1417783416344453836826827

theorem tailTrace_8283370 : CollatzResearch.WordTrace tailWord_8283370 prefixEnd_8283370 1417783416344453836826827 := by
  unfold tailWord_8283370
  simp only [CollatzResearch.WordTrace]
  refine ⟨75529831000193162953031891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201412882667181767874751709 75529831000193162953031891)
  ·
    refine ⟨113294746500289744429547837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75529831000193162953031891 113294746500289744429547837)
    ·
      refine ⟨42485529937608654161080439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113294746500289744429547837 42485529937608654161080439)
      ·
        refine ⟨63728294906412981241620659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42485529937608654161080439 63728294906412981241620659)
        ·
          refine ⟨95592442359619471862430989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63728294906412981241620659 95592442359619471862430989)
          ·
            refine ⟨35847165884857301948411621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95592442359619471862430989 35847165884857301948411621)
            ·
              refine ⟨6721343603410744115327179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35847165884857301948411621 6721343603410744115327179)
              ·
                refine ⟨10082015405116116172990769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721343603410744115327179 10082015405116116172990769)
                ·
                  refine ⟨7561511553837087129743077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082015405116116172990769 7561511553837087129743077)
                  ·
                    refine ⟨1417783416344453836826827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561511553837087129743077 1417783416344453836826827)
                    ·
                      rfl

theorem cell23_8283370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_8283370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283370 prefixEnd_8283370 := by exact prefixLift 8283370
  have htrace : WordTrace (prefixWord ++ tailWord_8283370) baseStart_8283370 baseEnd_8283370 := by
    simpa [prefixWord, tailWord_8283370, baseEnd_8283370] using wordTrace_append hprefix tailTrace_8283370
  have hstable : (prefixWord ++ tailWord_8283370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283370).length < 2 ^ (prefixWord ++ tailWord_8283370).sum := by decide
  have hdescent : baseEnd_8283370 < baseStart_8283370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283393 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_8283393 : Nat := 118140960795 + 8283393 * 2 ^ 59
def prefixEnd_8283393 : Nat := 4983230072969 + 3 ^ 40 * 8283393 * 2
def baseEnd_8283393 : Nat := 4253362059088414920492875

theorem tailTrace_8283393 : CollatzResearch.WordTrace tailWord_8283393 prefixEnd_8283393 4253362059088414920492875 := by
  unfold tailWord_8283393
  simp only [CollatzResearch.WordTrace]
  refine ⟨302120162879689326740214833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201413441919792884493476555 302120162879689326740214833)
  ·
    refine ⟨226590122159766995055161125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302120162879689326740214833 226590122159766995055161125)
    ·
      refine ⟨42485647904956311572842711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226590122159766995055161125 42485647904956311572842711)
      ·
        refine ⟨63728471857434467359264067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42485647904956311572842711 63728471857434467359264067)
        ·
          refine ⟨95592707786151701038896101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63728471857434467359264067 95592707786151701038896101)
          ·
            refine ⟨17923632709903443944793019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95592707786151701038896101 17923632709903443944793019)
            ·
              refine ⟨26885449064855165917189529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17923632709903443944793019 26885449064855165917189529)
              ·
                refine ⟨20164086798641374437892147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26885449064855165917189529 20164086798641374437892147)
                ·
                  refine ⟨30246130197962061656838221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20164086798641374437892147 30246130197962061656838221)
                  ·
                    refine ⟨11342298824235773121314333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30246130197962061656838221 11342298824235773121314333)
                    ·
                      refine ⟨4253362059088414920492875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342298824235773121314333 4253362059088414920492875)
                      ·
                        rfl

theorem cell23_8283393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_8283393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283393 prefixEnd_8283393 := by exact prefixLift 8283393
  have htrace : WordTrace (prefixWord ++ tailWord_8283393) baseStart_8283393 baseEnd_8283393 := by
    simpa [prefixWord, tailWord_8283393, baseEnd_8283393] using wordTrace_append hprefix tailTrace_8283393
  have hstable : (prefixWord ++ tailWord_8283393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283393).length < 2 ^ (prefixWord ++ tailWord_8283393).sum := by decide
  have hdescent : baseEnd_8283393 < baseStart_8283393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283416 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_8283416 : Nat := 118140960795 + 8283416 * 2 ^ 59
def prefixEnd_8283416 : Nat := 4983230072969 + 3 ^ 40 * 8283416 * 2
def baseEnd_8283416 : Nat := 4253373869143468330505269

theorem tailTrace_8283416 : CollatzResearch.WordTrace tailWord_8283416 prefixEnd_8283416 4253373869143468330505269 := by
  unfold tailWord_8283416
  simp only [CollatzResearch.WordTrace]
  refine ⟨151060500879303000834151051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201414001172404001112201401 151060500879303000834151051)
  ·
    refine ⟨226590751318954501251226577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151060500879303000834151051 226590751318954501251226577)
    ·
      refine ⟨169943063489215875938419933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226590751318954501251226577 169943063489215875938419933)
      ·
        refine ⟨63728648808455953476907475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169943063489215875938419933 63728648808455953476907475)
        ·
          refine ⟨95592973212683930215361213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63728648808455953476907475 95592973212683930215361213)
          ·
            refine ⟨35847364954756473830760455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95592973212683930215361213 35847364954756473830760455)
            ·
              refine ⟨53771047432134710746140683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35847364954756473830760455 53771047432134710746140683)
              ·
                refine ⟨80656571148202066119211025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53771047432134710746140683 80656571148202066119211025)
                ·
                  refine ⟨60492428361151549589408269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80656571148202066119211025 60492428361151549589408269)
                  ·
                    refine ⟨22684660635431831096028101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60492428361151549589408269 22684660635431831096028101)
                    ·
                      refine ⟨4253373869143468330505269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22684660635431831096028101 4253373869143468330505269)
                      ·
                        rfl

theorem cell23_8283416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_8283416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283416 prefixEnd_8283416 := by exact prefixLift 8283416
  have htrace : WordTrace (prefixWord ++ tailWord_8283416) baseStart_8283416 baseEnd_8283416 := by
    simpa [prefixWord, tailWord_8283416, baseEnd_8283416] using wordTrace_append hprefix tailTrace_8283416
  have hstable : (prefixWord ++ tailWord_8283416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283416).length < 2 ^ (prefixWord ++ tailWord_8283416).sum := by decide
  have hdescent : baseEnd_8283416 < baseStart_8283416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283436 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_8283436 : Nat := 118140960795 + 8283436 * 2 ^ 59
def prefixEnd_8283436 : Nat := 4983230072969 + 3 ^ 40 * 8283436 * 2
def baseEnd_8283436 : Nat := 4253384138756558252255177

theorem tailTrace_8283436 : CollatzResearch.WordTrace tailWord_8283436 prefixEnd_8283436 4253384138756558252255177 := by
  unfold tailWord_8283436
  simp only [CollatzResearch.WordTrace]
  refine ⟨151060865609266772542015081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201414487479022363389353441 151060865609266772542015081)
  ·
    refine ⟨113295649206950079406511311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151060865609266772542015081 113295649206950079406511311)
    ·
      refine ⟨169943473810425119109766967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113295649206950079406511311 169943473810425119109766967)
      ·
        refine ⟨254915210715637678664650451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169943473810425119109766967 254915210715637678664650451)
        ·
          refine ⟨382372816073456517996975677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254915210715637678664650451 382372816073456517996975677)
          ·
            refine ⟨143389806027546194248865879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382372816073456517996975677 143389806027546194248865879)
            ·
              refine ⟨215084709041319291373298819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143389806027546194248865879 215084709041319291373298819)
              ·
                refine ⟨322627063561978937059948229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215084709041319291373298819 322627063561978937059948229)
                ·
                  refine ⟨60492574417871050698740293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322627063561978937059948229 60492574417871050698740293)
                  ·
                    refine ⟨11342357703350822006013805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60492574417871050698740293 11342357703350822006013805)
                    ·
                      refine ⟨4253384138756558252255177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342357703350822006013805 4253384138756558252255177)
                      ·
                        rfl

theorem cell23_8283436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_8283436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283436 prefixEnd_8283436 := by exact prefixLift 8283436
  have htrace : WordTrace (prefixWord ++ tailWord_8283436) baseStart_8283436 baseEnd_8283436 := by
    simpa [prefixWord, tailWord_8283436, baseEnd_8283436] using wordTrace_append hprefix tailTrace_8283436
  have hstable : (prefixWord ++ tailWord_8283436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283436).length < 2 ^ (prefixWord ++ tailWord_8283436).sum := by decide
  have hdescent : baseEnd_8283436 < baseStart_8283436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283437 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_8283437 : Nat := 118140960795 + 8283437 * 2 ^ 59
def prefixEnd_8283437 : Nat := 4983230072969 + 3 ^ 40 * 8283437 * 2
def baseEnd_8283437 : Nat := 4253384652237212748342673

theorem tailTrace_8283437 : CollatzResearch.WordTrace tailWord_8283437 prefixEnd_8283437 4253384652237212748342673 := by
  unfold tailWord_8283437
  simp only [CollatzResearch.WordTrace]
  refine ⟨302121767691529922254816565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201414511794353281503211043 302121767691529922254816565)
  ·
    refine ⟨28323915721080930211389053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302121767691529922254816565 28323915721080930211389053)
    ·
      refine ⟨10621468395405348829270895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28323915721080930211389053 10621468395405348829270895)
      ·
        refine ⟨15932202593108023243906343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621468395405348829270895 15932202593108023243906343)
        ·
          refine ⟨23898303889662034865859515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15932202593108023243906343 23898303889662034865859515)
          ·
            refine ⟨35847455834493052298789273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23898303889662034865859515 35847455834493052298789273)
            ·
              refine ⟨26885591875869789224091955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35847455834493052298789273 26885591875869789224091955)
              ·
                refine ⟨40328387813804683836137933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26885591875869789224091955 40328387813804683836137933)
                ·
                  refine ⟨15123145430176756438551725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40328387813804683836137933 15123145430176756438551725)
                  ·
                    refine ⟨5671179536316283664456897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15123145430176756438551725 5671179536316283664456897)
                    ·
                      refine ⟨4253384652237212748342673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671179536316283664456897 4253384652237212748342673)
                      ·
                        rfl

theorem cell23_8283437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_8283437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283437 prefixEnd_8283437 := by exact prefixLift 8283437
  have htrace : WordTrace (prefixWord ++ tailWord_8283437) baseStart_8283437 baseEnd_8283437 := by
    simpa [prefixWord, tailWord_8283437, baseEnd_8283437] using wordTrace_append hprefix tailTrace_8283437
  have hstable : (prefixWord ++ tailWord_8283437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283437).length < 2 ^ (prefixWord ++ tailWord_8283437).sum := by decide
  have hdescent : baseEnd_8283437 < baseStart_8283437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283450 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_8283450 : Nat := 118140960795 + 8283450 * 2 ^ 59
def prefixEnd_8283450 : Nat := 4983230072969 + 3 ^ 40 * 8283450 * 2
def baseEnd_8283450 : Nat := 4253391327485721197480113

theorem tailTrace_8283450 : CollatzResearch.WordTrace tailWord_8283450 prefixEnd_8283450 4253391327485721197480113 := by
  unfold tailWord_8283450
  simp only [CollatzResearch.WordTrace]
  refine ⟨75530560460120706368759951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201414827893655216983359869 75530560460120706368759951)
  ·
    refine ⟨113295840690181059553139927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75530560460120706368759951 113295840690181059553139927)
    ·
      refine ⟨169943761035271589329709891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113295840690181059553139927 169943761035271589329709891)
      ·
        refine ⟨254915641552907383994564837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169943761035271589329709891 254915641552907383994564837)
        ·
          refine ⟨47796682791170134498980907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254915641552907383994564837 47796682791170134498980907)
          ·
            refine ⟨71695024186755201748471361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47796682791170134498980907 71695024186755201748471361)
            ·
              refine ⟨53771268140066401311353521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71695024186755201748471361 53771268140066401311353521)
              ·
                refine ⟨40328451105049800983515141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53771268140066401311353521 40328451105049800983515141)
                ·
                  refine ⟨7561584582196837684409089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40328451105049800983515141 7561584582196837684409089)
                  ·
                    refine ⟨5671188436647628263306817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561584582196837684409089 5671188436647628263306817)
                    ·
                      refine ⟨4253391327485721197480113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671188436647628263306817 4253391327485721197480113)
                      ·
                        rfl

theorem cell23_8283450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_8283450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283450 prefixEnd_8283450 := by exact prefixLift 8283450
  have htrace : WordTrace (prefixWord ++ tailWord_8283450) baseStart_8283450 baseEnd_8283450 := by
    simpa [prefixWord, tailWord_8283450, baseEnd_8283450] using wordTrace_append hprefix tailTrace_8283450
  have hstable : (prefixWord ++ tailWord_8283450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283450).length < 2 ^ (prefixWord ++ tailWord_8283450).sum := by decide
  have hdescent : baseEnd_8283450 < baseStart_8283450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283473 : List Nat := [1, 2, 2, 1, 4, 1, 1, 6, 5]
def baseStart_8283473 : Nat := 118140960795 + 8283473 * 2 ^ 59
def prefixEnd_8283473 : Nat := 4983230072969 + 3 ^ 40 * 8283473 * 2
def baseEnd_8283473 : Nat := 472600348615641623054723

theorem tailTrace_8283473 : CollatzResearch.WordTrace tailWord_8283473 prefixEnd_8283473 472600348615641623054723 := by
  unfold tailWord_8283473
  simp only [CollatzResearch.WordTrace]
  refine ⟨302123080719399500403127073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201415387146266333602084715 302123080719399500403127073)
  ·
    refine ⟨226592310539549625302345305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302123080719399500403127073 226592310539549625302345305)
    ·
      refine ⟨169944232904662218976758979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226592310539549625302345305 169944232904662218976758979)
      ·
        refine ⟨254916349356993328465138469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169944232904662218976758979 254916349356993328465138469)
        ·
          refine ⟨47796815504436249087213463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254916349356993328465138469 47796815504436249087213463)
          ·
            refine ⟨71695223256654373630820195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47796815504436249087213463 71695223256654373630820195)
            ·
              refine ⟨107542834884981560446230293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71695223256654373630820195 107542834884981560446230293)
              ·
                refine ⟨5041070385233510645917045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107542834884981560446230293 5041070385233510645917045)
                ·
                  refine ⟨472600348615641623054723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041070385233510645917045 472600348615641623054723)
                  ·
                    rfl

theorem cell23_8283473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 5].length) (baseStart_8283473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283473 prefixEnd_8283473 := by exact prefixLift 8283473
  have htrace : WordTrace (prefixWord ++ tailWord_8283473) baseStart_8283473 baseEnd_8283473 := by
    simpa [prefixWord, tailWord_8283473, baseEnd_8283473] using wordTrace_append hprefix tailTrace_8283473
  have hstable : (prefixWord ++ tailWord_8283473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283473).length < 2 ^ (prefixWord ++ tailWord_8283473).sum := by decide
  have hdescent : baseEnd_8283473 < baseStart_8283473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283478 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_8283478 : Nat := 118140960795 + 8283478 * 2 ^ 59
def prefixEnd_8283478 : Nat := 4983230072969 + 3 ^ 40 * 8283478 * 2
def baseEnd_8283478 : Nat := 4253405704944047087929985

theorem tailTrace_8283478 : CollatzResearch.WordTrace tailWord_8283478 prefixEnd_8283478 4253405704944047087929985 := by
  unfold tailWord_8283478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882703942773836641066193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201415508722920924171372725 18882703942773836641066193)
  ·
    refine ⟨14162027957080377480799645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18882703942773836641066193 14162027957080377480799645)
    ·
      refine ⟨5310760483905141555299867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14162027957080377480799645 5310760483905141555299867)
      ·
        refine ⟨7966140725857712332949801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310760483905141555299867 7966140725857712332949801)
        ·
          refine ⟨5974605544393284249712351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7966140725857712332949801 5974605544393284249712351)
          ·
            refine ⟨8961908316589926374568527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974605544393284249712351 8961908316589926374568527)
            ·
              refine ⟨13442862474884889561852791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961908316589926374568527 13442862474884889561852791)
              ·
                refine ⟨20164293712327334342779187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13442862474884889561852791 20164293712327334342779187)
                ·
                  refine ⟨30246440568491001514168781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20164293712327334342779187 30246440568491001514168781)
                  ·
                    refine ⟨11342415213184125567813293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30246440568491001514168781 11342415213184125567813293)
                    ·
                      refine ⟨4253405704944047087929985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342415213184125567813293 4253405704944047087929985)
                      ·
                        rfl

theorem cell23_8283478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_8283478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283478 prefixEnd_8283478 := by exact prefixLift 8283478
  have htrace : WordTrace (prefixWord ++ tailWord_8283478) baseStart_8283478 baseEnd_8283478 := by
    simpa [prefixWord, tailWord_8283478, baseEnd_8283478] using wordTrace_append hprefix tailTrace_8283478
  have hstable : (prefixWord ++ tailWord_8283478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283478).length < 2 ^ (prefixWord ++ tailWord_8283478).sum := by decide
  have hdescent : baseEnd_8283478 < baseStart_8283478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283523 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4]
def baseStart_8283523 : Nat := 118140960795 + 8283523 * 2 ^ 59
def prefixEnd_8283523 : Nat := 4983230072969 + 3 ^ 40 * 8283523 * 2
def baseEnd_8283523 : Nat := 4253428811573499411867277

theorem tailTrace_8283523 : CollatzResearch.WordTrace tailWord_8283523 prefixEnd_8283523 4253428811573499411867277 := by
  unfold tailWord_8283523
  simp only [CollatzResearch.WordTrace]
  refine ⟨302124904369218358942447223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201416602912812239294964815 302124904369218358942447223)
  ·
    refine ⟨453187356553827538413670835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302124904369218358942447223 453187356553827538413670835)
    ·
      refine ⟨679781034830741307620506253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453187356553827538413670835 679781034830741307620506253)
      ·
        refine ⟨254917888061527990357689845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679781034830741307620506253 254917888061527990357689845)
        ·
          refine ⟨23898552005768249096033423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254917888061527990357689845 23898552005768249096033423)
          ·
            refine ⟨35847828008652373644050135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23898552005768249096033423 35847828008652373644050135)
            ·
              refine ⟨53771742012978560466075203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35847828008652373644050135 53771742012978560466075203)
              ·
                refine ⟨80657613019467840699112805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53771742012978560466075203 80657613019467840699112805)
                ·
                  refine ⟨15123302441150220131083651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80657613019467840699112805 15123302441150220131083651)
                  ·
                    refine ⟨22684953661725330196625477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15123302441150220131083651 22684953661725330196625477)
                    ·
                      refine ⟨4253428811573499411867277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22684953661725330196625477 4253428811573499411867277)
                      ·
                        rfl

theorem cell23_8283523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_8283523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283523 prefixEnd_8283523 := by exact prefixLift 8283523
  have htrace : WordTrace (prefixWord ++ tailWord_8283523) baseStart_8283523 baseEnd_8283523 := by
    simpa [prefixWord, tailWord_8283523, baseEnd_8283523] using wordTrace_append hprefix tailTrace_8283523
  have hstable : (prefixWord ++ tailWord_8283523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283523).length < 2 ^ (prefixWord ++ tailWord_8283523).sum := by decide
  have hdescent : baseEnd_8283523 < baseStart_8283523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283543 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_8283543 : Nat := 118140960795 + 8283543 * 2 ^ 59
def prefixEnd_8283543 : Nat := 4983230072969 + 3 ^ 40 * 8283543 * 2
def baseEnd_8283543 : Nat := 4253439081186589333617185

theorem tailTrace_8283543 : CollatzResearch.WordTrace tailWord_8283543 prefixEnd_8283543 4253439081186589333617185 := by
  unfold tailWord_8283543
  simp only [CollatzResearch.WordTrace]
  refine ⟨302125633829145902358175283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201417089219430601572116855 302125633829145902358175283)
  ·
    refine ⟨453188450743718853537262925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302125633829145902358175283 453188450743718853537262925)
    ·
      refine ⟨169945669028894570076473597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453188450743718853537262925 169945669028894570076473597)
      ·
        refine ⟨63729625885835463778677599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169945669028894570076473597 63729625885835463778677599)
        ·
          refine ⟨95594438828753195668016399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63729625885835463778677599 95594438828753195668016399)
          ·
            refine ⟨143391658243129793502024599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95594438828753195668016399 143391658243129793502024599)
            ·
              refine ⟨215087487364694690253036899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143391658243129793502024599 215087487364694690253036899)
              ·
                refine ⟨322631231047042035379555349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215087487364694690253036899 322631231047042035379555349)
                ·
                  refine ⟨15123338955330095408416657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322631231047042035379555349 15123338955330095408416657)
                  ·
                    refine ⟨11342504216497571556312493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15123338955330095408416657 11342504216497571556312493)
                    ·
                      refine ⟨4253439081186589333617185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342504216497571556312493 4253439081186589333617185)
                      ·
                        rfl

theorem cell23_8283543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_8283543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283543 prefixEnd_8283543 := by exact prefixLift 8283543
  have htrace : WordTrace (prefixWord ++ tailWord_8283543) baseStart_8283543 baseEnd_8283543 := by
    simpa [prefixWord, tailWord_8283543, baseEnd_8283543] using wordTrace_append hprefix tailTrace_8283543
  have hstable : (prefixWord ++ tailWord_8283543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283543).length < 2 ^ (prefixWord ++ tailWord_8283543).sum := by decide
  have hdescent : baseEnd_8283543 < baseStart_8283543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283617 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_8283617 : Nat := 118140960795 + 8283617 * 2 ^ 59
def prefixEnd_8283617 : Nat := 4983230072969 + 3 ^ 40 * 8283617 * 2
def baseEnd_8283617 : Nat := 4253477078755022044091845

theorem tailTrace_8283617 : CollatzResearch.WordTrace tailWord_8283617 prefixEnd_8283617 4253477078755022044091845 := by
  unfold tailWord_8283617
  simp only [CollatzResearch.WordTrace]
  refine ⟨302128332830877812996369105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201418888553918541997579403 302128332830877812996369105)
  ·
    refine ⟨226596249623158359747276829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302128332830877812996369105 226596249623158359747276829)
    ·
      refine ⟨84973593608684384905228811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226596249623158359747276829 84973593608684384905228811)
      ·
        refine ⟨127460390413026577357843217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84973593608684384905228811 127460390413026577357843217)
        ·
          refine ⟨95595292809769933018382413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127460390413026577357843217 95595292809769933018382413)
          ·
            refine ⟨35848234803663724881893405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95595292809769933018382413 35848234803663724881893405)
            ·
              refine ⟨13443088051373896830710027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35848234803663724881893405 13443088051373896830710027)
              ·
                refine ⟨20164632077060845246065041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13443088051373896830710027 20164632077060845246065041)
                ·
                  refine ⟨15123474057795633934548781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20164632077060845246065041 15123474057795633934548781)
                  ·
                    refine ⟨5671302771673362725455793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15123474057795633934548781 5671302771673362725455793)
                    ·
                      refine ⟨4253477078755022044091845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671302771673362725455793 4253477078755022044091845)
                      ·
                        rfl

theorem cell23_8283617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_8283617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283617 prefixEnd_8283617 := by exact prefixLift 8283617
  have htrace : WordTrace (prefixWord ++ tailWord_8283617) baseStart_8283617 baseEnd_8283617 := by
    simpa [prefixWord, tailWord_8283617, baseEnd_8283617] using wordTrace_append hprefix tailTrace_8283617
  have hstable : (prefixWord ++ tailWord_8283617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283617).length < 2 ^ (prefixWord ++ tailWord_8283617).sum := by decide
  have hdescent : baseEnd_8283617 < baseStart_8283617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283624 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_8283624 : Nat := 118140960795 + 8283624 * 2 ^ 59
def prefixEnd_8283624 : Nat := 4983230072969 + 3 ^ 40 * 8283624 * 2
def baseEnd_8283624 : Nat := 4253480673119603516704313

theorem tailTrace_8283624 : CollatzResearch.WordTrace tailWord_8283624 prefixEnd_8283624 4253480673119603516704313 := by
  unfold tailWord_8283624
  simp only [CollatzResearch.WordTrace]
  refine ⟨151064294070926226595936963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201419058761234968794582617 151064294070926226595936963)
  ·
    refine ⟨226596441106389339893905445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151064294070926226595936963 226596441106389339893905445)
    ·
      refine ⟨42486832707448001230107271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226596441106389339893905445 42486832707448001230107271)
      ·
        refine ⟨63730249061172001845160907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42486832707448001230107271 63730249061172001845160907)
        ·
          refine ⟨95595373591758002767741361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63730249061172001845160907 95595373591758002767741361)
          ·
            refine ⟨71696530193818502075806021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95595373591758002767741361 71696530193818502075806021)
            ·
              refine ⟨13443099411340969139213629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71696530193818502075806021 13443099411340969139213629)
              ·
                refine ⟨5041162279252863427205111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13443099411340969139213629 5041162279252863427205111)
                ·
                  refine ⟨7561743418879295140807667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041162279252863427205111 7561743418879295140807667)
                  ·
                    refine ⟨11342615128318942711211501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7561743418879295140807667 11342615128318942711211501)
                    ·
                      refine ⟨4253480673119603516704313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342615128318942711211501 4253480673119603516704313)
                      ·
                        rfl

theorem cell23_8283624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_8283624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283624 prefixEnd_8283624 := by exact prefixLift 8283624
  have htrace : WordTrace (prefixWord ++ tailWord_8283624) baseStart_8283624 baseEnd_8283624 := by
    simpa [prefixWord, tailWord_8283624, baseEnd_8283624] using wordTrace_append hprefix tailTrace_8283624
  have hstable : (prefixWord ++ tailWord_8283624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283624).length < 2 ^ (prefixWord ++ tailWord_8283624).sum := by decide
  have hdescent : baseEnd_8283624 < baseStart_8283624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283640 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_8283640 : Nat := 118140960795 + 8283640 * 2 ^ 59
def prefixEnd_8283640 : Nat := 4983230072969 + 3 ^ 40 * 8283640 * 2
def baseEnd_8283640 : Nat := 1417829629603358484701413

theorem tailTrace_8283640 : CollatzResearch.WordTrace tailWord_8283640 prefixEnd_8283640 1417829629603358484701413 := by
  unfold tailWord_8283640
  simp only [CollatzResearch.WordTrace]
  refine ⟨151064585854897243962228187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201419447806529658616304249 151064585854897243962228187)
  ·
    refine ⟨226596878782345865943342281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151064585854897243962228187 226596878782345865943342281)
    ·
      refine ⟨169947659086759399457506711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226596878782345865943342281 169947659086759399457506711)
      ·
        refine ⟨254921488630139099186260067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169947659086759399457506711 254921488630139099186260067)
        ·
          refine ⟨382382232945208648779390101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254921488630139099186260067 382382232945208648779390101)
          ·
            refine ⟨17924167169306655411533911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382382232945208648779390101 17924167169306655411533911)
            ·
              refine ⟨26886250753959983117300867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17924167169306655411533911 26886250753959983117300867)
              ·
                refine ⟨40329376130939974675951301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26886250753959983117300867 40329376130939974675951301)
                ·
                  refine ⟨7561758024551245251740869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40329376130939974675951301 7561758024551245251740869)
                  ·
                    refine ⟨1417829629603358484701413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561758024551245251740869 1417829629603358484701413)
                    ·
                      rfl

theorem cell23_8283640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_8283640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283640 prefixEnd_8283640 := by exact prefixLift 8283640
  have htrace : WordTrace (prefixWord ++ tailWord_8283640) baseStart_8283640 baseEnd_8283640 := by
    simpa [prefixWord, tailWord_8283640, baseEnd_8283640] using wordTrace_append hprefix tailTrace_8283640
  have hstable : (prefixWord ++ tailWord_8283640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283640).length < 2 ^ (prefixWord ++ tailWord_8283640).sum := by decide
  have hdescent : baseEnd_8283640 < baseStart_8283640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283657 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 2, 4]
def baseStart_8283657 : Nat := 118140960795 + 8283657 * 2 ^ 59
def prefixEnd_8283657 : Nat := 4983230072969 + 3 ^ 40 * 8283657 * 2
def baseEnd_8283657 : Nat := 1417832539327067295863887

theorem tailTrace_8283657 : CollatzResearch.WordTrace tailWord_8283657 prefixEnd_8283657 1417832539327067295863887 := by
  unfold tailWord_8283657
  simp only [CollatzResearch.WordTrace]
  refine ⟨302129791750732899827825225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201419861167155266551883483 302129791750732899827825225)
  ·
    refine ⟨226597343813049674870868919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302129791750732899827825225 226597343813049674870868919)
    ·
      refine ⟨339896015719574512306303379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226597343813049674870868919 339896015719574512306303379)
      ·
        refine ⟨509844023579361768459455069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339896015719574512306303379 509844023579361768459455069)
        ·
          refine ⟨191191508842260663172295651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509844023579361768459455069 191191508842260663172295651)
          ·
            refine ⟨286787263263390994758443477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191191508842260663172295651 286787263263390994758443477)
            ·
              refine ⟨6721576482735726439651019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 286787263263390994758443477 6721576482735726439651019)
              ·
                refine ⟨10082364724103589659476529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721576482735726439651019 10082364724103589659476529)
                ·
                  refine ⟨7561773543077692244607397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082364724103589659476529 7561773543077692244607397)
                  ·
                    refine ⟨1417832539327067295863887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561773543077692244607397 1417832539327067295863887)
                    ·
                      rfl

theorem cell23_8283657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_8283657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283657 prefixEnd_8283657 := by exact prefixLift 8283657
  have htrace : WordTrace (prefixWord ++ tailWord_8283657) baseStart_8283657 baseEnd_8283657 := by
    simpa [prefixWord, tailWord_8283657, baseEnd_8283657] using wordTrace_append hprefix tailTrace_8283657
  have hstable : (prefixWord ++ tailWord_8283657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283657).length < 2 ^ (prefixWord ++ tailWord_8283657).sum := by decide
  have hdescent : baseEnd_8283657 < baseStart_8283657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283660 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_8283660 : Nat := 118140960795 + 8283660 * 2 ^ 59
def prefixEnd_8283660 : Nat := 4983230072969 + 3 ^ 40 * 8283660 * 2
def baseEnd_8283660 : Nat := 4253499158423165375854147

theorem tailTrace_8283660 : CollatzResearch.WordTrace tailWord_8283660 prefixEnd_8283660 4253499158423165375854147 := by
  unfold tailWord_8283660
  simp only [CollatzResearch.WordTrace]
  refine ⟨151064950584861015670092217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201419934113148020893456289 151064950584861015670092217)
  ·
    refine ⟨113298712938645761752569163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151064950584861015670092217 113298712938645761752569163)
    ·
      refine ⟨169948069407968642628853745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113298712938645761752569163 169948069407968642628853745)
      ·
        refine ⟨127461052055976481971640309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169948069407968642628853745 127461052055976481971640309)
        ·
          refine ⟨11949473630247795184841279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127461052055976481971640309 11949473630247795184841279)
          ·
            refine ⟨17924210445371692777261919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949473630247795184841279 17924210445371692777261919)
            ·
              refine ⟨26886315668057539165892879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17924210445371692777261919 26886315668057539165892879)
              ·
                refine ⟨40329473502086308748839319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26886315668057539165892879 40329473502086308748839319)
                ·
                  refine ⟨60494210253129463123258979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40329473502086308748839319 60494210253129463123258979)
                  ·
                    refine ⟨90741315379694194684888469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60494210253129463123258979 90741315379694194684888469)
                    ·
                      refine ⟨4253499158423165375854147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90741315379694194684888469 4253499158423165375854147)
                      ·
                        rfl

theorem cell23_8283660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_8283660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283660 prefixEnd_8283660 := by exact prefixLift 8283660
  have htrace : WordTrace (prefixWord ++ tailWord_8283660) baseStart_8283660 baseEnd_8283660 := by
    simpa [prefixWord, tailWord_8283660, baseEnd_8283660] using wordTrace_append hprefix tailTrace_8283660
  have hstable : (prefixWord ++ tailWord_8283660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283660).length < 2 ^ (prefixWord ++ tailWord_8283660).sum := by decide
  have hdescent : baseEnd_8283660 < baseStart_8283660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283661 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_8283661 : Nat := 118140960795 + 8283661 * 2 ^ 59
def prefixEnd_8283661 : Nat := 4983230072969 + 3 ^ 40 * 8283661 * 2
def baseEnd_8283661 : Nat := 1417833223967939957313881

theorem tailTrace_8283661 : CollatzResearch.WordTrace tailWord_8283661 prefixEnd_8283661 1417833223967939957313881 := by
  unfold tailWord_8283661
  simp only [CollatzResearch.WordTrace]
  refine ⟨302129937642718408510970837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201419958428478939007313891 302129937642718408510970837)
  ·
    refine ⟨7081170413501212699475879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 302129937642718408510970837 7081170413501212699475879)
    ·
      refine ⟨10621755620251819049213819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081170413501212699475879 10621755620251819049213819)
      ·
        refine ⟨15932633430377728573820729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621755620251819049213819 15932633430377728573820729)
        ·
          refine ⟨11949475072783296430365547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15932633430377728573820729 11949475072783296430365547)
          ·
            refine ⟨17924212609174944645548321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11949475072783296430365547 17924212609174944645548321)
            ·
              refine ⟨13443159456881208484161241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17924212609174944645548321 13443159456881208484161241)
              ·
                refine ⟨10082369592660906363120931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443159456881208484161241 10082369592660906363120931)
                ·
                  refine ⟨15123554388991359544681397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10082369592660906363120931 15123554388991359544681397)
                  ·
                    refine ⟨1417833223967939957313881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15123554388991359544681397 1417833223967939957313881)
                    ·
                      rfl

theorem cell23_8283661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_8283661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283661 prefixEnd_8283661 := by exact prefixLift 8283661
  have htrace : WordTrace (prefixWord ++ tailWord_8283661) baseStart_8283661 baseEnd_8283661 := by
    simpa [prefixWord, tailWord_8283661, baseEnd_8283661] using wordTrace_append hprefix tailTrace_8283661
  have hstable : (prefixWord ++ tailWord_8283661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283661).length < 2 ^ (prefixWord ++ tailWord_8283661).sum := by decide
  have hdescent : baseEnd_8283661 < baseStart_8283661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283667 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 3]
def baseStart_8283667 : Nat := 118140960795 + 8283667 * 2 ^ 59
def prefixEnd_8283667 : Nat := 4983230072969 + 3 ^ 40 * 8283667 * 2
def baseEnd_8283667 : Nat := 4253502752787746848466615

theorem tailTrace_8283667 : CollatzResearch.WordTrace tailWord_8283667 prefixEnd_8283667 4253502752787746848466615 := by
  unfold tailWord_8283667
  simp only [CollatzResearch.WordTrace]
  refine ⟨302130156480696671535689255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201420104320464447690459503 302130156480696671535689255)
  ·
    refine ⟨453195234721045007303533883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302130156480696671535689255 453195234721045007303533883)
    ·
      refine ⟨679792852081567510955300825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453195234721045007303533883 679792852081567510955300825)
      ·
        refine ⟨509844639061175633216475619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679792852081567510955300825 509844639061175633216475619)
        ·
          refine ⟨764766958591763449824713429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509844639061175633216475619 764766958591763449824713429)
          ·
            refine ⟨17924225591994455855266721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 764766958591763449824713429 17924225591994455855266721)
            ·
              refine ⟨13443169193995841891450041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17924225591994455855266721 13443169193995841891450041)
              ·
                refine ⟨10082376895496881418587531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443169193995841891450041 10082376895496881418587531)
                ·
                  refine ⟨15123565343245322127881297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10082376895496881418587531 15123565343245322127881297)
                  ·
                    refine ⟨11342674007433991595910973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15123565343245322127881297 11342674007433991595910973)
                    ·
                      refine ⟨4253502752787746848466615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342674007433991595910973 4253502752787746848466615)
                      ·
                        rfl

theorem cell23_8283667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 3].length) (baseStart_8283667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283667 prefixEnd_8283667 := by exact prefixLift 8283667
  have htrace : WordTrace (prefixWord ++ tailWord_8283667) baseStart_8283667 baseEnd_8283667 := by
    simpa [prefixWord, tailWord_8283667, baseEnd_8283667] using wordTrace_append hprefix tailTrace_8283667
  have hstable : (prefixWord ++ tailWord_8283667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283667).length < 2 ^ (prefixWord ++ tailWord_8283667).sum := by decide
  have hdescent : baseEnd_8283667 < baseStart_8283667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283681 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_8283681 : Nat := 118140960795 + 8283681 * 2 ^ 59
def prefixEnd_8283681 : Nat := 4983230072969 + 3 ^ 40 * 8283681 * 2
def baseEnd_8283681 : Nat := 4253509941516909793691551

theorem tailTrace_8283681 : CollatzResearch.WordTrace tailWord_8283681 prefixEnd_8283681 4253509941516909793691551 := by
  unfold tailWord_8283681
  simp only [CollatzResearch.WordTrace]
  refine ⟨302130667102645951926698897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201420444735097301284465931 302130667102645951926698897)
  ·
    refine ⟨226598000326984463945024173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302130667102645951926698897 226598000326984463945024173)
    ·
      refine ⟨84974250122619173979384065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226598000326984463945024173 84974250122619173979384065)
      ·
        refine ⟨63730687591964380484538049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84974250122619173979384065 63730687591964380484538049)
        ·
          refine ⟨47798015693973285363403537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63730687591964380484538049 47798015693973285363403537)
          ·
            refine ⟨35848511770479964022552653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47798015693973285363403537 35848511770479964022552653)
            ·
              refine ⟨13443191913929986508457245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35848511770479964022552653 13443191913929986508457245)
              ·
                refine ⟨5041196967723744940671467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13443191913929986508457245 5041196967723744940671467)
                ·
                  refine ⟨7561795451585617411007201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041196967723744940671467 7561795451585617411007201)
                  ·
                    refine ⟨5671346588689213058255401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561795451585617411007201 5671346588689213058255401)
                    ·
                      refine ⟨4253509941516909793691551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671346588689213058255401 4253509941516909793691551)
                      ·
                        rfl

theorem cell23_8283681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_8283681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283681 prefixEnd_8283681 := by exact prefixLift 8283681
  have htrace : WordTrace (prefixWord ++ tailWord_8283681) baseStart_8283681 baseEnd_8283681 := by
    simpa [prefixWord, tailWord_8283681, baseEnd_8283681] using wordTrace_append hprefix tailTrace_8283681
  have hstable : (prefixWord ++ tailWord_8283681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283681).length < 2 ^ (prefixWord ++ tailWord_8283681).sum := by decide
  have hdescent : baseEnd_8283681 < baseStart_8283681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283697 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_8283697 : Nat := 118140960795 + 8283697 * 2 ^ 59
def prefixEnd_8283697 : Nat := 4983230072969 + 3 ^ 40 * 8283697 * 2
def baseEnd_8283697 : Nat := 4253518157207381731091477

theorem tailTrace_8283697 : CollatzResearch.WordTrace tailWord_8283697 prefixEnd_8283697 4253518157207381731091477 := by
  unfold tailWord_8283697
  simp only [CollatzResearch.WordTrace]
  refine ⟨302131250670587986659281345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201420833780391991106187563 302131250670587986659281345)
  ·
    refine ⟨226598438002940989994461009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302131250670587986659281345 226598438002940989994461009)
    ·
      refine ⟨169948828502205742495845757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226598438002940989994461009 169948828502205742495845757)
      ·
        refine ⟨63730810688327153435942159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169948828502205742495845757 63730810688327153435942159)
        ·
          refine ⟨95596216032490730153913239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63730810688327153435942159 95596216032490730153913239)
          ·
            refine ⟨143394324048736095230869859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95596216032490730153913239 143394324048736095230869859)
            ·
              refine ⟨215091486073104142846304789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143394324048736095230869859 215091486073104142846304789)
              ·
                refine ⟨10082413409676756695920537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215091486073104142846304789 10082413409676756695920537)
                ·
                  refine ⟨7561810057257567521940403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082413409676756695920537 7561810057257567521940403)
                  ·
                    refine ⟨11342715085886351282910605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7561810057257567521940403 11342715085886351282910605)
                    ·
                      refine ⟨4253518157207381731091477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342715085886351282910605 4253518157207381731091477)
                      ·
                        rfl

theorem cell23_8283697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_8283697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283697 prefixEnd_8283697 := by exact prefixLift 8283697
  have htrace : WordTrace (prefixWord ++ tailWord_8283697) baseStart_8283697 baseEnd_8283697 := by
    simpa [prefixWord, tailWord_8283697, baseEnd_8283697] using wordTrace_append hprefix tailTrace_8283697
  have hstable : (prefixWord ++ tailWord_8283697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283697).length < 2 ^ (prefixWord ++ tailWord_8283697).sum := by decide
  have hdescent : baseEnd_8283697 < baseStart_8283697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283718 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_8283718 : Nat := 118140960795 + 8283718 * 2 ^ 59
def prefixEnd_8283718 : Nat := 4983230072969 + 3 ^ 40 * 8283718 * 2
def baseEnd_8283718 : Nat := 4253528940301126148928881

theorem tailTrace_8283718 : CollatzResearch.WordTrace tailWord_8283718 prefixEnd_8283718 4253528940301126148928881 := by
  unfold tailWord_8283718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441625518859747101431119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201421344402341271497197205 9441625518859747101431119)
  ·
    refine ⟨14162438278289620652146679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441625518859747101431119 14162438278289620652146679)
    ·
      refine ⟨21243657417434430978220019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162438278289620652146679 21243657417434430978220019)
      ·
        refine ⟨31865486126151646467330029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243657417434430978220019 31865486126151646467330029)
        ·
          refine ⟨11949557297306867425248761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31865486126151646467330029 11949557297306867425248761)
          ·
            refine ⟨8962167972980150568936571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11949557297306867425248761 8962167972980150568936571)
            ·
              refine ⟨13443251959470225853404857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962167972980150568936571 13443251959470225853404857)
              ·
                refine ⟨10082438969602669390053643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443251959470225853404857 10082438969602669390053643)
                ·
                  refine ⟨15123658454404004085080465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10082438969602669390053643 15123658454404004085080465)
                  ·
                    refine ⟨11342743840803003063810349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15123658454404004085080465 11342743840803003063810349)
                    ·
                      refine ⟨4253528940301126148928881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342743840803003063810349 4253528940301126148928881)
                      ·
                        rfl

theorem cell23_8283718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_8283718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283718 prefixEnd_8283718 := by exact prefixLift 8283718
  have htrace : WordTrace (prefixWord ++ tailWord_8283718) baseStart_8283718 baseEnd_8283718 := by
    simpa [prefixWord, tailWord_8283718, baseEnd_8283718] using wordTrace_append hprefix tailTrace_8283718
  have hstable : (prefixWord ++ tailWord_8283718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283718).length < 2 ^ (prefixWord ++ tailWord_8283718).sum := by decide
  have hdescent : baseEnd_8283718 < baseStart_8283718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283724 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_8283724 : Nat := 118140960795 + 8283724 * 2 ^ 59
def prefixEnd_8283724 : Nat := 4983230072969 + 3 ^ 40 * 8283724 * 2
def baseEnd_8283724 : Nat := 4253532021185053125453853

theorem tailTrace_8283724 : CollatzResearch.WordTrace tailWord_8283724 prefixEnd_8283724 4253532021185053125453853 := by
  unfold tailWord_8283724
  simp only [CollatzResearch.WordTrace]
  refine ⟨151066117720745085135257113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201421490294326780180342817 151066117720745085135257113)
  ·
    refine ⟨113299588290558813851442835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151066117720745085135257113 113299588290558813851442835)
    ·
      refine ⟨169949382435838220777164253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113299588290558813851442835 169949382435838220777164253)
      ·
        refine ⟨63731018413439332791436595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169949382435838220777164253 63731018413439332791436595)
        ·
          refine ⟨95596527620158999187154893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63731018413439332791436595 95596527620158999187154893)
          ·
            refine ⟨35848697857559624695183085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95596527620158999187154893 35848697857559624695183085)
            ·
              refine ⟨13443261696584859260693657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35848697857559624695183085 13443261696584859260693657)
              ·
                refine ⟨10082446272438644445520243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443261696584859260693657 10082446272438644445520243)
                ·
                  refine ⟨15123669408657966668280365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10082446272438644445520243 15123669408657966668280365)
                  ·
                    refine ⟨5671376028246737500605137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15123669408657966668280365 5671376028246737500605137)
                    ·
                      refine ⟨4253532021185053125453853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671376028246737500605137 4253532021185053125453853)
                      ·
                        rfl

theorem cell23_8283724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_8283724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283724 prefixEnd_8283724 := by exact prefixLift 8283724
  have htrace : WordTrace (prefixWord ++ tailWord_8283724) baseStart_8283724 baseEnd_8283724 := by
    simpa [prefixWord, tailWord_8283724, baseEnd_8283724] using wordTrace_append hprefix tailTrace_8283724
  have hstable : (prefixWord ++ tailWord_8283724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283724).length < 2 ^ (prefixWord ++ tailWord_8283724).sum := by decide
  have hdescent : baseEnd_8283724 < baseStart_8283724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283737 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 6, 2, 2]
def baseStart_8283737 : Nat := 118140960795 + 8283737 * 2 ^ 59
def prefixEnd_8283737 : Nat := 4983230072969 + 3 ^ 40 * 8283737 * 2
def baseEnd_8283737 : Nat := 4253538696433561574591293

theorem tailTrace_8283737 : CollatzResearch.WordTrace tailWord_8283737 prefixEnd_8283737 4253538696433561574591293 := by
  unfold tailWord_8283737
  simp only [CollatzResearch.WordTrace]
  refine ⟨302132709590443073490737465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201421806393628715660491643 302132709590443073490737465)
  ·
    refine ⟨226599532192832305118053099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302132709590443073490737465 226599532192832305118053099)
    ·
      refine ⟨339899298289248457677079649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226599532192832305118053099 339899298289248457677079649)
      ·
        refine ⟨254924473716936343257809737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339899298289248457677079649 254924473716936343257809737)
        ·
          refine ⟨191193355287702257443357303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254924473716936343257809737 191193355287702257443357303)
          ·
            refine ⟨286790032931553386165035955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191193355287702257443357303 286790032931553386165035955)
            ·
              refine ⟨430185049397330079247553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286790032931553386165035955 430185049397330079247553933)
              ·
                refine ⟨161319393523998779717832725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430185049397330079247553933 161319393523998779717832725)
                ·
                  refine ⟨7561846571437442799273409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161319393523998779717832725 7561846571437442799273409)
                  ·
                    refine ⟨5671384928578082099455057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7561846571437442799273409 5671384928578082099455057)
                    ·
                      refine ⟨4253538696433561574591293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671384928578082099455057 4253538696433561574591293)
                      ·
                        rfl

theorem cell23_8283737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_8283737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283737 prefixEnd_8283737 := by exact prefixLift 8283737
  have htrace : WordTrace (prefixWord ++ tailWord_8283737) baseStart_8283737 baseEnd_8283737 := by
    simpa [prefixWord, tailWord_8283737, baseEnd_8283737] using wordTrace_append hprefix tailTrace_8283737
  have hstable : (prefixWord ++ tailWord_8283737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283737).length < 2 ^ (prefixWord ++ tailWord_8283737).sum := by decide
  have hdescent : baseEnd_8283737 < baseStart_8283737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283753 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_8283753 : Nat := 118140960795 + 8283753 * 2 ^ 59
def prefixEnd_8283753 : Nat := 4983230072969 + 3 ^ 40 * 8283753 * 2
def baseEnd_8283753 : Nat := 4253546912124033511991219

theorem tailTrace_8283753 : CollatzResearch.WordTrace tailWord_8283753 prefixEnd_8283753 4253546912124033511991219 := by
  unfold tailWord_8283753
  simp only [CollatzResearch.WordTrace]
  refine ⟨302133293158385108223319913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201422195438923405482213275 302133293158385108223319913)
  ·
    refine ⟨226599969868788831167489935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302133293158385108223319913 226599969868788831167489935)
    ·
      refine ⟨339899954803183246751234903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226599969868788831167489935 339899954803183246751234903)
      ·
        refine ⟨509849932204774870126852355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339899954803183246751234903 509849932204774870126852355)
        ·
          refine ⟨764774898307162305190278533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509849932204774870126852355 764774898307162305190278533)
          ·
            refine ⟨143395293432592932223177225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 764774898307162305190278533 143395293432592932223177225)
            ·
              refine ⟨107546470074444699167382919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143395293432592932223177225 107546470074444699167382919)
              ·
                refine ⟨161319705111667048751074379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107546470074444699167382919 161319705111667048751074379)
                ·
                  refine ⟨241979557667500573126611569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161319705111667048751074379 241979557667500573126611569)
                  ·
                    refine ⟨181484668250625429844958677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 241979557667500573126611569 181484668250625429844958677)
                    ·
                      refine ⟨4253546912124033511991219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181484668250625429844958677 4253546912124033511991219)
                      ·
                        rfl

theorem cell23_8283753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_8283753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283753 prefixEnd_8283753 := by exact prefixLift 8283753
  have htrace : WordTrace (prefixWord ++ tailWord_8283753) baseStart_8283753 baseEnd_8283753 := by
    simpa [prefixWord, tailWord_8283753, baseEnd_8283753] using wordTrace_append hprefix tailTrace_8283753
  have hstable : (prefixWord ++ tailWord_8283753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283753).length < 2 ^ (prefixWord ++ tailWord_8283753).sum := by decide
  have hdescent : baseEnd_8283753 < baseStart_8283753 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283827 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 2, 4, 2]
def baseStart_8283827 : Nat := 118140960795 + 8283827 * 2 ^ 59
def prefixEnd_8283827 : Nat := 4983230072969 + 3 ^ 40 * 8283827 * 2
def baseEnd_8283827 : Nat := 4253584909692466222465879

theorem tailTrace_8283827 : CollatzResearch.WordTrace tailWord_8283827 prefixEnd_8283827 4253584909692466222465879 := by
  unfold tailWord_8283827
  simp only [CollatzResearch.WordTrace]
  refine ⟨302135992160117018861513735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201423994773411345907675823 302135992160117018861513735)
  ·
    refine ⟨453203988240175528292270603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302135992160117018861513735 453203988240175528292270603)
    ·
      refine ⟨679805982360263292438405905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453203988240175528292270603 679805982360263292438405905)
      ·
        refine ⟨509854486770197469328804429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679805982360263292438405905 509854486770197469328804429)
        ·
          refine ⟨191195432538824050998301661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 509854486770197469328804429 191195432538824050998301661)
          ·
            refine ⟨71698287202059019124363123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191195432538824050998301661 71698287202059019124363123)
            ·
              refine ⟨107547430803088528686544685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71698287202059019124363123 107547430803088528686544685)
              ·
                refine ⟨40330286551158198257454257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107547430803088528686544685 40330286551158198257454257)
                ·
                  refine ⟨30247714913368648693090693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40330286551158198257454257 30247714913368648693090693)
                  ·
                    refine ⟨5671446546256621629954505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30247714913368648693090693 5671446546256621629954505)
                    ·
                      refine ⟨4253584909692466222465879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671446546256621629954505 4253584909692466222465879)
                      ·
                        rfl

theorem cell23_8283827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4, 2].length) (baseStart_8283827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283827 prefixEnd_8283827 := by exact prefixLift 8283827
  have htrace : WordTrace (prefixWord ++ tailWord_8283827) baseStart_8283827 baseEnd_8283827 := by
    simpa [prefixWord, tailWord_8283827, baseEnd_8283827] using wordTrace_append hprefix tailTrace_8283827
  have hstable : (prefixWord ++ tailWord_8283827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283827).length < 2 ^ (prefixWord ++ tailWord_8283827).sum := by decide
  have hdescent : baseEnd_8283827 < baseStart_8283827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283837 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_8283837 : Nat := 118140960795 + 8283837 * 2 ^ 59
def prefixEnd_8283837 : Nat := 4983230072969 + 3 ^ 40 * 8283837 * 2
def baseEnd_8283837 : Nat := 1417863348166337061113611

theorem tailTrace_8283837 : CollatzResearch.WordTrace tailWord_8283837 prefixEnd_8283837 1417863348166337061113611 := by
  unfold tailWord_8283837
  simp only [CollatzResearch.WordTrace]
  refine ⟨302136356890080790569377765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201424237926720527046251843 302136356890080790569377765)
  ·
    refine ⟨56650566916890148231758331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302136356890080790569377765 56650566916890148231758331)
    ·
      refine ⟨84975850375335222347637497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56650566916890148231758331 84975850375335222347637497)
      ·
        refine ⟨63731887781501416760728123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84975850375335222347637497 63731887781501416760728123)
        ·
          refine ⟨95597831672252125141092185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63731887781501416760728123 95597831672252125141092185)
          ·
            refine ⟨71698373754189093855819139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95597831672252125141092185 71698373754189093855819139)
            ·
              refine ⟨107547560631283640783728709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71698373754189093855819139 107547560631283640783728709)
              ·
                refine ⟨20165167618365682646949133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107547560631283640783728709 20165167618365682646949133)
                ·
                  refine ⟨7561937856887130992605925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20165167618365682646949133 7561937856887130992605925)
                  ·
                    refine ⟨1417863348166337061113611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561937856887130992605925 1417863348166337061113611)
                    ·
                      rfl

theorem cell23_8283837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_8283837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283837 prefixEnd_8283837 := by exact prefixLift 8283837
  have htrace : WordTrace (prefixWord ++ tailWord_8283837) baseStart_8283837 baseEnd_8283837 := by
    simpa [prefixWord, tailWord_8283837, baseEnd_8283837] using wordTrace_append hprefix tailTrace_8283837
  have hstable : (prefixWord ++ tailWord_8283837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283837).length < 2 ^ (prefixWord ++ tailWord_8283837).sum := by decide
  have hdescent : baseEnd_8283837 < baseStart_8283837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283840 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_8283840 : Nat := 118140960795 + 8283840 * 2 ^ 59
def prefixEnd_8283840 : Nat := 4983230072969 + 3 ^ 40 * 8283840 * 2
def baseEnd_8283840 : Nat := 4253591584940974671603319

theorem tailTrace_8283840 : CollatzResearch.WordTrace tailWord_8283840 prefixEnd_8283840 4253591584940974671603319 := by
  unfold tailWord_8283840
  simp only [CollatzResearch.WordTrace]
  refine ⟨151068233154534961040868487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201424310872713281387824649 151068233154534961040868487)
  ·
    refine ⟨226602349731802441561302731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151068233154534961040868487 226602349731802441561302731)
    ·
      refine ⟨339903524597703662341954097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226602349731802441561302731 339903524597703662341954097)
      ·
        refine ⟨254927643448277746756465573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339903524597703662341954097 254927643448277746756465573)
        ·
          refine ⟨47798933146552077516837295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254927643448277746756465573 47798933146552077516837295)
          ·
            refine ⟨71698399719828116275255943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47798933146552077516837295 71698399719828116275255943)
            ·
              refine ⟨107547599579742174412883915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71698399719828116275255943 107547599579742174412883915)
              ·
                refine ⟨161321399369613261619325873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107547599579742174412883915 161321399369613261619325873)
                ·
                  refine ⟨120991049527209946214494405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161321399369613261619325873 120991049527209946214494405)
                  ·
                    refine ⟨22685821786351864915217701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120991049527209946214494405 22685821786351864915217701)
                    ·
                      refine ⟨4253591584940974671603319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22685821786351864915217701 4253591584940974671603319)
                      ·
                        rfl

theorem cell23_8283840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_8283840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283840 prefixEnd_8283840 := by exact prefixLift 8283840
  have htrace : WordTrace (prefixWord ++ tailWord_8283840) baseStart_8283840 baseEnd_8283840 := by
    simpa [prefixWord, tailWord_8283840, baseEnd_8283840] using wordTrace_append hprefix tailTrace_8283840
  have hstable : (prefixWord ++ tailWord_8283840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283840).length < 2 ^ (prefixWord ++ tailWord_8283840).sum := by decide
  have hdescent : baseEnd_8283840 < baseStart_8283840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283847 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_8283847 : Nat := 118140960795 + 8283847 * 2 ^ 59
def prefixEnd_8283847 : Nat := 4983230072969 + 3 ^ 40 * 8283847 * 2
def baseEnd_8283847 : Nat := 4253595179305556144215787

theorem tailTrace_8283847 : CollatzResearch.WordTrace tailWord_8283847 prefixEnd_8283847 4253595179305556144215787 := by
  unfold tailWord_8283847
  simp only [CollatzResearch.WordTrace]
  refine ⟨302136721620044562277241795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201424481080029708184827863 302136721620044562277241795)
  ·
    refine ⟨453205082430066843415862693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302136721620044562277241795 453205082430066843415862693)
    ·
      refine ⟨84975952955637533140474255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453205082430066843415862693 84975952955637533140474255)
      ·
        refine ⟨127463929433456299710711383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84975952955637533140474255 127463929433456299710711383)
        ·
          refine ⟨191195894150184449566067075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127463929433456299710711383 191195894150184449566067075)
          ·
            refine ⟨286793841225276674349100613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191195894150184449566067075 286793841225276674349100613)
            ·
              refine ⟨53773845229739376440456365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286793841225276674349100613 53773845229739376440456365)
              ·
                refine ⟨20165191961152266165171137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53773845229739376440456365 20165191961152266165171137)
                ·
                  refine ⟨15123893970864199623878353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20165191961152266165171137 15123893970864199623878353)
                  ·
                    refine ⟨11342920478148149717908765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15123893970864199623878353 11342920478148149717908765)
                    ·
                      refine ⟨4253595179305556144215787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11342920478148149717908765 4253595179305556144215787)
                      ·
                        rfl

theorem cell23_8283847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_8283847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283847 prefixEnd_8283847 := by exact prefixLift 8283847
  have htrace : WordTrace (prefixWord ++ tailWord_8283847) baseStart_8283847 baseEnd_8283847 := by
    simpa [prefixWord, tailWord_8283847, baseEnd_8283847] using wordTrace_append hprefix tailTrace_8283847
  have hstable : (prefixWord ++ tailWord_8283847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283847).length < 2 ^ (prefixWord ++ tailWord_8283847).sum := by decide
  have hdescent : baseEnd_8283847 < baseStart_8283847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283871 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 1, 4]
def baseStart_8283871 : Nat := 118140960795 + 8283871 * 2 ^ 59
def prefixEnd_8283871 : Nat := 4983230072969 + 3 ^ 40 * 8283871 * 2
def baseEnd_8283871 : Nat := 1417869167613754683438559

theorem tailTrace_8283871 : CollatzResearch.WordTrace tailWord_8283871 prefixEnd_8283871 1417869167613754683438559 := by
  unfold tailWord_8283871
  simp only [CollatzResearch.WordTrace]
  refine ⟨302137596971957614376115467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201425064647971742917410311 302137596971957614376115467)
  ·
    refine ⟨453206395457936421564173201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302137596971957614376115467 453206395457936421564173201)
    ·
      refine ⟨339904796593452316173129901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453206395457936421564173201 339904796593452316173129901)
      ·
        refine ⟨127464298722544618564923713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339904796593452316173129901 127464298722544618564923713)
        ·
          refine ⟨95598224041908463923692785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127464298722544618564923713 95598224041908463923692785)
          ·
            refine ⟨71698668031431347942769589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95598224041908463923692785 71698668031431347942769589)
            ·
              refine ⟨6721750127946688869634649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71698668031431347942769589 6721750127946688869634649)
              ·
                refine ⟨5041312595960016652225987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6721750127946688869634649 5041312595960016652225987)
                ·
                  refine ⟨7561968893940024978338981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041312595960016652225987 7561968893940024978338981)
                  ·
                    refine ⟨1417869167613754683438559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7561968893940024978338981 1417869167613754683438559)
                    ·
                      rfl

theorem cell23_8283871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 4].length) (baseStart_8283871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283871 prefixEnd_8283871 := by exact prefixLift 8283871
  have htrace : WordTrace (prefixWord ++ tailWord_8283871) baseStart_8283871 baseEnd_8283871 := by
    simpa [prefixWord, tailWord_8283871, baseEnd_8283871] using wordTrace_append hprefix tailTrace_8283871
  have hstable : (prefixWord ++ tailWord_8283871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283871).length < 2 ^ (prefixWord ++ tailWord_8283871).sum := by decide
  have hdescent : baseEnd_8283871 < baseStart_8283871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283928 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 1, 1, 3]
def baseStart_8283928 : Nat := 118140960795 + 8283928 * 2 ^ 59
def prefixEnd_8283928 : Nat := 4983230072969 + 3 ^ 40 * 8283928 * 2
def baseEnd_8283928 : Nat := 4253636771238570327302915

theorem tailTrace_8283928 : CollatzResearch.WordTrace tailWord_8283928 prefixEnd_8283928 4253636771238570327302915 := by
  unfold tailWord_8283928
  simp only [CollatzResearch.WordTrace]
  refine ⟨151069837966375556555470219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201426450621834075407293625 151069837966375556555470219)
  ·
    refine ⟨226604756949563334833205329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151069837966375556555470219 226604756949563334833205329)
    ·
      refine ⟨169953567712172501124903997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226604756949563334833205329 169953567712172501124903997)
      ·
        refine ⟨63732587892064687921838999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169953567712172501124903997 63732587892064687921838999)
        ·
          refine ⟨95598881838097031882758499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63732587892064687921838999 95598881838097031882758499)
          ·
            refine ⟨143398322757145547824137749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95598881838097031882758499 143398322757145547824137749)
            ·
              refine ⟨6721796379241197554256457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143398322757145547824137749 6721796379241197554256457)
              ·
                refine ⟨5041347284430898165692343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6721796379241197554256457 5041347284430898165692343)
                ·
                  refine ⟨7562020926646347248538515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041347284430898165692343 7562020926646347248538515)
                  ·
                    refine ⟨11343031389969520872807773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7562020926646347248538515 11343031389969520872807773)
                    ·
                      refine ⟨4253636771238570327302915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343031389969520872807773 4253636771238570327302915)
                      ·
                        rfl

theorem cell23_8283928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_8283928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283928 prefixEnd_8283928 := by exact prefixLift 8283928
  have htrace : WordTrace (prefixWord ++ tailWord_8283928) baseStart_8283928 baseEnd_8283928 := by
    simpa [prefixWord, tailWord_8283928, baseEnd_8283928] using wordTrace_append hprefix tailTrace_8283928
  have hstable : (prefixWord ++ tailWord_8283928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283928).length < 2 ^ (prefixWord ++ tailWord_8283928).sum := by decide
  have hdescent : baseEnd_8283928 < baseStart_8283928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283944 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 1, 6]
def baseStart_8283944 : Nat := 118140960795 + 8283944 * 2 ^ 59
def prefixEnd_8283944 : Nat := 4983230072969 + 3 ^ 40 * 8283944 * 2
def baseEnd_8283944 : Nat := 1417881662309680754900947

theorem tailTrace_8283944 : CollatzResearch.WordTrace tailWord_8283944 prefixEnd_8283944 1417881662309680754900947 := by
  unfold tailWord_8283944
  simp only [CollatzResearch.WordTrace]
  refine ⟨151070129750346573921761443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201426839667128765229015257 151070129750346573921761443)
  ·
    refine ⟨226605194625519860882642165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151070129750346573921761443 226605194625519860882642165)
    ·
      refine ⟨21244236996142486957747703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226605194625519860882642165 21244236996142486957747703)
      ·
        refine ⟨31866355494213730436621555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21244236996142486957747703 31866355494213730436621555)
        ·
          refine ⟨47799533241320595654932333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31866355494213730436621555 47799533241320595654932333)
          ·
            refine ⟨17924824965495223370599625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47799533241320595654932333 17924824965495223370599625)
            ·
              refine ⟨13443618724121417527949719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17924824965495223370599625 13443618724121417527949719)
              ·
                refine ⟨20165428086182126291924579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13443618724121417527949719 20165428086182126291924579)
                ·
                  refine ⟨30248142129273189437886869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20165428086182126291924579 30248142129273189437886869)
                  ·
                    refine ⟨1417881662309680754900947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30248142129273189437886869 1417881662309680754900947)
                    ·
                      rfl

theorem cell23_8283944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_8283944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283944 prefixEnd_8283944 := by exact prefixLift 8283944
  have htrace : WordTrace (prefixWord ++ tailWord_8283944) baseStart_8283944 baseEnd_8283944 := by
    simpa [prefixWord, tailWord_8283944, baseEnd_8283944] using wordTrace_append hprefix tailTrace_8283944
  have hstable : (prefixWord ++ tailWord_8283944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283944).length < 2 ^ (prefixWord ++ tailWord_8283944).sum := by decide
  have hdescent : baseEnd_8283944 < baseStart_8283944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283954 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_8283954 : Nat := 118140960795 + 8283954 * 2 ^ 59
def prefixEnd_8283954 : Nat := 4983230072969 + 3 ^ 40 * 8283954 * 2
def baseEnd_8283954 : Nat := 4253650121735587225577795

theorem tailTrace_8283954 : CollatzResearch.WordTrace tailWord_8283954 prefixEnd_8283954 4253650121735587225577795 := by
  unfold tailWord_8283954
  simp only [CollatzResearch.WordTrace]
  refine ⟨75535156057664229887846729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201427082820437946367591277 75535156057664229887846729)
  ·
    refine ⟨56651367043248172415885047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75535156057664229887846729 56651367043248172415885047)
    ·
      refine ⟨84977050564872258623827571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56651367043248172415885047 84977050564872258623827571)
      ·
        refine ⟨127465575847308387935741357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84977050564872258623827571 127465575847308387935741357)
        ·
          refine ⟨47799590942740645475903009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127465575847308387935741357 47799590942740645475903009)
          ·
            refine ⟨35849693207055484106927257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47799590942740645475903009 35849693207055484106927257)
            ·
              refine ⟨26887269905291613080195443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35849693207055484106927257 26887269905291613080195443)
              ·
                refine ⟨40330904857937419620293165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26887269905291613080195443 40330904857937419620293165)
                ·
                  refine ⟨15124089321726532357609937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40330904857937419620293165 15124089321726532357609937)
                  ·
                    refine ⟨11343066991294899268207453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15124089321726532357609937 11343066991294899268207453)
                    ·
                      refine ⟨4253650121735587225577795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343066991294899268207453 4253650121735587225577795)
                      ·
                        rfl

theorem cell23_8283954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_8283954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283954 prefixEnd_8283954 := by exact prefixLift 8283954
  have htrace : WordTrace (prefixWord ++ tailWord_8283954) baseStart_8283954 baseEnd_8283954 := by
    simpa [prefixWord, tailWord_8283954, baseEnd_8283954] using wordTrace_append hprefix tailTrace_8283954
  have hstable : (prefixWord ++ tailWord_8283954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283954).length < 2 ^ (prefixWord ++ tailWord_8283954).sum := by decide
  have hdescent : baseEnd_8283954 < baseStart_8283954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8283971 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 1, 2, 3]
def baseStart_8283971 : Nat := 118140960795 + 8283971 * 2 ^ 59
def prefixEnd_8283971 : Nat := 4983230072969 + 3 ^ 40 * 8283971 * 2
def baseEnd_8283971 : Nat := 4253658850906713659065217

theorem tailTrace_8283971 : CollatzResearch.WordTrace tailWord_8283971 prefixEnd_8283971 4253658850906713659065217 := by
  unfold tailWord_8283971
  simp only [CollatzResearch.WordTrace]
  refine ⟨302141244271595331454755767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201427496181063554303170511 302141244271595331454755767)
  ·
    refine ⟨453211866407392997182133651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302141244271595331454755767 453211866407392997182133651)
    ·
      refine ⟨679817799611089495773200477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453211866407392997182133651 679817799611089495773200477)
      ·
        refine ⟨254931674854158560914950179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 679817799611089495773200477 254931674854158560914950179)
        ·
          refine ⟨382397512281237841372425269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254931674854158560914950179 382397512281237841372425269)
          ·
            refine ⟨35849766776366047628664869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 382397512281237841372425269 35849766776366047628664869)
            ·
              refine ⟨6721831270568633930374663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35849766776366047628664869 6721831270568633930374663)
              ·
                refine ⟨10082746905852950895561995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721831270568633930374663 10082746905852950895561995)
                ·
                  refine ⟨15124120358779426343342993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10082746905852950895561995 15124120358779426343342993)
                  ·
                    refine ⟨11343090269084569757507245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15124120358779426343342993 11343090269084569757507245)
                    ·
                      refine ⟨4253658850906713659065217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343090269084569757507245 4253658850906713659065217)
                      ·
                        rfl

theorem cell23_8283971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_8283971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8283971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8283971 prefixEnd_8283971 := by exact prefixLift 8283971
  have htrace : WordTrace (prefixWord ++ tailWord_8283971) baseStart_8283971 baseEnd_8283971 := by
    simpa [prefixWord, tailWord_8283971, baseEnd_8283971] using wordTrace_append hprefix tailTrace_8283971
  have hstable : (prefixWord ++ tailWord_8283971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8283971).length < 2 ^ (prefixWord ++ tailWord_8283971).sum := by decide
  have hdescent : baseEnd_8283971 < baseStart_8283971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8283971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284014 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_8284014 : Nat := 118140960795 + 8284014 * 2 ^ 59
def prefixEnd_8284014 : Nat := 4983230072969 + 3 ^ 40 * 8284014 * 2
def baseEnd_8284014 : Nat := 4253680930574856990827519

theorem tailTrace_8284014 : CollatzResearch.WordTrace tailWord_8284014 prefixEnd_8284014 4253680930574856990827519 := by
  unfold tailWord_8284014
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767851576304943724821387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201428541740293033199047397 37767851576304943724821387)
  ·
    refine ⟨56651777364457415587232081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37767851576304943724821387 56651777364457415587232081)
    ·
      refine ⟨42488833023343061690424061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56651777364457415587232081 42488833023343061690424061)
      ·
        refine ⟨15933312383753648133909023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42488833023343061690424061 15933312383753648133909023)
        ·
          refine ⟨23899968575630472200863535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933312383753648133909023 23899968575630472200863535)
          ·
            refine ⟨35849952863445708301295303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23899968575630472200863535 35849952863445708301295303)
            ·
              refine ⟨53774929295168562451942955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35849952863445708301295303 53774929295168562451942955)
              ·
                refine ⟨80662393942752843677914433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53774929295168562451942955 80662393942752843677914433)
                ·
                  refine ⟨60496795457064632758435825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80662393942752843677914433 60496795457064632758435825)
                  ·
                    refine ⟨45372596592798474568826869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60496795457064632758435825 45372596592798474568826869)
                    ·
                      refine ⟨4253680930574856990827519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45372596592798474568826869 4253680930574856990827519)
                      ·
                        rfl

theorem cell23_8284014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_8284014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284014 prefixEnd_8284014 := by exact prefixLift 8284014
  have htrace : WordTrace (prefixWord ++ tailWord_8284014) baseStart_8284014 baseEnd_8284014 := by
    simpa [prefixWord, tailWord_8284014, baseEnd_8284014] using wordTrace_append hprefix tailTrace_8284014
  have hstable : (prefixWord ++ tailWord_8284014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284014).length < 2 ^ (prefixWord ++ tailWord_8284014).sum := by decide
  have hdescent : baseEnd_8284014 < baseStart_8284014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284027 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3]
def baseStart_8284027 : Nat := 118140960795 + 8284027 * 2 ^ 59
def prefixEnd_8284027 : Nat := 4983230072969 + 3 ^ 40 * 8284027 * 2
def baseEnd_8284027 : Nat := 4253687605823365439964959

theorem tailTrace_8284027 : CollatzResearch.WordTrace tailWord_8284027 prefixEnd_8284027 4253687605823365439964959 := by
  unfold tailWord_8284027
  simp only [CollatzResearch.WordTrace]
  refine ⟨302143286759392453018794335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201428857839594968679196223 302143286759392453018794335)
  ·
    refine ⟨453214930139088679528191503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302143286759392453018794335 453214930139088679528191503)
    ·
      refine ⟨679822395208633019292287255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453214930139088679528191503 679822395208633019292287255)
      ·
        refine ⟨1019733592812949528938430883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679822395208633019292287255 1019733592812949528938430883)
        ·
          refine ⟨1529600389219424293407646325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019733592812949528938430883 1529600389219424293407646325)
          ·
            refine ⟨143400036489321027506966843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1529600389219424293407646325 143400036489321027506966843)
            ·
              refine ⟨215100054733981541260450265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143400036489321027506966843 215100054733981541260450265)
              ·
                refine ⟨161325041050486155945337699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215100054733981541260450265 161325041050486155945337699)
                ·
                  refine ⟨241987561575729233918006549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161325041050486155945337699 241987561575729233918006549)
                  ·
                    refine ⟨11343166948862307839906557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 241987561575729233918006549 11343166948862307839906557)
                    ·
                      refine ⟨4253687605823365439964959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343166948862307839906557 4253687605823365439964959)
                      ·
                        rfl

theorem cell23_8284027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 3].length) (baseStart_8284027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284027 prefixEnd_8284027 := by exact prefixLift 8284027
  have htrace : WordTrace (prefixWord ++ tailWord_8284027) baseStart_8284027 baseEnd_8284027 := by
    simpa [prefixWord, tailWord_8284027, baseEnd_8284027] using wordTrace_append hprefix tailTrace_8284027
  have hstable : (prefixWord ++ tailWord_8284027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284027).length < 2 ^ (prefixWord ++ tailWord_8284027).sum := by decide
  have hdescent : baseEnd_8284027 < baseStart_8284027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284041 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 4, 2, 2]
def baseStart_8284041 : Nat := 118140960795 + 8284041 * 2 ^ 59
def prefixEnd_8284041 : Nat := 4983230072969 + 3 ^ 40 * 8284041 * 2
def baseEnd_8284041 : Nat := 4253694794552528385189895

theorem tailTrace_8284041 : CollatzResearch.WordTrace tailWord_8284041 prefixEnd_8284041 4253694794552528385189895 := by
  unfold tailWord_8284041
  simp only [CollatzResearch.WordTrace]
  refine ⟨302143797381341733409803977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201429198254227822273202651 302143797381341733409803977)
  ·
    refine ⟨226607848036006300057352983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302143797381341733409803977 226607848036006300057352983)
    ·
      refine ⟨339911772054009450086029475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226607848036006300057352983 339911772054009450086029475)
      ·
        refine ⟨509867658081014175129044213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339911772054009450086029475 509867658081014175129044213)
        ·
          refine ⟨47800092945095078918347895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 509867658081014175129044213 47800092945095078918347895)
          ·
            refine ⟨71700139417642618377521843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47800092945095078918347895 71700139417642618377521843)
            ·
              refine ⟨107550209126463927566282765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71700139417642618377521843 107550209126463927566282765)
              ·
                refine ⟨40331328422423972837356037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107550209126463927566282765 40331328422423972837356037)
                ·
                  refine ⟨7562124079204494907004257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40331328422423972837356037 7562124079204494907004257)
                  ·
                    refine ⟨5671593059403371180253193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7562124079204494907004257 5671593059403371180253193)
                    ·
                      refine ⟨4253694794552528385189895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671593059403371180253193 4253694794552528385189895)
                      ·
                        rfl

theorem cell23_8284041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 2, 2].length) (baseStart_8284041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284041 prefixEnd_8284041 := by exact prefixLift 8284041
  have htrace : WordTrace (prefixWord ++ tailWord_8284041) baseStart_8284041 baseEnd_8284041 := by
    simpa [prefixWord, tailWord_8284041, baseEnd_8284041] using wordTrace_append hprefix tailTrace_8284041
  have hstable : (prefixWord ++ tailWord_8284041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284041).length < 2 ^ (prefixWord ++ tailWord_8284041).sum := by decide
  have hdescent : baseEnd_8284041 < baseStart_8284041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284092 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_8284092 : Nat := 118140960795 + 8284092 * 2 ^ 59
def prefixEnd_8284092 : Nat := 4983230072969 + 3 ^ 40 * 8284092 * 2
def baseEnd_8284092 : Nat := 4253720982065907685652161

theorem tailTrace_8284092 : CollatzResearch.WordTrace tailWord_8284092 prefixEnd_8284092 4253720982065907685652161 := by
  unfold tailWord_8284092
  simp only [CollatzResearch.WordTrace]
  refine ⟨151072828752078484559955265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201430438336104646079940353 151072828752078484559955265)
  ·
    refine ⟨113304621564058863419966449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151072828752078484559955265 113304621564058863419966449)
    ·
      refine ⟨84978466173044147564974837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113304621564058863419966449 84978466173044147564974837)
      ·
        refine ⟨7966731203722888834216391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84978466173044147564974837 7966731203722888834216391)
        ·
          refine ⟨11950096805584333251324587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966731203722888834216391 11950096805584333251324587)
          ·
            refine ⟨17925145208376499876986881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950096805584333251324587 17925145208376499876986881)
            ·
              refine ⟨13443858906282374907740161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17925145208376499876986881 13443858906282374907740161)
              ·
                refine ⟨10082894179711781180805121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13443858906282374907740161 10082894179711781180805121)
                ·
                  refine ⟨7562170634783835885603841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10082894179711781180805121 7562170634783835885603841)
                  ·
                    refine ⟨5671627976087876914202881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7562170634783835885603841 5671627976087876914202881)
                    ·
                      refine ⟨4253720982065907685652161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671627976087876914202881 4253720982065907685652161)
                      ·
                        rfl

theorem cell23_8284092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_8284092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284092 prefixEnd_8284092 := by exact prefixLift 8284092
  have htrace : WordTrace (prefixWord ++ tailWord_8284092) baseStart_8284092 baseEnd_8284092 := by
    simpa [prefixWord, tailWord_8284092, baseEnd_8284092] using wordTrace_append hprefix tailTrace_8284092
  have hstable : (prefixWord ++ tailWord_8284092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284092).length < 2 ^ (prefixWord ++ tailWord_8284092).sum := by decide
  have hdescent : baseEnd_8284092 < baseStart_8284092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284104 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_8284104 : Nat := 118140960795 + 8284104 * 2 ^ 59
def prefixEnd_8284104 : Nat := 4983230072969 + 3 ^ 40 * 8284104 * 2
def baseEnd_8284104 : Nat := 4253727143833761638702105

theorem tailTrace_8284104 : CollatzResearch.WordTrace tailWord_8284104 prefixEnd_8284104 4253727143833761638702105 := by
  unfold tailWord_8284104
  simp only [CollatzResearch.WordTrace]
  refine ⟨151073047590056747584673683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201430730120075663446231577 151073047590056747584673683)
  ·
    refine ⟨226609571385085121377010525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151073047590056747584673683 226609571385085121377010525)
    ·
      refine ⟨84978589269406920516378947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226609571385085121377010525 84978589269406920516378947)
      ·
        refine ⟨127467883904110380774568421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84978589269406920516378947 127467883904110380774568421)
        ·
          refine ⟨23900228232020696395231579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127467883904110380774568421 23900228232020696395231579)
          ·
            refine ⟨35850342348031044592847369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23900228232020696395231579 35850342348031044592847369)
            ·
              refine ⟨26887756761023283444635527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35850342348031044592847369 26887756761023283444635527)
              ·
                refine ⟨40331635141534925166953291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26887756761023283444635527 40331635141534925166953291)
                ·
                  refine ⟨60497452712302387750429937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40331635141534925166953291 60497452712302387750429937)
                  ·
                    refine ⟨45373089534226790812822453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60497452712302387750429937 45373089534226790812822453)
                    ·
                      refine ⟨4253727143833761638702105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45373089534226790812822453 4253727143833761638702105)
                      ·
                        rfl

theorem cell23_8284104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_8284104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284104 prefixEnd_8284104 := by exact prefixLift 8284104
  have htrace : WordTrace (prefixWord ++ tailWord_8284104) baseStart_8284104 baseEnd_8284104 := by
    simpa [prefixWord, tailWord_8284104, baseEnd_8284104] using wordTrace_append hprefix tailTrace_8284104
  have hstable : (prefixWord ++ tailWord_8284104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284104).length < 2 ^ (prefixWord ++ tailWord_8284104).sum := by decide
  have hdescent : baseEnd_8284104 < baseStart_8284104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284131 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4]
def baseStart_8284131 : Nat := 118140960795 + 8284131 * 2 ^ 59
def prefixEnd_8284131 : Nat := 4983230072969 + 3 ^ 40 * 8284131 * 2
def baseEnd_8284131 : Nat := 4253741007811433033064481

theorem tailTrace_8284131 : CollatzResearch.WordTrace tailWord_8284131 prefixEnd_8284131 4253741007811433033064481 := by
  unfold tailWord_8284131
  simp only [CollatzResearch.WordTrace]
  refine ⟨302147079951015678780580247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201431386634010452520386831 302147079951015678780580247)
  ·
    refine ⟨453220619926523518170870371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302147079951015678780580247 453220619926523518170870371)
    ·
      refine ⟨679830929889785277256305557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453220619926523518170870371 679830929889785277256305557)
      ·
        refine ⟨31867074838583684871389323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 679830929889785277256305557 31867074838583684871389323)
        ·
          refine ⟨47800612257875527307083985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31867074838583684871389323 47800612257875527307083985)
          ·
            refine ⟨35850459193406645480312989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47800612257875527307083985 35850459193406645480312989)
            ·
              refine ⟨13443922197527492055117371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35850459193406645480312989 13443922197527492055117371)
              ·
                refine ⟨20165883296291238082676057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13443922197527492055117371 20165883296291238082676057)
                ·
                  refine ⟨15124412472218428562007043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20165883296291238082676057 15124412472218428562007043)
                  ·
                    refine ⟨22686618708327642843010565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15124412472218428562007043 22686618708327642843010565)
                    ·
                      refine ⟨4253741007811433033064481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22686618708327642843010565 4253741007811433033064481)
                      ·
                        rfl

theorem cell23_8284131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_8284131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284131 prefixEnd_8284131 := by exact prefixLift 8284131
  have htrace : WordTrace (prefixWord ++ tailWord_8284131) baseStart_8284131 baseEnd_8284131 := by
    simpa [prefixWord, tailWord_8284131, baseEnd_8284131] using wordTrace_append hprefix tailTrace_8284131
  have hstable : (prefixWord ++ tailWord_8284131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284131).length < 2 ^ (prefixWord ++ tailWord_8284131).sum := by decide
  have hdescent : baseEnd_8284131 < baseStart_8284131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284158 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_8284158 : Nat := 118140960795 + 8284158 * 2 ^ 59
def prefixEnd_8284158 : Nat := 4983230072969 + 3 ^ 40 * 8284158 * 2
def baseEnd_8284158 : Nat := 1417918290596368142475619

theorem tailTrace_8284158 : CollatzResearch.WordTrace tailWord_8284158 prefixEnd_8284158 1417918290596368142475619 := by
  unfold tailWord_8284158
  simp only [CollatzResearch.WordTrace]
  refine ⟨37768508090239732798976641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201432043147945241594542085 37768508090239732798976641)
  ·
    refine ⟨28326381067679799599232481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37768508090239732798976641 28326381067679799599232481)
    ·
      refine ⟨21244785800759849699424361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28326381067679799599232481 21244785800759849699424361)
      ·
        refine ⟨15933589350569887274568271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21244785800759849699424361 15933589350569887274568271)
        ·
          refine ⟨23900384025854830911852407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933589350569887274568271 23900384025854830911852407)
          ·
            refine ⟨35850576038782246367778611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23900384025854830911852407 35850576038782246367778611)
            ·
              refine ⟨53775864058173369551667917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35850576038782246367778611 53775864058173369551667917)
              ·
                refine ⟨20165949021815013581875469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53775864058173369551667917 20165949021815013581875469)
                ·
                  refine ⟨7562230883180630093203301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20165949021815013581875469 7562230883180630093203301)
                  ·
                    refine ⟨1417918290596368142475619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7562230883180630093203301 1417918290596368142475619)
                    ·
                      rfl

theorem cell23_8284158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_8284158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284158 prefixEnd_8284158 := by exact prefixLift 8284158
  have htrace : WordTrace (prefixWord ++ tailWord_8284158) baseStart_8284158 baseEnd_8284158 := by
    simpa [prefixWord, tailWord_8284158, baseEnd_8284158] using wordTrace_append hprefix tailTrace_8284158
  have hstable : (prefixWord ++ tailWord_8284158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284158).length < 2 ^ (prefixWord ++ tailWord_8284158).sum := by decide
  have hdescent : baseEnd_8284158 < baseStart_8284158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284171 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 6]
def baseStart_8284171 : Nat := 118140960795 + 8284171 * 2 ^ 59
def prefixEnd_8284171 : Nat := 4983230072969 + 3 ^ 40 * 8284171 * 2
def baseEnd_8284171 : Nat := 472640171893068097396033

theorem tailTrace_8284171 : CollatzResearch.WordTrace tailWord_8284171 prefixEnd_8284171 472640171893068097396033 := by
  unfold tailWord_8284171
  simp only [CollatzResearch.WordTrace]
  refine ⟨302148538870870765612036367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201432359247247177074690911 302148538870870765612036367)
  ·
    refine ⟨453222808306306148418054551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302148538870870765612036367 453222808306306148418054551)
    ·
      refine ⟨679834212459459222627081827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453222808306306148418054551 679834212459459222627081827)
      ·
        refine ⟨1019751318689188833940622741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679834212459459222627081827 1019751318689188833940622741)
        ·
          refine ⟨47800843063555726590966691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1019751318689188833940622741 47800843063555726590966691)
          ·
            refine ⟨71701264595333589886450037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47800843063555726590966691 71701264595333589886450037)
            ·
              refine ⟨6721993555812524051854691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71701264595333589886450037 6721993555812524051854691)
              ·
                refine ⟨10082990333718786077782037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6721993555812524051854691 10082990333718786077782037)
                ·
                  refine ⟨472640171893068097396033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10082990333718786077782037 472640171893068097396033)
                  ·
                    rfl

theorem cell23_8284171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 6].length) (baseStart_8284171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284171 prefixEnd_8284171 := by exact prefixLift 8284171
  have htrace : WordTrace (prefixWord ++ tailWord_8284171) baseStart_8284171 baseEnd_8284171 := by
    simpa [prefixWord, tailWord_8284171, baseEnd_8284171] using wordTrace_append hprefix tailTrace_8284171
  have hstable : (prefixWord ++ tailWord_8284171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284171).length < 2 ^ (prefixWord ++ tailWord_8284171).sum := by decide
  have hdescent : baseEnd_8284171 < baseStart_8284171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284174 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_8284174 : Nat := 118140960795 + 8284174 * 2 ^ 59
def prefixEnd_8284174 : Nat := 4983230072969 + 3 ^ 40 * 8284174 * 2
def baseEnd_8284174 : Nat := 4253763087479576364826783

theorem tailTrace_8284174 : CollatzResearch.WordTrace tailWord_8284174 prefixEnd_8284174 4253763087479576364826783 := by
  unfold tailWord_8284174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37768581036232487140549447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201432432193239931416263717 37768581036232487140549447)
  ·
    refine ⟨56652871554348730710824171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37768581036232487140549447 56652871554348730710824171)
    ·
      refine ⟨84979307331523096066236257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56652871554348730710824171 84979307331523096066236257)
      ·
        refine ⟨63734480498642322049677193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84979307331523096066236257 63734480498642322049677193)
        ·
          refine ⟨47800860373981741537257895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63734480498642322049677193 47800860373981741537257895)
          ·
            refine ⟨71701290560972612305886843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47800860373981741537257895 71701290560972612305886843)
            ·
              refine ⟨107551935841458918458830265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71701290560972612305886843 107551935841458918458830265)
              ·
                refine ⟨80663951881094188844122699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107551935841458918458830265 80663951881094188844122699)
                ·
                  refine ⟨120995927821641283266184049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80663951881094188844122699 120995927821641283266184049)
                  ·
                    refine ⟨90746945866230962449638037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120995927821641283266184049 90746945866230962449638037)
                    ·
                      refine ⟨4253763087479576364826783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90746945866230962449638037 4253763087479576364826783)
                      ·
                        rfl

theorem cell23_8284174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_8284174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284174 prefixEnd_8284174 := by exact prefixLift 8284174
  have htrace : WordTrace (prefixWord ++ tailWord_8284174) baseStart_8284174 baseEnd_8284174 := by
    simpa [prefixWord, tailWord_8284174, baseEnd_8284174] using wordTrace_append hprefix tailTrace_8284174
  have hstable : (prefixWord ++ tailWord_8284174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284174).length < 2 ^ (prefixWord ++ tailWord_8284174).sum := by decide
  have hdescent : baseEnd_8284174 < baseStart_8284174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284191 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 5, 2]
def baseStart_8284191 : Nat := 118140960795 + 8284191 * 2 ^ 59
def prefixEnd_8284191 : Nat := 4983230072969 + 3 ^ 40 * 8284191 * 2
def baseEnd_8284191 : Nat := 4253771816650702798314205

theorem tailTrace_8284191 : CollatzResearch.WordTrace tailWord_8284191 prefixEnd_8284191 4253771816650702798314205 := by
  unfold tailWord_8284191
  simp only [CollatzResearch.WordTrace]
  refine ⟨302149268330798309027764427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201432845553865539351842951 302149268330798309027764427)
  ·
    refine ⟨453223902496197463541646641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302149268330798309027764427 453223902496197463541646641)
    ·
      refine ⟨339917926872148097656234981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453223902496197463541646641 339917926872148097656234981)
      ·
        refine ⟨63734611288527768310544059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339917926872148097656234981 63734611288527768310544059)
        ·
          refine ⟨95601916932791652465816089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63734611288527768310544059 95601916932791652465816089)
          ·
            refine ⟨71701437699593739349362067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95601916932791652465816089 71701437699593739349362067)
            ·
              refine ⟨107552156549390609024043101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71701437699593739349362067 107552156549390609024043101)
              ·
                refine ⟨40332058706021478384016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107552156549390609024043101 40332058706021478384016163)
                ·
                  refine ⟨60498088059032217576024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40332058706021478384016163 60498088059032217576024245)
                  ·
                    refine ⟨5671695755534270397752273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60498088059032217576024245 5671695755534270397752273)
                    ·
                      refine ⟨4253771816650702798314205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671695755534270397752273 4253771816650702798314205)
                      ·
                        rfl

theorem cell23_8284191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_8284191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284191 prefixEnd_8284191 := by exact prefixLift 8284191
  have htrace : WordTrace (prefixWord ++ tailWord_8284191) baseStart_8284191 baseEnd_8284191 := by
    simpa [prefixWord, tailWord_8284191, baseEnd_8284191] using wordTrace_append hprefix tailTrace_8284191
  have hstable : (prefixWord ++ tailWord_8284191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284191).length < 2 ^ (prefixWord ++ tailWord_8284191).sum := by decide
  have hdescent : baseEnd_8284191 < baseStart_8284191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284208 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2]
def baseStart_8284208 : Nat := 118140960795 + 8284208 * 2 ^ 59
def prefixEnd_8284208 : Nat := 4983230072969 + 3 ^ 40 * 8284208 * 2
def baseEnd_8284208 : Nat := 4253780545821829231801627

theorem tailTrace_8284208 : CollatzResearch.WordTrace tailWord_8284208 prefixEnd_8284208 4253780545821829231801627 := by
  unfold tailWord_8284208
  simp only [CollatzResearch.WordTrace]
  refine ⟨151074944185868360465566639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201433258914491147287422185 151074944185868360465566639)
  ·
    refine ⟨226612416278802540698349959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151074944185868360465566639 226612416278802540698349959)
    ·
      refine ⟨339918624418203811047524939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226612416278802540698349959 339918624418203811047524939)
      ·
        refine ⟨509877936627305716571287409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339918624418203811047524939 509877936627305716571287409)
        ·
          refine ⟨382408452470479287428465557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509877936627305716571287409 382408452470479287428465557)
          ·
            refine ⟨17925396209553716598209323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382408452470479287428465557 17925396209553716598209323)
            ·
              refine ⟨26888094314330574897313985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17925396209553716598209323 26888094314330574897313985)
              ·
                refine ⟨20166070735747931172985489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26888094314330574897313985 20166070735747931172985489)
                ·
                  refine ⟨15124553051810948379739117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20166070735747931172985489 15124553051810948379739117)
                  ·
                    refine ⟨5671707394429105642402169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15124553051810948379739117 5671707394429105642402169)
                    ·
                      refine ⟨4253780545821829231801627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671707394429105642402169 4253780545821829231801627)
                      ·
                        rfl

theorem cell23_8284208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 3, 2].length) (baseStart_8284208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284208 prefixEnd_8284208 := by exact prefixLift 8284208
  have htrace : WordTrace (prefixWord ++ tailWord_8284208) baseStart_8284208 baseEnd_8284208 := by
    simpa [prefixWord, tailWord_8284208, baseEnd_8284208] using wordTrace_append hprefix tailTrace_8284208
  have hstable : (prefixWord ++ tailWord_8284208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284208).length < 2 ^ (prefixWord ++ tailWord_8284208).sum := by decide
  have hdescent : baseEnd_8284208 < baseStart_8284208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284221 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_8284221 : Nat := 118140960795 + 8284221 * 2 ^ 59
def prefixEnd_8284221 : Nat := 4983230072969 + 3 ^ 40 * 8284221 * 2
def baseEnd_8284221 : Nat := 4253787221070337680939067

theorem tailTrace_8284221 : CollatzResearch.WordTrace tailWord_8284221 prefixEnd_8284221 4253787221070337680939067 := by
  unfold tailWord_8284221
  simp only [CollatzResearch.WordTrace]
  refine ⟨302150362520689624151356517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201433575013793082767571011 302150362520689624151356517)
  ·
    refine ⟨56653192972629304528379347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302150362520689624151356517 56653192972629304528379347)
    ·
      refine ⟨84979789458943956792569021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56653192972629304528379347 84979789458943956792569021)
      ·
        refine ⟨31867421047103983797213383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84979789458943956792569021 31867421047103983797213383)
        ·
          refine ⟨47801131570655975695820075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31867421047103983797213383 47801131570655975695820075)
          ·
            refine ⟨71701697355983963543730113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47801131570655975695820075 71701697355983963543730113)
            ·
              refine ⟨53776273016987972657797585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71701697355983963543730113 53776273016987972657797585)
              ·
                refine ⟨40332204762740979493348189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53776273016987972657797585 40332204762740979493348189)
                ·
                  refine ⟨15124576786027867310005571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40332204762740979493348189 15124576786027867310005571)
                  ·
                    refine ⟨22686865179041800965008357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15124576786027867310005571 22686865179041800965008357)
                    ·
                      refine ⟨4253787221070337680939067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22686865179041800965008357 4253787221070337680939067)
                      ·
                        rfl

theorem cell23_8284221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_8284221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284221 prefixEnd_8284221 := by exact prefixLift 8284221
  have htrace : WordTrace (prefixWord ++ tailWord_8284221) baseStart_8284221 baseEnd_8284221 := by
    simpa [prefixWord, tailWord_8284221, baseEnd_8284221] using wordTrace_append hprefix tailTrace_8284221
  have hstable : (prefixWord ++ tailWord_8284221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284221).length < 2 ^ (prefixWord ++ tailWord_8284221).sum := by decide
  have hdescent : baseEnd_8284221 < baseStart_8284221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284222 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_8284222 : Nat := 118140960795 + 8284222 * 2 ^ 59
def prefixEnd_8284222 : Nat := 4983230072969 + 3 ^ 40 * 8284222 * 2
def baseEnd_8284222 : Nat := 472643081616776908558507

theorem tailTrace_8284222 : CollatzResearch.WordTrace tailWord_8284222 prefixEnd_8284222 472643081616776908558507 := by
  unfold tailWord_8284222
  simp only [CollatzResearch.WordTrace]
  refine ⟨37768799874210750165267865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201433599329124000881428613 37768799874210750165267865)
  ·
    refine ⟨28326599905658062623950899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37768799874210750165267865 28326599905658062623950899)
    ·
      refine ⟨42489899858487093935926349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28326599905658062623950899 42489899858487093935926349)
      ·
        refine ⟨15933712446932660225972381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42489899858487093935926349 15933712446932660225972381)
        ·
          refine ⟨5975142167599747584739643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15933712446932660225972381 5975142167599747584739643)
          ·
            refine ⟨8962713251399621377109465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975142167599747584739643 8962713251399621377109465)
            ·
              refine ⟨6722034938549716032832099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8962713251399621377109465 6722034938549716032832099)
              ·
                refine ⟨10083052407824574049248149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722034938549716032832099 10083052407824574049248149)
                ·
                  refine ⟨472643081616776908558507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10083052407824574049248149 472643081616776908558507)
                  ·
                    rfl

theorem cell23_8284222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_8284222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284222 prefixEnd_8284222 := by exact prefixLift 8284222
  have htrace : WordTrace (prefixWord ++ tailWord_8284222) baseStart_8284222 baseEnd_8284222 := by
    simpa [prefixWord, tailWord_8284222, baseEnd_8284222] using wordTrace_append hprefix tailTrace_8284222
  have hstable : (prefixWord ++ tailWord_8284222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284222).length < 2 ^ (prefixWord ++ tailWord_8284222).sum := by decide
  have hdescent : baseEnd_8284222 < baseStart_8284222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284238 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_8284238 : Nat := 118140960795 + 8284238 * 2 ^ 59
def prefixEnd_8284238 : Nat := 4983230072969 + 3 ^ 40 * 8284238 * 2
def baseEnd_8284238 : Nat := 4253795950241464114426489

theorem tailTrace_8284238 : CollatzResearch.WordTrace tailWord_8284238 prefixEnd_8284238 4253795950241464114426489 := by
  unfold tailWord_8284238
  simp only [CollatzResearch.WordTrace]
  refine ⟨37768872820203504506840671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201433988374418690703150245 37768872820203504506840671)
  ·
    refine ⟨56653309230305256760261007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37768872820203504506840671 56653309230305256760261007)
    ·
      refine ⟨84979963845457885140391511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56653309230305256760261007 84979963845457885140391511)
      ·
        refine ⟨127469945768186827710587267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84979963845457885140391511 127469945768186827710587267)
        ·
          refine ⟨191204918652280241565880901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127469945768186827710587267 191204918652280241565880901)
          ·
            refine ⟨35850922247302545293602669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191204918652280241565880901 35850922247302545293602669)
            ·
              refine ⟨13444095842738454485101001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35850922247302545293602669 13444095842738454485101001)
              ·
                refine ⟨10083071882053840863825751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13444095842738454485101001 10083071882053840863825751)
                ·
                  refine ⟨15124607823080761295738627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083071882053840863825751 15124607823080761295738627)
                  ·
                    refine ⟨22686911734621141943607941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15124607823080761295738627 22686911734621141943607941)
                    ·
                      refine ⟨4253795950241464114426489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22686911734621141943607941 4253795950241464114426489)
                      ·
                        rfl

theorem cell23_8284238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_8284238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284238 prefixEnd_8284238 := by exact prefixLift 8284238
  have htrace : WordTrace (prefixWord ++ tailWord_8284238) baseStart_8284238 baseEnd_8284238 := by
    simpa [prefixWord, tailWord_8284238, baseEnd_8284238] using wordTrace_append hprefix tailTrace_8284238
  have hstable : (prefixWord ++ tailWord_8284238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284238).length < 2 ^ (prefixWord ++ tailWord_8284238).sum := by decide
  have hdescent : baseEnd_8284238 < baseStart_8284238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284266 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_8284266 : Nat := 118140960795 + 8284266 * 2 ^ 59
def prefixEnd_8284266 : Nat := 4983230072969 + 3 ^ 40 * 8284266 * 2
def baseEnd_8284266 : Nat := 4253810327699790004876361

theorem tailTrace_8284266 : CollatzResearch.WordTrace tailWord_8284266 prefixEnd_8284266 4253810327699790004876361 := by
  unfold tailWord_8284266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538000951381649209186163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201434669203684397891163101 75538000951381649209186163)
  ·
    refine ⟨113307001427072473813779245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75538000951381649209186163 113307001427072473813779245)
    ·
      refine ⟨42490125535152177680167217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113307001427072473813779245 42490125535152177680167217)
      ·
        refine ⟨31867594151364133260125413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42490125535152177680167217 31867594151364133260125413)
        ·
          refine ⟨5975173903380774986273515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31867594151364133260125413 5975173903380774986273515)
          ·
            refine ⟨8962760855071162479410273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975173903380774986273515 8962760855071162479410273)
            ·
              refine ⟨6722070641303371859557705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8962760855071162479410273 6722070641303371859557705)
              ·
                refine ⟨5041552980977528894668279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722070641303371859557705 5041552980977528894668279)
                ·
                  refine ⟨7562329471466293342002419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041552980977528894668279 7562329471466293342002419)
                  ·
                    refine ⟨11343494207199440013003629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7562329471466293342002419 11343494207199440013003629)
                    ·
                      refine ⟨4253810327699790004876361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343494207199440013003629 4253810327699790004876361)
                      ·
                        rfl

theorem cell23_8284266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_8284266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284266 prefixEnd_8284266 := by exact prefixLift 8284266
  have htrace : WordTrace (prefixWord ++ tailWord_8284266) baseStart_8284266 baseEnd_8284266 := by
    simpa [prefixWord, tailWord_8284266, baseEnd_8284266] using wordTrace_append hprefix tailTrace_8284266
  have hstable : (prefixWord ++ tailWord_8284266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284266).length < 2 ^ (prefixWord ++ tailWord_8284266).sum := by decide
  have hdescent : baseEnd_8284266 < baseStart_8284266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284272 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 1, 2, 2]
def baseStart_8284272 : Nat := 118140960795 + 8284272 * 2 ^ 59
def prefixEnd_8284272 : Nat := 4983230072969 + 3 ^ 40 * 8284272 * 2
def baseEnd_8284272 : Nat := 4253813408583716981401333

theorem tailTrace_8284272 : CollatzResearch.WordTrace tailWord_8284272 prefixEnd_8284272 4253813408583716981401333 := by
  unfold tailWord_8284272
  simp only [CollatzResearch.WordTrace]
  refine ⟨151076111321752429930731535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201434815095669906574308713 151076111321752429930731535)
  ·
    refine ⟨226614166982628644896097303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151076111321752429930731535 226614166982628644896097303)
    ·
      refine ⟨339921250473942967344145955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226614166982628644896097303 339921250473942967344145955)
      ·
        refine ⟨509881875710914451016218933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339921250473942967344145955 509881875710914451016218933)
        ·
          refine ⟨47801425847898229782770525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 509881875710914451016218933 47801425847898229782770525)
          ·
            refine ⟨17925534692961836168538947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47801425847898229782770525 17925534692961836168538947)
            ·
              refine ⟨26888302039442754252808421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17925534692961836168538947 26888302039442754252808421)
              ·
                refine ⟨5041556632395516422401579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26888302039442754252808421 5041556632395516422401579)
                ·
                  refine ⟨7562334948593274633602369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5041556632395516422401579 7562334948593274633602369)
                  ·
                    refine ⟨5671751211444955975201777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7562334948593274633602369 5671751211444955975201777)
                    ·
                      refine ⟨4253813408583716981401333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671751211444955975201777 4253813408583716981401333)
                      ·
                        rfl

theorem cell23_8284272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 2, 2].length) (baseStart_8284272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284272 prefixEnd_8284272 := by exact prefixLift 8284272
  have htrace : WordTrace (prefixWord ++ tailWord_8284272) baseStart_8284272 baseEnd_8284272 := by
    simpa [prefixWord, tailWord_8284272, baseEnd_8284272] using wordTrace_append hprefix tailTrace_8284272
  have hstable : (prefixWord ++ tailWord_8284272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284272).length < 2 ^ (prefixWord ++ tailWord_8284272).sum := by decide
  have hdescent : baseEnd_8284272 < baseStart_8284272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284278 : List Nat := [5, 1, 1, 2, 1, 4, 1, 8]
def baseStart_8284278 : Nat := 118140960795 + 8284278 * 2 ^ 59
def prefixEnd_8284278 : Nat := 4983230072969 + 3 ^ 40 * 8284278 * 2
def baseEnd_8284278 : Nat := 157548758869171998441715

theorem tailTrace_8284278 : CollatzResearch.WordTrace tailWord_8284278 prefixEnd_8284278 157548758869171998441715 := by
  unfold tailWord_8284278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884527592592695180386343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201434960987655415257454325 18884527592592695180386343)
  ·
    refine ⟨28326791388889042770579515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18884527592592695180386343 28326791388889042770579515)
    ·
      refine ⟨42490187083333564155869273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28326791388889042770579515 42490187083333564155869273)
      ·
        refine ⟨31867640312500173116901955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42490187083333564155869273 31867640312500173116901955)
        ·
          refine ⟨47801460468750259675352933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31867640312500173116901955 47801460468750259675352933)
          ·
            refine ⟨8962773837890673689128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47801460468750259675352933 8962773837890673689128675)
            ·
              refine ⟨13444160756836010533693013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962773837890673689128675 13444160756836010533693013)
              ·
                refine ⟨157548758869171998441715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13444160756836010533693013 157548758869171998441715)
                ·
                  rfl

theorem cell23_8284278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_8284278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284278 prefixEnd_8284278 := by exact prefixLift 8284278
  have htrace : WordTrace (prefixWord ++ tailWord_8284278) baseStart_8284278 baseEnd_8284278 := by
    simpa [prefixWord, tailWord_8284278, baseEnd_8284278] using wordTrace_append hprefix tailTrace_8284278
  have hstable : (prefixWord ++ tailWord_8284278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284278).length < 2 ^ (prefixWord ++ tailWord_8284278).sum := by decide
  have hdescent : baseEnd_8284278 < baseStart_8284278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284304 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 8]
def baseStart_8284304 : Nat := 118140960795 + 8284304 * 2 ^ 59
def prefixEnd_8284304 : Nat := 4983230072969 + 3 ^ 40 * 8284304 * 2
def baseEnd_8284304 : Nat := 1417943279988220285400395

theorem tailTrace_8284304 : CollatzResearch.WordTrace tailWord_8284304 prefixEnd_8284304 1417943279988220285400395 := by
  unfold tailWord_8284304
  simp only [CollatzResearch.WordTrace]
  refine ⟨151076694889694464663313983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201435593186259286217751977 151076694889694464663313983)
  ·
    refine ⟨226615042334541696994970975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151076694889694464663313983 226615042334541696994970975)
    ·
      refine ⟨339922563501812545492456463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226615042334541696994970975 339922563501812545492456463)
      ·
        refine ⟨509883845252718818238684695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339922563501812545492456463 509883845252718818238684695)
        ·
          refine ⟨764825767879078227358027043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509883845252718818238684695 764825767879078227358027043)
          ·
            refine ⟨1147238651818617341037040565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764825767879078227358027043 1147238651818617341037040565)
            ·
              refine ⟨107553623607995375722222553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1147238651818617341037040565 107553623607995375722222553)
              ·
                refine ⟨80665217705996531791666915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107553623607995375722222553 80665217705996531791666915)
                ·
                  refine ⟨120997826558994797687500373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80665217705996531791666915 120997826558994797687500373)
                  ·
                    refine ⟨1417943279988220285400395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 120997826558994797687500373 1417943279988220285400395)
                    ·
                      rfl

theorem cell23_8284304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_8284304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284304 prefixEnd_8284304 := by exact prefixLift 8284304
  have htrace : WordTrace (prefixWord ++ tailWord_8284304) baseStart_8284304 baseEnd_8284304 := by
    simpa [prefixWord, tailWord_8284304, baseEnd_8284304] using wordTrace_append hprefix tailTrace_8284304
  have hstable : (prefixWord ++ tailWord_8284304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284304).length < 2 ^ (prefixWord ++ tailWord_8284304).sum := by decide
  have hdescent : baseEnd_8284304 < baseStart_8284304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284321 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_8284321 : Nat := 118140960795 + 8284321 * 2 ^ 59
def prefixEnd_8284321 : Nat := 4983230072969 + 3 ^ 40 * 8284321 * 2
def baseEnd_8284321 : Nat := 1417946189711929096562869

theorem tailTrace_8284321 : CollatzResearch.WordTrace tailWord_8284321 prefixEnd_8284321 1417946189711929096562869 := by
  unfold tailWord_8284321
  simp only [CollatzResearch.WordTrace]
  refine ⟨302154009820327341229996817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201436006546884894153331211 302154009820327341229996817)
  ·
    refine ⟨226615507365245505922497613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302154009820327341229996817 226615507365245505922497613)
    ·
      refine ⟨84980815261967064720936605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226615507365245505922497613 84980815261967064720936605)
      ·
        refine ⟨31867805723237649270351227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84980815261967064720936605 31867805723237649270351227)
        ·
          refine ⟨47801708584856473905526841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31867805723237649270351227 47801708584856473905526841)
          ·
            refine ⟨35851281438642355429145131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47801708584856473905526841 35851281438642355429145131)
            ·
              refine ⟨53776922157963533143717697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35851281438642355429145131 53776922157963533143717697)
              ·
                refine ⟨40332691618472649857788273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53776922157963533143717697 40332691618472649857788273)
                ·
                  refine ⟨30249518713854487393341205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40332691618472649857788273 30249518713854487393341205)
                  ·
                    refine ⟨1417946189711929096562869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30249518713854487393341205 1417946189711929096562869)
                    ·
                      rfl

theorem cell23_8284321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_8284321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284321 prefixEnd_8284321 := by exact prefixLift 8284321
  have htrace : WordTrace (prefixWord ++ tailWord_8284321) baseStart_8284321 baseEnd_8284321 := by
    simpa [prefixWord, tailWord_8284321, baseEnd_8284321] using wordTrace_append hprefix tailTrace_8284321
  have hstable : (prefixWord ++ tailWord_8284321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284321).length < 2 ^ (prefixWord ++ tailWord_8284321).sum := by decide
  have hdescent : baseEnd_8284321 < baseStart_8284321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284322 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_8284322 : Nat := 118140960795 + 8284322 * 2 ^ 59
def prefixEnd_8284322 : Nat := 4983230072969 + 3 ^ 40 * 8284322 * 2
def baseEnd_8284322 : Nat := 4253839082616441785776103

theorem tailTrace_8284322 : CollatzResearch.WordTrace tailWord_8284322 prefixEnd_8284322 4253839082616441785776103 := by
  unfold tailWord_8284322
  simp only [CollatzResearch.WordTrace]
  refine ⟨75538511573330929600195805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201436030862215812267188813 75538511573330929600195805)
  ·
    refine ⟨28326941839999098600073427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75538511573330929600195805 28326941839999098600073427)
    ·
      refine ⟨42490412759998647900110141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28326941839999098600073427 42490412759998647900110141)
      ·
        refine ⟨15933904784999492962541303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42490412759998647900110141 15933904784999492962541303)
        ·
          refine ⟨23900857177499239443811955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15933904784999492962541303 23900857177499239443811955)
          ·
            refine ⟨35851285766248859165717933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23900857177499239443811955 35851285766248859165717933)
            ·
              refine ⟨13444232162343322187144225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35851285766248859165717933 13444232162343322187144225)
              ·
                refine ⟨10083174121757491640358169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13444232162343322187144225 10083174121757491640358169)
                ·
                  refine ⟨7562380591318118730268627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10083174121757491640358169 7562380591318118730268627)
                  ·
                    refine ⟨11343570886977178095402941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7562380591318118730268627 11343570886977178095402941)
                    ·
                      refine ⟨4253839082616441785776103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343570886977178095402941 4253839082616441785776103)
                      ·
                        rfl

theorem cell23_8284322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_8284322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284322 prefixEnd_8284322 := by exact prefixLift 8284322
  have htrace : WordTrace (prefixWord ++ tailWord_8284322) baseStart_8284322 baseEnd_8284322 := by
    simpa [prefixWord, tailWord_8284322, baseEnd_8284322] using wordTrace_append hprefix tailTrace_8284322
  have hstable : (prefixWord ++ tailWord_8284322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284322).length < 2 ^ (prefixWord ++ tailWord_8284322).sum := by decide
  have hdescent : baseEnd_8284322 < baseStart_8284322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284361 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_8284361 : Nat := 118140960795 + 8284361 * 2 ^ 59
def prefixEnd_8284361 : Nat := 4983230072969 + 3 ^ 40 * 8284361 * 2
def baseEnd_8284361 : Nat := 4253859108361967133188423

theorem tailTrace_8284361 : CollatzResearch.WordTrace tailWord_8284361 prefixEnd_8284361 4253859108361967133188423 := by
  unfold tailWord_8284361
  simp only [CollatzResearch.WordTrace]
  refine ⟨302155468740182428061452937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201436979160121618707635291 302155468740182428061452937)
  ·
    refine ⟨226616601555136821046089703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302155468740182428061452937 226616601555136821046089703)
    ·
      refine ⟨339924902332705231569134555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226616601555136821046089703 339924902332705231569134555)
      ·
        refine ⟨509887353499057847353701833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339924902332705231569134555 509887353499057847353701833)
        ·
          refine ⟨382415515124293385515276375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509887353499057847353701833 382415515124293385515276375)
          ·
            refine ⟨573623272686440078272914563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382415515124293385515276375 573623272686440078272914563)
            ·
              refine ⟨860434909029660117409371845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573623272686440078272914563 860434909029660117409371845)
              ·
                refine ⟨161331545443061272014257221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 860434909029660117409371845 161331545443061272014257221)
                ·
                  refine ⟨30249664770573988502673229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161331545443061272014257221 30249664770573988502673229)
                  ·
                    refine ⟨11343624288965245688502461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30249664770573988502673229 11343624288965245688502461)
                    ·
                      refine ⟨4253859108361967133188423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343624288965245688502461 4253859108361967133188423)
                      ·
                        rfl

theorem cell23_8284361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_8284361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284361 prefixEnd_8284361 := by exact prefixLift 8284361
  have htrace : WordTrace (prefixWord ++ tailWord_8284361) baseStart_8284361 baseEnd_8284361 := by
    simpa [prefixWord, tailWord_8284361, baseEnd_8284361] using wordTrace_append hprefix tailTrace_8284361
  have hstable : (prefixWord ++ tailWord_8284361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284361).length < 2 ^ (prefixWord ++ tailWord_8284361).sum := by decide
  have hdescent : baseEnd_8284361 < baseStart_8284361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284385 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 5]
def baseStart_8284385 : Nat := 118140960795 + 8284385 * 2 ^ 59
def prefixEnd_8284385 : Nat := 4983230072969 + 3 ^ 40 * 8284385 * 2
def baseEnd_8284385 : Nat := 472652381321963893254257

theorem tailTrace_8284385 : CollatzResearch.WordTrace tailWord_8284385 prefixEnd_8284385 472652381321963893254257 := by
  unfold tailWord_8284385
  simp only [CollatzResearch.WordTrace]
  refine ⟨302156344092095480160326609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201437562728063653440217739 302156344092095480160326609)
  ·
    refine ⟨226617258069071610120244957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302156344092095480160326609 226617258069071610120244957)
    ·
      refine ⟨84981471775901853795091859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226617258069071610120244957 84981471775901853795091859)
      ·
        refine ⟨127472207663852780692637789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84981471775901853795091859 127472207663852780692637789)
        ·
          refine ⟨47802077873944792759739171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127472207663852780692637789 47802077873944792759739171)
          ·
            refine ⟨71703116810917189139608757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47802077873944792759739171 71703116810917189139608757)
            ·
              refine ⟨6722167201023486481838321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71703116810917189139608757 6722167201023486481838321)
              ·
                refine ⟨5041625400767614861378741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6722167201023486481838321 5041625400767614861378741)
                ·
                  refine ⟨472652381321963893254257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041625400767614861378741 472652381321963893254257)
                  ·
                    rfl

theorem cell23_8284385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 5].length) (baseStart_8284385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284385 prefixEnd_8284385 := by exact prefixLift 8284385
  have htrace : WordTrace (prefixWord ++ tailWord_8284385) baseStart_8284385 baseEnd_8284385 := by
    simpa [prefixWord, tailWord_8284385, baseEnd_8284385] using wordTrace_append hprefix tailTrace_8284385
  have hstable : (prefixWord ++ tailWord_8284385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284385).length < 2 ^ (prefixWord ++ tailWord_8284385).sum := by decide
  have hdescent : baseEnd_8284385 < baseStart_8284385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284388 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_8284388 : Nat := 118140960795 + 8284388 * 2 ^ 59
def prefixEnd_8284388 : Nat := 4983230072969 + 3 ^ 40 * 8284388 * 2
def baseEnd_8284388 : Nat := 4253872972339638527550799

theorem tailTrace_8284388 : CollatzResearch.WordTrace tailWord_8284388 prefixEnd_8284388 4253872972339638527550799 := by
  unfold tailWord_8284388
  simp only [CollatzResearch.WordTrace]
  refine ⟨151078226755542305836342909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201437635674056407781790545 151078226755542305836342909)
  ·
    refine ⟨56654335033328364688628591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151078226755542305836342909 56654335033328364688628591)
    ·
      refine ⟨84981502549992547032942887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56654335033328364688628591 84981502549992547032942887)
      ·
        refine ⟨127472253824988820549414331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84981502549992547032942887 127472253824988820549414331)
        ·
          refine ⟨191208380737483230824121497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127472253824988820549414331 191208380737483230824121497)
          ·
            refine ⟨143406285553112423118091123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191208380737483230824121497 143406285553112423118091123)
            ·
              refine ⟨215109428329668634677136685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143406285553112423118091123 215109428329668634677136685)
              ·
                refine ⟨80666035623625738003926257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215109428329668634677136685 80666035623625738003926257)
                ·
                  refine ⟨60499526717719303502944693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80666035623625738003926257 60499526717719303502944693)
                  ·
                    refine ⟨5671830629786184703401065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60499526717719303502944693 5671830629786184703401065)
                    ·
                      refine ⟨4253872972339638527550799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671830629786184703401065 4253872972339638527550799)
                      ·
                        rfl

theorem cell23_8284388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_8284388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284388 prefixEnd_8284388 := by exact prefixLift 8284388
  have htrace : WordTrace (prefixWord ++ tailWord_8284388) baseStart_8284388 baseEnd_8284388 := by
    simpa [prefixWord, tailWord_8284388, baseEnd_8284388] using wordTrace_append hprefix tailTrace_8284388
  have hstable : (prefixWord ++ tailWord_8284388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284388).length < 2 ^ (prefixWord ++ tailWord_8284388).sum := by decide
  have hdescent : baseEnd_8284388 < baseStart_8284388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284401 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_8284401 : Nat := 118140960795 + 8284401 * 2 ^ 59
def prefixEnd_8284401 : Nat := 4983230072969 + 3 ^ 40 * 8284401 * 2
def baseEnd_8284401 : Nat := 4253879647588146976688239

theorem tailTrace_8284401 : CollatzResearch.WordTrace tailWord_8284401 prefixEnd_8284401 4253879647588146976688239 := by
  unfold tailWord_8284401
  simp only [CollatzResearch.WordTrace]
  refine ⟨302156927660037514892909057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201437951773358343261939371 302156927660037514892909057)
  ·
    refine ⟨226617695745028136169681793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302156927660037514892909057 226617695745028136169681793)
    ·
      refine ⟨169963271808771102127261345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226617695745028136169681793 169963271808771102127261345)
      ·
        refine ⟨127472453856578326595446009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169963271808771102127261345 127472453856578326595446009)
        ·
          refine ⟨95604340392433744946584507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127472453856578326595446009 95604340392433744946584507)
          ·
            refine ⟨143406510588650617419876761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95604340392433744946584507 143406510588650617419876761)
            ·
              refine ⟨107554882941487963064907571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143406510588650617419876761 107554882941487963064907571)
              ·
                refine ⟨161332324412231944597361357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107554882941487963064907571 161332324412231944597361357)
                ·
                  refine ⟨60499621654586979224010509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161332324412231944597361357 60499621654586979224010509)
                  ·
                    refine ⟨22687358120470117209003941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60499621654586979224010509 22687358120470117209003941)
                    ·
                      refine ⟨4253879647588146976688239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22687358120470117209003941 4253879647588146976688239)
                      ·
                        rfl

theorem cell23_8284401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_8284401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284401 prefixEnd_8284401 := by exact prefixLift 8284401
  have htrace : WordTrace (prefixWord ++ tailWord_8284401) baseStart_8284401 baseEnd_8284401 := by
    simpa [prefixWord, tailWord_8284401, baseEnd_8284401] using wordTrace_append hprefix tailTrace_8284401
  have hstable : (prefixWord ++ tailWord_8284401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284401).length < 2 ^ (prefixWord ++ tailWord_8284401).sum := by decide
  have hdescent : baseEnd_8284401 < baseStart_8284401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284522 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_8284522 : Nat := 118140960795 + 8284522 * 2 ^ 59
def prefixEnd_8284522 : Nat := 4983230072969 + 3 ^ 40 * 8284522 * 2
def baseEnd_8284522 : Nat := 1417980592915780334425061

theorem tailTrace_8284522 : CollatzResearch.WordTrace tailWord_8284522 prefixEnd_8284522 1417980592915780334425061 := by
  unfold tailWord_8284522
  simp only [CollatzResearch.WordTrace]
  refine ⟨75540335223149788139515955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201440893928399435038709213 75540335223149788139515955)
  ·
    refine ⟨113310502834724682209273933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75540335223149788139515955 113310502834724682209273933)
    ·
      refine ⟨42491438563021755828477725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113310502834724682209273933 42491438563021755828477725)
      ·
        refine ⟨15934289461133158435679147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42491438563021755828477725 15934289461133158435679147)
        ·
          refine ⟨23901434191699737653518721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15934289461133158435679147 23901434191699737653518721)
          ·
            refine ⟨17926075643774803240139041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23901434191699737653518721 17926075643774803240139041)
            ·
              refine ⟨13444556732831102430104281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17926075643774803240139041 13444556732831102430104281)
              ·
                refine ⟨10083417549623326822578211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13444556732831102430104281 10083417549623326822578211)
                ·
                  refine ⟨15125126324434990233867317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083417549623326822578211 15125126324434990233867317)
                  ·
                    refine ⟨1417980592915780334425061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15125126324434990233867317 1417980592915780334425061)
                    ·
                      rfl

theorem cell23_8284522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_8284522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284522 prefixEnd_8284522 := by exact prefixLift 8284522
  have htrace : WordTrace (prefixWord ++ tailWord_8284522) baseStart_8284522 baseEnd_8284522 := by
    simpa [prefixWord, tailWord_8284522, baseEnd_8284522] using wordTrace_append hprefix tailTrace_8284522
  have hstable : (prefixWord ++ tailWord_8284522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284522).length < 2 ^ (prefixWord ++ tailWord_8284522).sum := by decide
  have hdescent : baseEnd_8284522 < baseStart_8284522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284525 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_8284525 : Nat := 118140960795 + 8284525 * 2 ^ 59
def prefixEnd_8284525 : Nat := 4983230072969 + 3 ^ 40 * 8284525 * 2
def baseEnd_8284525 : Nat := 4253943319189304491537669

theorem tailTrace_8284525 : CollatzResearch.WordTrace tailWord_8284525 prefixEnd_8284525 4253943319189304491537669 := by
  unfold tailWord_8284525
  simp only [CollatzResearch.WordTrace]
  refine ⟨302161450311588284070423029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201440966874392189380282019 302161450311588284070423029)
  ·
    refine ⟨28327635966711401631602159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302161450311588284070423029 28327635966711401631602159)
    ·
      refine ⟨42491453950067102447403239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28327635966711401631602159 42491453950067102447403239)
      ·
        refine ⟨63737180925100653671104859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42491453950067102447403239 63737180925100653671104859)
        ·
          refine ⟨95605771387650980506657289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63737180925100653671104859 95605771387650980506657289)
          ·
            refine ⟨71704328540738235379992967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95605771387650980506657289 71704328540738235379992967)
            ·
              refine ⟨107556492811107353069989451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71704328540738235379992967 107556492811107353069989451)
              ·
                refine ⟨161334739216661029604984177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107556492811107353069989451 161334739216661029604984177)
                ·
                  refine ⟨121001054412495772203738133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161334739216661029604984177 121001054412495772203738133)
                  ·
                    refine ⟨5671924425585739322050225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121001054412495772203738133 5671924425585739322050225)
                    ·
                      refine ⟨4253943319189304491537669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671924425585739322050225 4253943319189304491537669)
                      ·
                        rfl

theorem cell23_8284525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_8284525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284525 prefixEnd_8284525 := by exact prefixLift 8284525
  have htrace : WordTrace (prefixWord ++ tailWord_8284525) baseStart_8284525 baseEnd_8284525 := by
    simpa [prefixWord, tailWord_8284525, baseEnd_8284525] using wordTrace_append hprefix tailTrace_8284525
  have hstable : (prefixWord ++ tailWord_8284525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284525).length < 2 ^ (prefixWord ++ tailWord_8284525).sum := by decide
  have hdescent : baseEnd_8284525 < baseStart_8284525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284531 : List Nat := [1, 1, 1, 2, 2, 1, 2, 13]
def baseStart_8284531 : Nat := 118140960795 + 8284531 * 2 ^ 59
def prefixEnd_8284531 : Nat := 4983230072969 + 3 ^ 40 * 8284531 * 2
def baseEnd_8284531 : Nat := 157553570373082646965283

theorem tailTrace_8284531 : CollatzResearch.WordTrace tailWord_8284531 prefixEnd_8284531 157553570373082646965283 := by
  unfold tailWord_8284531
  simp only [CollatzResearch.WordTrace]
  refine ⟨302161669149566547095141447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201441112766377698063427631 302161669149566547095141447)
  ·
    refine ⟨453242503724349820642712171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302161669149566547095141447 453242503724349820642712171)
    ·
      refine ⟨679863755586524730964068257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453242503724349820642712171 679863755586524730964068257)
      ·
        refine ⟨509897816689893548223051193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679863755586524730964068257 509897816689893548223051193)
        ·
          refine ⟨382423362517420161167288395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509897816689893548223051193 382423362517420161167288395)
          ·
            refine ⟨573635043776130241750932593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382423362517420161167288395 573635043776130241750932593)
            ·
              refine ⟨430226282832097681313199445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573635043776130241750932593 430226282832097681313199445)
              ·
                refine ⟨157553570373082646965283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 430226282832097681313199445 157553570373082646965283)
                ·
                  rfl

theorem cell23_8284531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 13].length) (baseStart_8284531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284531 prefixEnd_8284531 := by exact prefixLift 8284531
  have htrace : WordTrace (prefixWord ++ tailWord_8284531) baseStart_8284531 baseEnd_8284531 := by
    simpa [prefixWord, tailWord_8284531, baseEnd_8284531] using wordTrace_append hprefix tailTrace_8284531
  have hstable : (prefixWord ++ tailWord_8284531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284531).length < 2 ^ (prefixWord ++ tailWord_8284531).sum := by decide
  have hdescent : baseEnd_8284531 < baseStart_8284531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284545 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_8284545 : Nat := 118140960795 + 8284545 * 2 ^ 59
def prefixEnd_8284545 : Nat := 4983230072969 + 3 ^ 40 * 8284545 * 2
def baseEnd_8284545 : Nat := 4253953588802394413287577

theorem tailTrace_8284545 : CollatzResearch.WordTrace tailWord_8284545 prefixEnd_8284545 4253953588802394413287577 := by
  unfold tailWord_8284545
  simp only [CollatzResearch.WordTrace]
  refine ⟨302162179771515827486151089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201441453181010551657434059 302162179771515827486151089)
  ·
    refine ⟨226621634828636870614613317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302162179771515827486151089 226621634828636870614613317)
    ·
      refine ⟨42491556530369413240239997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226621634828636870614613317 42491556530369413240239997)
      ·
        refine ⟨15934333698888529965089999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42491556530369413240239997 15934333698888529965089999)
        ·
          refine ⟨23901500548332794947634999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15934333698888529965089999 23901500548332794947634999)
          ·
            refine ⟨35852250822499192421452499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23901500548332794947634999 35852250822499192421452499)
            ·
              refine ⟨53778376233748788632178749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35852250822499192421452499 53778376233748788632178749)
              ·
                refine ⟨20166891087655795737067031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53778376233748788632178749 20166891087655795737067031)
                ·
                  refine ⟨30250336631483693605600547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20166891087655795737067031 30250336631483693605600547)
                  ·
                    refine ⟨45375504947225540408400821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30250336631483693605600547 45375504947225540408400821)
                    ·
                      refine ⟨4253953588802394413287577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45375504947225540408400821 4253953588802394413287577)
                      ·
                        rfl

theorem cell23_8284545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_8284545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284545 prefixEnd_8284545 := by exact prefixLift 8284545
  have htrace : WordTrace (prefixWord ++ tailWord_8284545) baseStart_8284545 baseEnd_8284545 := by
    simpa [prefixWord, tailWord_8284545, baseEnd_8284545] using wordTrace_append hprefix tailTrace_8284545
  have hstable : (prefixWord ++ tailWord_8284545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284545).length < 2 ^ (prefixWord ++ tailWord_8284545).sum := by decide
  have hdescent : baseEnd_8284545 < baseStart_8284545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284546 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_8284546 : Nat := 118140960795 + 8284546 * 2 ^ 59
def prefixEnd_8284546 : Nat := 4983230072969 + 3 ^ 40 * 8284546 * 2
def baseEnd_8284546 : Nat := 4253954102283048909375073

theorem tailTrace_8284546 : CollatzResearch.WordTrace tailWord_8284546 prefixEnd_8284546 4253954102283048909375073 := by
  unfold tailWord_8284546
  simp only [CollatzResearch.WordTrace]
  refine ⟨75540554061128051164234373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201441477496341469771291661 75540554061128051164234373)
  ·
    refine ⟨14163853886461509593293945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75540554061128051164234373 14163853886461509593293945)
    ·
      refine ⟨10622890414846132194970459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14163853886461509593293945 10622890414846132194970459)
      ·
        refine ⟨15934335622269198292455689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10622890414846132194970459 15934335622269198292455689)
        ·
          refine ⟨11950751716701898719341767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15934335622269198292455689 11950751716701898719341767)
          ·
            refine ⟨17926127575052848079012651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950751716701898719341767 17926127575052848079012651)
            ·
              refine ⟨26889191362579272118518977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926127575052848079012651 26889191362579272118518977)
              ·
                refine ⟨20166893521934454088889233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26889191362579272118518977 20166893521934454088889233)
                ·
                  refine ⟨15125170141450840566666925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20166893521934454088889233 15125170141450840566666925)
                  ·
                    refine ⟨5671938803044065212500097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15125170141450840566666925 5671938803044065212500097)
                    ·
                      refine ⟨4253954102283048909375073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671938803044065212500097 4253954102283048909375073)
                      ·
                        rfl

theorem cell23_8284546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_8284546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284546 prefixEnd_8284546 := by exact prefixLift 8284546
  have htrace : WordTrace (prefixWord ++ tailWord_8284546) baseStart_8284546 baseEnd_8284546 := by
    simpa [prefixWord, tailWord_8284546, baseEnd_8284546] using wordTrace_append hprefix tailTrace_8284546
  have hstable : (prefixWord ++ tailWord_8284546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284546).length < 2 ^ (prefixWord ++ tailWord_8284546).sum := by decide
  have hdescent : baseEnd_8284546 < baseStart_8284546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284575 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_8284575 : Nat := 118140960795 + 8284575 * 2 ^ 59
def prefixEnd_8284575 : Nat := 4983230072969 + 3 ^ 40 * 8284575 * 2
def baseEnd_8284575 : Nat := 4253968993222029295912439

theorem tailTrace_8284575 : CollatzResearch.WordTrace tailWord_8284575 prefixEnd_8284575 4253968993222029295912439 := by
  unfold tailWord_8284575
  simp only [CollatzResearch.WordTrace]
  refine ⟨302163273961407142609743179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201442182640938095073162119 302163273961407142609743179)
  ·
    refine ⟨453244910942110713914614769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302163273961407142609743179 453244910942110713914614769)
    ·
      refine ⟨339933683206583035435961077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453244910942110713914614769 339933683206583035435961077)
      ·
        refine ⟨31868782800617159572121351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 339933683206583035435961077 31868782800617159572121351)
        ·
          refine ⟨47803174200925739358182027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31868782800617159572121351 47803174200925739358182027)
          ·
            refine ⟨71704761301388609037273041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47803174200925739358182027 71704761301388609037273041)
            ·
              refine ⟨53778570976041456777954781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71704761301388609037273041 53778570976041456777954781)
              ·
                refine ⟨20166964116015546291733043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53778570976041456777954781 20166964116015546291733043)
                ·
                  refine ⟨30250446174023319437599565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20166964116015546291733043 30250446174023319437599565)
                  ·
                    refine ⟨11343917315258744789099837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30250446174023319437599565 11343917315258744789099837)
                    ·
                      refine ⟨4253968993222029295912439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11343917315258744789099837 4253968993222029295912439)
                      ·
                        rfl

theorem cell23_8284575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_8284575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284575 prefixEnd_8284575 := by exact prefixLift 8284575
  have htrace : WordTrace (prefixWord ++ tailWord_8284575) baseStart_8284575 baseEnd_8284575 := by
    simpa [prefixWord, tailWord_8284575, baseEnd_8284575] using wordTrace_append hprefix tailTrace_8284575
  have hstable : (prefixWord ++ tailWord_8284575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284575).length < 2 ^ (prefixWord ++ tailWord_8284575).sum := by decide
  have hdescent : baseEnd_8284575 < baseStart_8284575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284596 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_8284596 : Nat := 118140960795 + 8284596 * 2 ^ 59
def prefixEnd_8284596 : Nat := 4983230072969 + 3 ^ 40 * 8284596 * 2
def baseEnd_8284596 : Nat := 4253979776315773713749843

theorem tailTrace_8284596 : CollatzResearch.WordTrace tailWord_8284596 prefixEnd_8284596 4253979776315773713749843 := by
  unfold tailWord_8284596
  simp only [CollatzResearch.WordTrace]
  refine ⟨151082019947165531598128821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201442693262887375464171761 151082019947165531598128821)
  ·
    refine ⟨14163939370046768587324577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151082019947165531598128821 14163939370046768587324577)
    ·
      refine ⟨10622954527535076440493433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14163939370046768587324577 10622954527535076440493433)
      ·
        refine ⟨7967215895651307330370075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10622954527535076440493433 7967215895651307330370075)
        ·
          refine ⟨11950823843476960995555113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967215895651307330370075 11950823843476960995555113)
          ·
            refine ⟨8963117882607720746666335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11950823843476960995555113 8963117882607720746666335)
            ·
              refine ⟨13444676823911581119999503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8963117882607720746666335 13444676823911581119999503)
              ·
                refine ⟨20167015235867371679999255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13444676823911581119999503 20167015235867371679999255)
                ·
                  refine ⟨30250522853801057519998883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20167015235867371679999255 30250522853801057519998883)
                  ·
                    refine ⟨45375784280701586279998325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30250522853801057519998883 45375784280701586279998325)
                    ·
                      refine ⟨4253979776315773713749843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45375784280701586279998325 4253979776315773713749843)
                      ·
                        rfl

theorem cell23_8284596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_8284596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284596 prefixEnd_8284596 := by exact prefixLift 8284596
  have htrace : WordTrace (prefixWord ++ tailWord_8284596) baseStart_8284596 baseEnd_8284596 := by
    simpa [prefixWord, tailWord_8284596, baseEnd_8284596] using wordTrace_append hprefix tailTrace_8284596
  have hstable : (prefixWord ++ tailWord_8284596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284596).length < 2 ^ (prefixWord ++ tailWord_8284596).sum := by decide
  have hdescent : baseEnd_8284596 < baseStart_8284596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284602 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_8284602 : Nat := 118140960795 + 8284602 * 2 ^ 59
def prefixEnd_8284602 : Nat := 4983230072969 + 3 ^ 40 * 8284602 * 2
def baseEnd_8284602 : Nat := 4253982857199700690274815

theorem tailTrace_8284602 : CollatzResearch.WordTrace tailWord_8284602 prefixEnd_8284602 4253982857199700690274815 := by
  unfold tailWord_8284602
  simp only [CollatzResearch.WordTrace]
  refine ⟨75541064683077331555244015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201442839154872884147317373 75541064683077331555244015)
  ·
    refine ⟨113311597024615997332866023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75541064683077331555244015 113311597024615997332866023)
    ·
      refine ⟨169967395536923995999299035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113311597024615997332866023 169967395536923995999299035)
      ·
        refine ⟨254951093305385993998948553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169967395536923995999299035 254951093305385993998948553)
        ·
          refine ⟨191213319979039495499211415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254951093305385993998948553 191213319979039495499211415)
          ·
            refine ⟨286819979968559243248817123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191213319979039495499211415 286819979968559243248817123)
            ·
              refine ⟨430229969952838864873225685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286819979968559243248817123 430229969952838864873225685)
              ·
                refine ⟨10083514920769660895466227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 430229969952838864873225685 10083514920769660895466227)
                ·
                  refine ⟨15125272381154491343199341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083514920769660895466227 15125272381154491343199341)
                  ·
                    refine ⟨5671977142932934253699753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15125272381154491343199341 5671977142932934253699753)
                    ·
                      refine ⟨4253982857199700690274815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671977142932934253699753 4253982857199700690274815)
                      ·
                        rfl

theorem cell23_8284602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_8284602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284602 prefixEnd_8284602 := by exact prefixLift 8284602
  have htrace : WordTrace (prefixWord ++ tailWord_8284602) baseStart_8284602 baseEnd_8284602 := by
    simpa [prefixWord, tailWord_8284602, baseEnd_8284602] using wordTrace_append hprefix tailTrace_8284602
  have hstable : (prefixWord ++ tailWord_8284602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284602).length < 2 ^ (prefixWord ++ tailWord_8284602).sum := by decide
  have hdescent : baseEnd_8284602 < baseStart_8284602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284608 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 2, 6]
def baseStart_8284608 : Nat := 118140960795 + 8284608 * 2 ^ 59
def prefixEnd_8284608 : Nat := 4983230072969 + 3 ^ 40 * 8284608 * 2
def baseEnd_8284608 : Nat := 1417995312694542555599929

theorem tailTrace_8284608 : CollatzResearch.WordTrace tailWord_8284608 prefixEnd_8284608 1417995312694542555599929 := by
  unfold tailWord_8284608
  simp only [CollatzResearch.WordTrace]
  refine ⟨151082238785143794622847239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201442985046858392830462985 151082238785143794622847239)
  ·
    refine ⟨226623358177715691934270859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151082238785143794622847239 226623358177715691934270859)
    ·
      refine ⟨339935037266573537901406289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226623358177715691934270859 339935037266573537901406289)
      ·
        refine ⟨254951277949930153426054717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339935037266573537901406289 254951277949930153426054717)
        ·
          refine ⟨95606729231223807534770519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254951277949930153426054717 95606729231223807534770519)
          ·
            refine ⟨143410093846835711302155779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95606729231223807534770519 143410093846835711302155779)
            ·
              refine ⟨215115140770253566953233669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143410093846835711302155779 215115140770253566953233669)
              ·
                refine ⟨40334088894422543803731313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215115140770253566953233669 40334088894422543803731313)
                ·
                  refine ⟨30250566670816907852798485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40334088894422543803731313 30250566670816907852798485)
                  ·
                    refine ⟨1417995312694542555599929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30250566670816907852798485 1417995312694542555599929)
                    ·
                      rfl

theorem cell23_8284608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_8284608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284608 prefixEnd_8284608 := by exact prefixLift 8284608
  have htrace : WordTrace (prefixWord ++ tailWord_8284608) baseStart_8284608 baseEnd_8284608 := by
    simpa [prefixWord, tailWord_8284608, baseEnd_8284608] using wordTrace_append hprefix tailTrace_8284608
  have hstable : (prefixWord ++ tailWord_8284608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284608).length < 2 ^ (prefixWord ++ tailWord_8284608).sum := by decide
  have hdescent : baseEnd_8284608 < baseStart_8284608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284632 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_8284632 : Nat := 118140960795 + 8284632 * 2 ^ 59
def prefixEnd_8284632 : Nat := 4983230072969 + 3 ^ 40 * 8284632 * 2
def baseEnd_8284632 : Nat := 4253998261619335572899677

theorem tailTrace_8284632 : CollatzResearch.WordTrace tailWord_8284632 prefixEnd_8284632 4253998261619335572899677 := by
  unfold tailWord_8284632
  simp only [CollatzResearch.WordTrace]
  refine ⟨151082676461100320672284075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201443568614800427563045433 151082676461100320672284075)
  ·
    refine ⟨226624014691650481008426113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151082676461100320672284075 226624014691650481008426113)
    ·
      refine ⟨169968011018737860756319585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226624014691650481008426113 169968011018737860756319585)
      ·
        refine ⟨127476008264053395567239689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169968011018737860756319585 127476008264053395567239689)
        ·
          refine ⟨95607006198040046675429767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127476008264053395567239689 95607006198040046675429767)
          ·
            refine ⟨143410509297060070013144651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95607006198040046675429767 143410509297060070013144651)
            ·
              refine ⟨215115763945590105019716977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143410509297060070013144651 215115763945590105019716977)
              ·
                refine ⟨161336822959192578764787733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215115763945590105019716977 161336822959192578764787733)
                ·
                  refine ⟨7562663576212152129599425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161336822959192578764787733 7562663576212152129599425)
                  ·
                    refine ⟨5671997682159114097199569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7562663576212152129599425 5671997682159114097199569)
                    ·
                      refine ⟨4253998261619335572899677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5671997682159114097199569 4253998261619335572899677)
                      ·
                        rfl

theorem cell23_8284632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_8284632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284632 prefixEnd_8284632 := by exact prefixLift 8284632
  have htrace : WordTrace (prefixWord ++ tailWord_8284632) baseStart_8284632 baseEnd_8284632 := by
    simpa [prefixWord, tailWord_8284632, baseEnd_8284632] using wordTrace_append hprefix tailTrace_8284632
  have hstable : (prefixWord ++ tailWord_8284632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284632).length < 2 ^ (prefixWord ++ tailWord_8284632).sum := by decide
  have hdescent : baseEnd_8284632 < baseStart_8284632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284653 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_8284653 : Nat := 118140960795 + 8284653 * 2 ^ 59
def prefixEnd_8284653 : Nat := 4983230072969 + 3 ^ 40 * 8284653 * 2
def baseEnd_8284653 : Nat := 4254009044713079990737081

theorem tailTrace_8284653 : CollatzResearch.WordTrace tailWord_8284653 prefixEnd_8284653 4254009044713079990737081 := by
  unfold tailWord_8284653
  simp only [CollatzResearch.WordTrace]
  refine ⟨302166118855124561931082613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201444079236749707954055075 302166118855124561931082613)
  ·
    refine ⟨28328073642667927681038995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302166118855124561931082613 28328073642667927681038995)
    ·
      refine ⟨42492110464001891521558493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28328073642667927681038995 42492110464001891521558493)
      ·
        refine ⟨15934541424000709320584435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42492110464001891521558493 15934541424000709320584435)
        ·
          refine ⟨23901812136001063980876653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15934541424000709320584435 23901812136001063980876653)
          ·
            refine ⟨8963179551000398992828745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23901812136001063980876653 8963179551000398992828745)
            ·
              refine ⟨6722384663250299244621559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8963179551000398992828745 6722384663250299244621559)
              ·
                refine ⟨10083576994875448866932339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722384663250299244621559 10083576994875448866932339)
                ·
                  refine ⟨15125365492313173300398509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083576994875448866932339 15125365492313173300398509)
                  ·
                    refine ⟨5672012059617439987649441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15125365492313173300398509 5672012059617439987649441)
                    ·
                      refine ⟨4254009044713079990737081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672012059617439987649441 4254009044713079990737081)
                      ·
                        rfl

theorem cell23_8284653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_8284653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284653 prefixEnd_8284653 := by exact prefixLift 8284653
  have htrace : WordTrace (prefixWord ++ tailWord_8284653) baseStart_8284653 baseEnd_8284653 := by
    simpa [prefixWord, tailWord_8284653, baseEnd_8284653] using wordTrace_append hprefix tailTrace_8284653
  have hstable : (prefixWord ++ tailWord_8284653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284653).length < 2 ^ (prefixWord ++ tailWord_8284653).sum := by decide
  have hdescent : baseEnd_8284653 < baseStart_8284653 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284665 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_8284665 : Nat := 118140960795 + 8284665 * 2 ^ 59
def prefixEnd_8284665 : Nat := 4983230072969 + 3 ^ 40 * 8284665 * 2
def baseEnd_8284665 : Nat := 4254015206480933943787025

theorem tailTrace_8284665 : CollatzResearch.WordTrace tailWord_8284665 prefixEnd_8284665 4254015206480933943787025 := by
  unfold tailWord_8284665
  simp only [CollatzResearch.WordTrace]
  refine ⟨302166556531081087980519449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201444371020720725320346299 302166556531081087980519449)
  ·
    refine ⟨226624917398310815985389587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302166556531081087980519449 226624917398310815985389587)
    ·
      refine ⟨339937376097466223978084381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226624917398310815985389587 339937376097466223978084381)
      ·
        refine ⟨127476516036549833991781643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339937376097466223978084381 127476516036549833991781643)
        ·
          refine ⟨191214774054824750987672465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127476516036549833991781643 191214774054824750987672465)
          ·
            refine ⟨143411080541118563240754349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191214774054824750987672465 143411080541118563240754349)
            ·
              refine ⟨53779155202919461215282881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143411080541118563240754349 53779155202919461215282881)
              ·
                refine ⟨40334366402189595911462161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53779155202919461215282881 40334366402189595911462161)
                ·
                  refine ⟨30250774801642196933596621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40334366402189595911462161 30250774801642196933596621)
                  ·
                    refine ⟨11344040550615823850098733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30250774801642196933596621 11344040550615823850098733)
                    ·
                      refine ⟨4254015206480933943787025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11344040550615823850098733 4254015206480933943787025)
                      ·
                        rfl

theorem cell23_8284665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_8284665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284665 prefixEnd_8284665 := by exact prefixLift 8284665
  have htrace : WordTrace (prefixWord ++ tailWord_8284665) baseStart_8284665 baseEnd_8284665 := by
    simpa [prefixWord, tailWord_8284665, baseEnd_8284665] using wordTrace_append hprefix tailTrace_8284665
  have hstable : (prefixWord ++ tailWord_8284665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284665).length < 2 ^ (prefixWord ++ tailWord_8284665).sum := by decide
  have hdescent : baseEnd_8284665 < baseStart_8284665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284705 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_8284705 : Nat := 118140960795 + 8284705 * 2 ^ 59
def prefixEnd_8284705 : Nat := 4983230072969 + 3 ^ 40 * 8284705 * 2
def baseEnd_8284705 : Nat := 4254035745707113787286841

theorem tailTrace_8284705 : CollatzResearch.WordTrace tailWord_8284705 prefixEnd_8284705 4254035745707113787286841 := by
  unfold tailWord_8284705
  simp only [CollatzResearch.WordTrace]
  refine ⟨302168015450936174811975569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201445343633957449874650379 302168015450936174811975569)
  ·
    refine ⟨226626011588202131108981677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302168015450936174811975569 226626011588202131108981677)
    ·
      refine ⟨84984754345575799165868129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226626011588202131108981677 84984754345575799165868129)
      ·
        refine ⟨63738565759181849374401097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84984754345575799165868129 63738565759181849374401097)
        ·
          refine ⟨47803924319386387030800823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63738565759181849374401097 47803924319386387030800823)
          ·
            refine ⟨71705886479079580546201235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47803924319386387030800823 71705886479079580546201235)
            ·
              refine ⟨107558829718619370819301853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71705886479079580546201235 107558829718619370819301853)
              ·
                refine ⟨40334561144482264057238195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107558829718619370819301853 40334561144482264057238195)
                ·
                  refine ⟨60501841716723396085857293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40334561144482264057238195 60501841716723396085857293)
                  ·
                    refine ⟨22688190643771273532196485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60501841716723396085857293 22688190643771273532196485)
                    ·
                      refine ⟨4254035745707113787286841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22688190643771273532196485 4254035745707113787286841)
                      ·
                        rfl

theorem cell23_8284705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_8284705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284705 prefixEnd_8284705 := by exact prefixLift 8284705
  have htrace : WordTrace (prefixWord ++ tailWord_8284705) baseStart_8284705 baseEnd_8284705 := by
    simpa [prefixWord, tailWord_8284705, baseEnd_8284705] using wordTrace_append hprefix tailTrace_8284705
  have hstable : (prefixWord ++ tailWord_8284705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284705).length < 2 ^ (prefixWord ++ tailWord_8284705).sum := by decide
  have hdescent : baseEnd_8284705 < baseStart_8284705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284715 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 5, 4]
def baseStart_8284715 : Nat := 118140960795 + 8284715 * 2 ^ 59
def prefixEnd_8284715 : Nat := 4983230072969 + 3 ^ 40 * 8284715 * 2
def baseEnd_8284715 : Nat := 1418013626837886249387265

theorem tailTrace_8284715 : CollatzResearch.WordTrace tailWord_8284715 prefixEnd_8284715 1418013626837886249387265 := by
  unfold tailWord_8284715
  simp only [CollatzResearch.WordTrace]
  refine ⟨302168380180899946519839599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201445586787266631013226399 302168380180899946519839599)
  ·
    refine ⟨453252570271349919779759399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302168380180899946519839599 453252570271349919779759399)
    ·
      refine ⟨679878855407024879669639099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453252570271349919779759399 679878855407024879669639099)
      ·
        refine ⟨1019818283110537319504458649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679878855407024879669639099 1019818283110537319504458649)
        ·
          refine ⟨764863712332902989628343987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019818283110537319504458649 764863712332902989628343987)
          ·
            refine ⟨1147295568499354484442515981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764863712332902989628343987 1147295568499354484442515981)
            ·
              refine ⟨430235838187257931665943493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147295568499354484442515981 430235838187257931665943493)
              ·
                refine ⟨80669219660110862187364405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430235838187257931665943493 80669219660110862187364405)
                ·
                  refine ⟨7562739343135393330065413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80669219660110862187364405 7562739343135393330065413)
                  ·
                    refine ⟨1418013626837886249387265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7562739343135393330065413 1418013626837886249387265)
                    ·
                      rfl

theorem cell23_8284715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 4].length) (baseStart_8284715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284715 prefixEnd_8284715 := by exact prefixLift 8284715
  have htrace : WordTrace (prefixWord ++ tailWord_8284715) baseStart_8284715 baseEnd_8284715 := by
    simpa [prefixWord, tailWord_8284715, baseEnd_8284715] using wordTrace_append hprefix tailTrace_8284715
  have hstable : (prefixWord ++ tailWord_8284715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284715).length < 2 ^ (prefixWord ++ tailWord_8284715).sum := by decide
  have hdescent : baseEnd_8284715 < baseStart_8284715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284722 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_8284722 : Nat := 118140960795 + 8284722 * 2 ^ 59
def prefixEnd_8284722 : Nat := 4983230072969 + 3 ^ 40 * 8284722 * 2
def baseEnd_8284722 : Nat := 4254044474878240220774263

theorem tailTrace_8284722 : CollatzResearch.WordTrace tailWord_8284722 prefixEnd_8284722 4254044474878240220774263 := by
  unfold tailWord_8284722
  simp only [CollatzResearch.WordTrace]
  refine ⟨75542158872968646678836105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201445756994583057810229613 75542158872968646678836105)
  ·
    refine ⟨56656619154726485009127079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75542158872968646678836105 56656619154726485009127079)
    ·
      refine ⟨84984928732089727513690619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56656619154726485009127079 84984928732089727513690619)
      ·
        refine ⟨127477393098134591270535929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84984928732089727513690619 127477393098134591270535929)
        ·
          refine ⟨95608044823600943452901947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127477393098134591270535929 95608044823600943452901947)
          ·
            refine ⟨143412067235401415179352921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95608044823600943452901947 143412067235401415179352921)
            ·
              refine ⟨107559050426551061384514691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143412067235401415179352921 107559050426551061384514691)
              ·
                refine ⟨161338575639826592076772037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107559050426551061384514691 161338575639826592076772037)
                ·
                  refine ⟨30250982932467486014394757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161338575639826592076772037 30250982932467486014394757)
                  ·
                    refine ⟨5672059299837653627699017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30250982932467486014394757 5672059299837653627699017)
                    ·
                      refine ⟨4254044474878240220774263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672059299837653627699017 4254044474878240220774263)
                      ·
                        rfl

theorem cell23_8284722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_8284722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284722 prefixEnd_8284722 := by exact prefixLift 8284722
  have htrace : WordTrace (prefixWord ++ tailWord_8284722) baseStart_8284722 baseEnd_8284722 := by
    simpa [prefixWord, tailWord_8284722, baseEnd_8284722] using wordTrace_append hprefix tailTrace_8284722
  have hstable : (prefixWord ++ tailWord_8284722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284722).length < 2 ^ (prefixWord ++ tailWord_8284722).sum := by decide
  have hdescent : baseEnd_8284722 < baseStart_8284722 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284812 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_8284812 : Nat := 118140960795 + 8284812 * 2 ^ 59
def prefixEnd_8284812 : Nat := 4983230072969 + 3 ^ 40 * 8284812 * 2
def baseEnd_8284812 : Nat := 4254090688137144868648849

theorem tailTrace_8284812 : CollatzResearch.WordTrace tailWord_8284812 prefixEnd_8284812 4254090688137144868648849 := by
  unfold tailWord_8284812
  simp only [CollatzResearch.WordTrace]
  refine ⟨151085959030774266043060345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201447945374365688057413793 151085959030774266043060345)
  ·
    refine ⟨113314469273080699532295259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151085959030774266043060345 113314469273080699532295259)
    ·
      refine ⟨169971703909621049298442889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113314469273080699532295259 169971703909621049298442889)
      ·
        refine ⟨127478777932215786973832167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169971703909621049298442889 127478777932215786973832167)
        ·
          refine ⟨191218166898323680460748251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127478777932215786973832167 191218166898323680460748251)
          ·
            refine ⟨286827250347485520691122377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191218166898323680460748251 286827250347485520691122377)
            ·
              refine ⟨215120437760614140518341783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286827250347485520691122377 215120437760614140518341783)
              ·
                refine ⟨322680656640921210777512675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215120437760614140518341783 322680656640921210777512675)
                ·
                  refine ⟨484020984961381816166269013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322680656640921210777512675 484020984961381816166269013)
                  ·
                    refine ⟨5672120917516193158198465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 484020984961381816166269013 5672120917516193158198465)
                    ·
                      refine ⟨4254090688137144868648849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672120917516193158198465 4254090688137144868648849)
                      ·
                        rfl

theorem cell23_8284812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_8284812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284812 prefixEnd_8284812 := by exact prefixLift 8284812
  have htrace : WordTrace (prefixWord ++ tailWord_8284812) baseStart_8284812 baseEnd_8284812 := by
    simpa [prefixWord, tailWord_8284812, baseEnd_8284812] using wordTrace_append hprefix tailTrace_8284812
  have hstable : (prefixWord ++ tailWord_8284812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284812).length < 2 ^ (prefixWord ++ tailWord_8284812).sum := by decide
  have hdescent : baseEnd_8284812 < baseStart_8284812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284815 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_8284815 : Nat := 118140960795 + 8284815 * 2 ^ 59
def prefixEnd_8284815 : Nat := 4983230072969 + 3 ^ 40 * 8284815 * 2
def baseEnd_8284815 : Nat := 4254092228579108356911335

theorem tailTrace_8284815 : CollatzResearch.WordTrace tailWord_8284815 prefixEnd_8284815 4254092228579108356911335 := by
  unfold tailWord_8284815
  simp only [CollatzResearch.WordTrace]
  refine ⟨302172027480537663598479899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201448018320358442398986599 302172027480537663598479899)
  ·
    refine ⟨453258041220806495397719849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302172027480537663598479899 453258041220806495397719849)
    ·
      refine ⟨339943530915604871548289887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453258041220806495397719849 339943530915604871548289887)
      ·
        refine ⟨509915296373407307322434831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339943530915604871548289887 509915296373407307322434831)
        ·
          refine ⟨764872944560110960983652247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509915296373407307322434831 764872944560110960983652247)
          ·
            refine ⟨1147309416840166441475478371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764872944560110960983652247 1147309416840166441475478371)
            ·
              refine ⟨1720964125260249662213217557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147309416840166441475478371 1720964125260249662213217557)
              ·
                refine ⟨80670193371574202916244573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1720964125260249662213217557 80670193371574202916244573)
                ·
                  refine ⟨30251322514340326093591715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80670193371574202916244573 30251322514340326093591715)
                  ·
                    refine ⟨45376983771510489140387573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30251322514340326093591715 45376983771510489140387573)
                    ·
                      refine ⟨4254092228579108356911335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45376983771510489140387573 4254092228579108356911335)
                      ·
                        rfl

theorem cell23_8284815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_8284815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284815 prefixEnd_8284815 := by exact prefixLift 8284815
  have htrace : WordTrace (prefixWord ++ tailWord_8284815) baseStart_8284815 baseEnd_8284815 := by
    simpa [prefixWord, tailWord_8284815, baseEnd_8284815] using wordTrace_append hprefix tailTrace_8284815
  have hstable : (prefixWord ++ tailWord_8284815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284815).length < 2 ^ (prefixWord ++ tailWord_8284815).sum := by decide
  have hdescent : baseEnd_8284815 < baseStart_8284815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284826 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_8284826 : Nat := 118140960795 + 8284826 * 2 ^ 59
def prefixEnd_8284826 : Nat := 4983230072969 + 3 ^ 40 * 8284826 * 2
def baseEnd_8284826 : Nat := 1418032625622102604624595

theorem tailTrace_8284826 : CollatzResearch.WordTrace tailWord_8284826 prefixEnd_8284826 1418032625622102604624595 := by
  unfold tailWord_8284826
  simp only [CollatzResearch.WordTrace]
  refine ⟨75543107170874453119282583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201448285788998541651420221 75543107170874453119282583)
  ·
    refine ⟨113314660756311679678923875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75543107170874453119282583 113314660756311679678923875)
    ·
      refine ⟨169971991134467519518385813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113314660756311679678923875 169971991134467519518385813)
      ·
        refine ⟨7967437084428164977424335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169971991134467519518385813 7967437084428164977424335)
        ·
          refine ⟨11951155626642247466136503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967437084428164977424335 11951155626642247466136503)
          ·
            refine ⟨17926733439963371199204755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951155626642247466136503 17926733439963371199204755)
            ·
              refine ⟨26890100159945056798807133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926733439963371199204755 26890100159945056798807133)
              ·
                refine ⟨10083787559979396299552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26890100159945056798807133 10083787559979396299552675)
                ·
                  refine ⟨15125681339969094449329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083787559979396299552675 15125681339969094449329013)
                  ·
                    refine ⟨1418032625622102604624595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15125681339969094449329013 1418032625622102604624595)
                    ·
                      rfl

theorem cell23_8284826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_8284826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284826 prefixEnd_8284826 := by exact prefixLift 8284826
  have htrace : WordTrace (prefixWord ++ tailWord_8284826) baseStart_8284826 baseEnd_8284826 := by
    simpa [prefixWord, tailWord_8284826, baseEnd_8284826] using wordTrace_append hprefix tailTrace_8284826
  have hstable : (prefixWord ++ tailWord_8284826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284826).length < 2 ^ (prefixWord ++ tailWord_8284826).sum := by decide
  have hdescent : baseEnd_8284826 < baseStart_8284826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284917 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_8284917 : Nat := 118140960795 + 8284917 * 2 ^ 59
def prefixEnd_8284917 : Nat := 4983230072969 + 3 ^ 40 * 8284917 * 2
def baseEnd_8284917 : Nat := 4254144603605866957835867

theorem tailTrace_8284917 : CollatzResearch.WordTrace tailWord_8284917 prefixEnd_8284917 4254144603605866957835867 := by
  unfold tailWord_8284917
  simp only [CollatzResearch.WordTrace]
  refine ⟨302175747726168135018693005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201450498484112090012462003 302175747726168135018693005)
  ·
    refine ⟨113315905397313050632009877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302175747726168135018693005 113315905397313050632009877)
    ·
      refine ⟨5311683065499049248375463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113315905397313050632009877 5311683065499049248375463)
      ·
        refine ⟨7967524598248573872563195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311683065499049248375463 7967524598248573872563195)
        ·
          refine ⟨11951286897372860808844793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967524598248573872563195 11951286897372860808844793)
          ·
            refine ⟨8963465173029645606633595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11951286897372860808844793 8963465173029645606633595)
            ·
              refine ⟨13445197759544468409950393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8963465173029645606633595 13445197759544468409950393)
              ·
                refine ⟨10083898319658351307462795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13445197759544468409950393 10083898319658351307462795)
                ·
                  refine ⟨15125847479487526961194193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10083898319658351307462795 15125847479487526961194193)
                  ·
                    refine ⟨11344385609615645220895645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15125847479487526961194193 11344385609615645220895645)
                    ·
                      refine ⟨4254144603605866957835867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11344385609615645220895645 4254144603605866957835867)
                      ·
                        rfl

theorem cell23_8284917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_8284917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284917 prefixEnd_8284917 := by exact prefixLift 8284917
  have htrace : WordTrace (prefixWord ++ tailWord_8284917) baseStart_8284917 baseEnd_8284917 := by
    simpa [prefixWord, tailWord_8284917, baseEnd_8284917] using wordTrace_append hprefix tailTrace_8284917
  have hstable : (prefixWord ++ tailWord_8284917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284917).length < 2 ^ (prefixWord ++ tailWord_8284917).sum := by decide
  have hdescent : baseEnd_8284917 < baseStart_8284917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284919 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_8284919 : Nat := 118140960795 + 8284919 * 2 ^ 59
def prefixEnd_8284919 : Nat := 4983230072969 + 3 ^ 40 * 8284919 * 2
def baseEnd_8284919 : Nat := 4254145630567175950010857

theorem tailTrace_8284919 : CollatzResearch.WordTrace tailWord_8284919 prefixEnd_8284919 4254145630567175950010857 := by
  unfold tailWord_8284919
  simp only [CollatzResearch.WordTrace]
  refine ⟨302175820672160889360265811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201450547114773926240177207 302175820672160889360265811)
  ·
    refine ⟨453263731008241334040398717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302175820672160889360265811 453263731008241334040398717)
    ·
      refine ⟨169973899128090500265149519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453263731008241334040398717 169973899128090500265149519)
      ·
        refine ⟨254960848692135750397724279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169973899128090500265149519 254960848692135750397724279)
        ·
          refine ⟨382441273038203625596586419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254960848692135750397724279 382441273038203625596586419)
          ·
            refine ⟨573661909557305438394879629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382441273038203625596586419 573661909557305438394879629)
            ·
              refine ⟨215123216083989539398079861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573661909557305438394879629 215123216083989539398079861)
              ·
                refine ⟨20167801507874019318569987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215123216083989539398079861 20167801507874019318569987)
                ·
                  refine ⟨30251702261811028977854981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20167801507874019318569987 30251702261811028977854981)
                  ·
                    refine ⟨5672194174089567933347809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30251702261811028977854981 5672194174089567933347809)
                    ·
                      refine ⟨4254145630567175950010857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672194174089567933347809 4254145630567175950010857)
                      ·
                        rfl

theorem cell23_8284919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_8284919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284919 prefixEnd_8284919 := by exact prefixLift 8284919
  have htrace : WordTrace (prefixWord ++ tailWord_8284919) baseStart_8284919 baseEnd_8284919 := by
    simpa [prefixWord, tailWord_8284919, baseEnd_8284919] using wordTrace_append hprefix tailTrace_8284919
  have hstable : (prefixWord ++ tailWord_8284919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284919).length < 2 ^ (prefixWord ++ tailWord_8284919).sum := by decide
  have hdescent : baseEnd_8284919 < baseStart_8284919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284922 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_8284922 : Nat := 118140960795 + 8284922 * 2 ^ 59
def prefixEnd_8284922 : Nat := 4983230072969 + 3 ^ 40 * 8284922 * 2
def baseEnd_8284922 : Nat := 4254147171009139438273343

theorem tailTrace_8284922 : CollatzResearch.WordTrace tailWord_8284922 prefixEnd_8284922 4254147171009139438273343 := by
  unfold tailWord_8284922
  simp only [CollatzResearch.WordTrace]
  refine ⟨75543982522787505218156255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201450620060766680581750013 75543982522787505218156255)
  ·
    refine ⟨113315973784181257827234383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75543982522787505218156255 113315973784181257827234383)
    ·
      refine ⟨169973960676271886740851575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113315973784181257827234383 169973960676271886740851575)
      ·
        refine ⟨254960941014407830111277363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169973960676271886740851575 254960941014407830111277363)
        ·
          refine ⟨382441411521611745166916045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254960941014407830111277363 382441411521611745166916045)
          ·
            refine ⟨143415529320604404437593517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382441411521611745166916045 143415529320604404437593517)
            ·
              refine ⟨53780823495226651664097569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143415529320604404437593517 53780823495226651664097569)
              ·
                refine ⟨40335617621419988748073177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53780823495226651664097569 40335617621419988748073177)
                ·
                  refine ⟨30251713216064991561054883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40335617621419988748073177 30251713216064991561054883)
                  ·
                    refine ⟨45377569824097487341582325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30251713216064991561054883 45377569824097487341582325)
                    ·
                      refine ⟨4254147171009139438273343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45377569824097487341582325 4254147171009139438273343)
                      ·
                        rfl

theorem cell23_8284922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_8284922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284922 prefixEnd_8284922 := by exact prefixLift 8284922
  have htrace : WordTrace (prefixWord ++ tailWord_8284922) baseStart_8284922 baseEnd_8284922 := by
    simpa [prefixWord, tailWord_8284922, baseEnd_8284922] using wordTrace_append hprefix tailTrace_8284922
  have hstable : (prefixWord ++ tailWord_8284922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284922).length < 2 ^ (prefixWord ++ tailWord_8284922).sum := by decide
  have hdescent : baseEnd_8284922 < baseStart_8284922 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284936 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_8284936 : Nat := 118140960795 + 8284936 * 2 ^ 59
def prefixEnd_8284936 : Nat := 4983230072969 + 3 ^ 40 * 8284936 * 2
def baseEnd_8284936 : Nat := 4254154359738302383498279

theorem tailTrace_8284936 : CollatzResearch.WordTrace tailWord_8284936 prefixEnd_8284936 4254154359738302383498279 := by
  unfold tailWord_8284936
  simp only [CollatzResearch.WordTrace]
  refine ⟨151088220356549650631817331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201450960475399534175756441 151088220356549650631817331)
  ·
    refine ⟨226632330534824475947725997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151088220356549650631817331 226632330534824475947725997)
    ·
      refine ⟨84987123950559178480397249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226632330534824475947725997 84987123950559178480397249)
      ·
        refine ⟨63740342962919383860297937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84987123950559178480397249 63740342962919383860297937)
        ·
          refine ⟨47805257222189537895223453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63740342962919383860297937 47805257222189537895223453)
          ·
            refine ⟨17926971458321076710708795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47805257222189537895223453 17926971458321076710708795)
            ·
              refine ⟨26890457187481615066063193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17926971458321076710708795 26890457187481615066063193)
              ·
                refine ⟨20167842890611211299547395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26890457187481615066063193 20167842890611211299547395)
                ·
                  refine ⟨30251764335916816949321093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20167842890611211299547395 30251764335916816949321093)
                  ·
                    refine ⟨5672205812984403177997705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30251764335916816949321093 5672205812984403177997705)
                    ·
                      refine ⟨4254154359738302383498279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672205812984403177997705 4254154359738302383498279)
                      ·
                        rfl

theorem cell23_8284936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_8284936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284936 prefixEnd_8284936 := by exact prefixLift 8284936
  have htrace : WordTrace (prefixWord ++ tailWord_8284936) baseStart_8284936 baseEnd_8284936 := by
    simpa [prefixWord, tailWord_8284936, baseEnd_8284936] using wordTrace_append hprefix tailTrace_8284936
  have hstable : (prefixWord ++ tailWord_8284936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284936).length < 2 ^ (prefixWord ++ tailWord_8284936).sum := by decide
  have hdescent : baseEnd_8284936 < baseStart_8284936 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284970 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_8284970 : Nat := 118140960795 + 8284970 * 2 ^ 59
def prefixEnd_8284970 : Nat := 4983230072969 + 3 ^ 40 * 8284970 * 2
def baseEnd_8284970 : Nat := 4254171818080555250473123

theorem tailTrace_8284970 : CollatzResearch.WordTrace tailWord_8284970 prefixEnd_8284970 4254171818080555250473123 := by
  unfold tailWord_8284970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75544420198744031267593091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201451787196650750046914909 75544420198744031267593091)
  ·
    refine ⟨113316630298116046901389637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75544420198744031267593091 113316630298116046901389637)
    ·
      refine ⟨21246868180896758794010557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113316630298116046901389637 21246868180896758794010557)
      ·
        refine ⟨7967575567836284547753959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21246868180896758794010557 7967575567836284547753959)
        ·
          refine ⟨11951363351754426821630939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967575567836284547753959 11951363351754426821630939)
          ·
            refine ⟨17927045027631640232446409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951363351754426821630939 17927045027631640232446409)
            ·
              refine ⟨13445283770723730174334807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17927045027631640232446409 13445283770723730174334807)
              ·
                refine ⟨20167925656085595261502211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13445283770723730174334807 20167925656085595261502211)
                ·
                  refine ⟨30251888484128392892253317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20167925656085595261502211 30251888484128392892253317)
                  ·
                    refine ⟨5672229090774073667297497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30251888484128392892253317 5672229090774073667297497)
                    ·
                      refine ⟨4254171818080555250473123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672229090774073667297497 4254171818080555250473123)
                      ·
                        rfl

theorem cell23_8284970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_8284970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284970 prefixEnd_8284970 := by exact prefixLift 8284970
  have htrace : WordTrace (prefixWord ++ tailWord_8284970) baseStart_8284970 baseEnd_8284970 := by
    simpa [prefixWord, tailWord_8284970, baseEnd_8284970] using wordTrace_append hprefix tailTrace_8284970
  have hstable : (prefixWord ++ tailWord_8284970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284970).length < 2 ^ (prefixWord ++ tailWord_8284970).sum := by decide
  have hdescent : baseEnd_8284970 < baseStart_8284970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8284972 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_8284972 : Nat := 118140960795 + 8284972 * 2 ^ 59
def prefixEnd_8284972 : Nat := 4983230072969 + 3 ^ 40 * 8284972 * 2
def baseEnd_8284972 : Nat := 1418057615013954747549371

theorem tailTrace_8284972 : CollatzResearch.WordTrace tailWord_8284972 prefixEnd_8284972 1418057615013954747549371 := by
  unfold tailWord_8284972
  simp only [CollatzResearch.WordTrace]
  refine ⟨151088876870484439705972585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201451835827312586274630113 151088876870484439705972585)
  ·
    refine ⟨113316657652863329779479439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151088876870484439705972585 113316657652863329779479439)
    ·
      refine ⟨169974986479294994669219159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113316657652863329779479439 169974986479294994669219159)
      ·
        refine ⟨254962479718942492003828739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169974986479294994669219159 254962479718942492003828739)
        ·
          refine ⟨382443719578413738005743109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254962479718942492003828739 382443719578413738005743109)
          ·
            refine ⟨71708197420952575876076833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382443719578413738005743109 71708197420952575876076833)
            ·
              refine ⟨53781148065714431907057625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71708197420952575876076833 53781148065714431907057625)
              ·
                refine ⟨40335861049285823930293219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53781148065714431907057625 40335861049285823930293219)
                ·
                  refine ⟨60503791573928735895439829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40335861049285823930293219 60503791573928735895439829)
                  ·
                    refine ⟨1418057615013954747549371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60503791573928735895439829 1418057615013954747549371)
                    ·
                      rfl

theorem cell23_8284972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_8284972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8284972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8284972 prefixEnd_8284972 := by exact prefixLift 8284972
  have htrace : WordTrace (prefixWord ++ tailWord_8284972) baseStart_8284972 baseEnd_8284972 := by
    simpa [prefixWord, tailWord_8284972, baseEnd_8284972] using wordTrace_append hprefix tailTrace_8284972
  have hstable : (prefixWord ++ tailWord_8284972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8284972).length < 2 ^ (prefixWord ++ tailWord_8284972).sum := by decide
  have hdescent : baseEnd_8284972 < baseStart_8284972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8284972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285029 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_8285029 : Nat := 118140960795 + 8285029 * 2 ^ 59
def prefixEnd_8285029 : Nat := 4983230072969 + 3 ^ 40 * 8285029 * 2
def baseEnd_8285029 : Nat := 4254202113439170519635351

theorem tailTrace_8285029 : CollatzResearch.WordTrace tailWord_8285029 prefixEnd_8285029 4254202113439170519635351 := by
  unfold tailWord_8285029
  simp only [CollatzResearch.WordTrace]
  refine ⟨302179832701762378146770141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201453221801174918764513427 302179832701762378146770141)
  ·
    refine ⟨113317437263160891805038803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302179832701762378146770141 113317437263160891805038803)
    ·
      refine ⟨169976155894741337707558205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113317437263160891805038803 169976155894741337707558205)
      ·
        refine ⟨63741058460528001640334327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169976155894741337707558205 63741058460528001640334327)
        ·
          refine ⟨95611587690792002460501491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63741058460528001640334327 95611587690792002460501491)
          ·
            refine ⟨143417381536188003690752237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95611587690792002460501491 143417381536188003690752237)
            ·
              refine ⟨53781518076070501384032089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143417381536188003690752237 53781518076070501384032089)
              ·
                refine ⟨40336138557052876038024067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53781518076070501384032089 40336138557052876038024067)
                ·
                  refine ⟨60504207835579314057036101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40336138557052876038024067 60504207835579314057036101)
                  ·
                    refine ⟨11344538969171121385694269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60504207835579314057036101 11344538969171121385694269)
                    ·
                      refine ⟨4254202113439170519635351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11344538969171121385694269 4254202113439170519635351)
                      ·
                        rfl

theorem cell23_8285029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_8285029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285029 prefixEnd_8285029 := by exact prefixLift 8285029
  have htrace : WordTrace (prefixWord ++ tailWord_8285029) baseStart_8285029 baseEnd_8285029 := by
    simpa [prefixWord, tailWord_8285029, baseEnd_8285029] using wordTrace_append hprefix tailTrace_8285029
  have hstable : (prefixWord ++ tailWord_8285029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285029).length < 2 ^ (prefixWord ++ tailWord_8285029).sum := by decide
  have hdescent : baseEnd_8285029 < baseStart_8285029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285053 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_8285053 : Nat := 118140960795 + 8285053 * 2 ^ 59
def prefixEnd_8285053 : Nat := 4983230072969 + 3 ^ 40 * 8285053 * 2
def baseEnd_8285053 : Nat := 1418071478991626141911747

theorem tailTrace_8285053 : CollatzResearch.WordTrace tailWord_8285053 prefixEnd_8285053 1418071478991626141911747 := by
  unfold tailWord_8285053
  simp only [CollatzResearch.WordTrace]
  refine ⟨302180708053675430245643813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201453805369116953497095875 302180708053675430245643813)
  ·
    refine ⟨56658882760064143171058215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302180708053675430245643813 56658882760064143171058215)
    ·
      refine ⟨84988324140096214756587323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56658882760064143171058215 84988324140096214756587323)
      ·
        refine ⟨127482486210144322134880985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84988324140096214756587323 127482486210144322134880985)
        ·
          refine ⟨95611864657608241601160739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127482486210144322134880985 95611864657608241601160739)
          ·
            refine ⟨143417796986412362401741109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95611864657608241601160739 143417796986412362401741109)
            ·
              refine ⟨13445418467476158975163229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143417796986412362401741109 13445418467476158975163229)
              ·
                refine ⟨5042031925303559615686211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13445418467476158975163229 5042031925303559615686211)
                ·
                  refine ⟨7563047887955339423529317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042031925303559615686211 7563047887955339423529317)
                  ·
                    refine ⟨1418071478991626141911747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7563047887955339423529317 1418071478991626141911747)
                    ·
                      rfl

theorem cell23_8285053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_8285053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285053 prefixEnd_8285053 := by exact prefixLift 8285053
  have htrace : WordTrace (prefixWord ++ tailWord_8285053) baseStart_8285053 baseEnd_8285053 := by
    simpa [prefixWord, tailWord_8285053, baseEnd_8285053] using wordTrace_append hprefix tailTrace_8285053
  have hstable : (prefixWord ++ tailWord_8285053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285053).length < 2 ^ (prefixWord ++ tailWord_8285053).sum := by decide
  have hdescent : baseEnd_8285053 < baseStart_8285053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285079 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 3, 5]
def baseStart_8285079 : Nat := 118140960795 + 8285079 * 2 ^ 59
def prefixEnd_8285079 : Nat := 4983230072969 + 3 ^ 40 * 8285079 * 2
def baseEnd_8285079 : Nat := 1418075929157298441336707

theorem tailTrace_8285079 : CollatzResearch.WordTrace tailWord_8285079 prefixEnd_8285079 1418075929157298441336707 := by
  unfold tailWord_8285079
  simp only [CollatzResearch.WordTrace]
  refine ⟨302181656351581236686090291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201454437567720824457393527 302181656351581236686090291)
  ·
    refine ⟨453272484527371855029135437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302181656351581236686090291 453272484527371855029135437)
    ·
      refine ⟨169977181697764445635925789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453272484527371855029135437 169977181697764445635925789)
      ·
        refine ⟨63741443136661667113472171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169977181697764445635925789 63741443136661667113472171)
        ·
          refine ⟨95612164704992500670208257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63741443136661667113472171 95612164704992500670208257)
          ·
            refine ⟨71709123528744375502656193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95612164704992500670208257 71709123528744375502656193)
            ·
              refine ⟨53781842646558281626992145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71709123528744375502656193 53781842646558281626992145)
              ·
                refine ⟨40336381984918711220244109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53781842646558281626992145 40336381984918711220244109)
                ·
                  refine ⟨15126143244344516707591541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40336381984918711220244109 15126143244344516707591541)
                  ·
                    refine ⟨1418075929157298441336707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15126143244344516707591541 1418075929157298441336707)
                    ·
                      rfl

theorem cell23_8285079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_8285079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285079 prefixEnd_8285079 := by exact prefixLift 8285079
  have htrace : WordTrace (prefixWord ++ tailWord_8285079) baseStart_8285079 baseEnd_8285079 := by
    simpa [prefixWord, tailWord_8285079, baseEnd_8285079] using wordTrace_append hprefix tailTrace_8285079
  have hstable : (prefixWord ++ tailWord_8285079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285079).length < 2 ^ (prefixWord ++ tailWord_8285079).sum := by decide
  have hdescent : baseEnd_8285079 < baseStart_8285079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285099 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4]
def baseStart_8285099 : Nat := 118140960795 + 8285099 * 2 ^ 59
def prefixEnd_8285099 : Nat := 4983230072969 + 3 ^ 40 * 8285099 * 2
def baseEnd_8285099 : Nat := 4254238057084985245760029

theorem tailTrace_8285099 : CollatzResearch.WordTrace tailWord_8285099 prefixEnd_8285099 4254238057084985245760029 := by
  unfold tailWord_8285099
  simp only [CollatzResearch.WordTrace]
  refine ⟨302182385811508780101818351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201454923874339186734545567 302182385811508780101818351)
  ·
    refine ⟨453273578717263170152727527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302182385811508780101818351 453273578717263170152727527)
    ·
      refine ⟨679910368075894755229091291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453273578717263170152727527 679910368075894755229091291)
      ·
        refine ⟨1019865552113842132843636937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679910368075894755229091291 1019865552113842132843636937)
        ·
          refine ⟨764899164085381599632727703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019865552113842132843636937 764899164085381599632727703)
          ·
            refine ⟨1147348746128072399449091555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764899164085381599632727703 1147348746128072399449091555)
            ·
              refine ⟨1721023119192108599173637333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147348746128072399449091555 1721023119192108599173637333)
              ·
                refine ⟨40336479356065045293132125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1721023119192108599173637333 40336479356065045293132125)
                ·
                  refine ⟨15126179758524391984924547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40336479356065045293132125 15126179758524391984924547)
                  ·
                    refine ⟨22689269637786587977386821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15126179758524391984924547 22689269637786587977386821)
                    ·
                      refine ⟨4254238057084985245760029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22689269637786587977386821 4254238057084985245760029)
                      ·
                        rfl

theorem cell23_8285099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 4].length) (baseStart_8285099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285099 prefixEnd_8285099 := by exact prefixLift 8285099
  have htrace : WordTrace (prefixWord ++ tailWord_8285099) baseStart_8285099 baseEnd_8285099 := by
    simpa [prefixWord, tailWord_8285099, baseEnd_8285099] using wordTrace_append hprefix tailTrace_8285099
  have hstable : (prefixWord ++ tailWord_8285099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285099).length < 2 ^ (prefixWord ++ tailWord_8285099).sum := by decide
  have hdescent : baseEnd_8285099 < baseStart_8285099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285113 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 1, 5]
def baseStart_8285113 : Nat := 118140960795 + 8285113 * 2 ^ 59
def prefixEnd_8285113 : Nat := 4983230072969 + 3 ^ 40 * 8285113 * 2
def baseEnd_8285113 : Nat := 1418081748604716063661655

theorem tailTrace_8285113 : CollatzResearch.WordTrace tailWord_8285113 prefixEnd_8285113 1418081748604716063661655 := by
  unfold tailWord_8285113
  simp only [CollatzResearch.WordTrace]
  refine ⟨302182896433458060492827993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201455264288972040328551995 302182896433458060492827993)
  ·
    refine ⟨226637172325093545369620995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302182896433458060492827993 226637172325093545369620995)
    ·
      refine ⟨339955758487640318054431493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226637172325093545369620995 339955758487640318054431493)
      ·
        refine ⟨63741704716432559635205905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339955758487640318054431493 63741704716432559635205905)
        ·
          refine ⟨47806278537324419726404429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63741704716432559635205905 47806278537324419726404429)
          ·
            refine ⟨17927354451496657397401661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47806278537324419726404429 17927354451496657397401661)
            ·
              refine ⟨6722757919311246524025623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17927354451496657397401661 6722757919311246524025623)
              ·
                refine ⟨10084136878966869786038435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722757919311246524025623 10084136878966869786038435)
                ·
                  refine ⟨15126205318450304679057653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10084136878966869786038435 15126205318450304679057653)
                  ·
                    refine ⟨1418081748604716063661655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15126205318450304679057653 1418081748604716063661655)
                    ·
                      rfl

theorem cell23_8285113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_8285113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285113 prefixEnd_8285113 := by exact prefixLift 8285113
  have htrace : WordTrace (prefixWord ++ tailWord_8285113) baseStart_8285113 baseEnd_8285113 := by
    simpa [prefixWord, tailWord_8285113, baseEnd_8285113] using wordTrace_append hprefix tailTrace_8285113
  have hstable : (prefixWord ++ tailWord_8285113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285113).length < 2 ^ (prefixWord ++ tailWord_8285113).sum := by decide
  have hdescent : baseEnd_8285113 < baseStart_8285113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285119 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_8285119 : Nat := 118140960795 + 8285119 * 2 ^ 59
def prefixEnd_8285119 : Nat := 4983230072969 + 3 ^ 40 * 8285119 * 2
def baseEnd_8285119 : Nat := 4254248326698075167509937

theorem tailTrace_8285119 : CollatzResearch.WordTrace tailWord_8285119 prefixEnd_8285119 4254248326698075167509937 := by
  unfold tailWord_8285119
  simp only [CollatzResearch.WordTrace]
  refine ⟨302183115271436323517546411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201455410180957549011697607 302183115271436323517546411)
  ·
    refine ⟨453274672907154485276319617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302183115271436323517546411 453274672907154485276319617)
    ·
      refine ⟨339956004680365863957239713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453274672907154485276319617 339956004680365863957239713)
      ·
        refine ⟨254967003510274397967929785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339956004680365863957239713 254967003510274397967929785)
        ·
          refine ⟨191225252632705798475947339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254967003510274397967929785 191225252632705798475947339)
          ·
            refine ⟨286837878949058697713921009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191225252632705798475947339 286837878949058697713921009)
            ·
              refine ⟨215128409211794023285440757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286837878949058697713921009 215128409211794023285440757)
              ·
                refine ⟨20168288363605689683010071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215128409211794023285440757 20168288363605689683010071)
                ·
                  refine ⟨30252432545408534524515107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20168288363605689683010071 30252432545408534524515107)
                  ·
                    refine ⟨45378648818112801786772661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30252432545408534524515107 45378648818112801786772661)
                    ·
                      refine ⟨4254248326698075167509937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45378648818112801786772661 4254248326698075167509937)
                      ·
                        rfl

theorem cell23_8285119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_8285119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285119 prefixEnd_8285119 := by exact prefixLift 8285119
  have htrace : WordTrace (prefixWord ++ tailWord_8285119) baseStart_8285119 baseEnd_8285119 := by
    simpa [prefixWord, tailWord_8285119, baseEnd_8285119] using wordTrace_append hprefix tailTrace_8285119
  have hstable : (prefixWord ++ tailWord_8285119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285119).length < 2 ^ (prefixWord ++ tailWord_8285119).sum := by decide
  have hdescent : baseEnd_8285119 < baseStart_8285119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285146 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_8285146 : Nat := 118140960795 + 8285146 * 2 ^ 59
def prefixEnd_8285146 : Nat := 4983230072969 + 3 ^ 40 * 8285146 * 2
def baseEnd_8285146 : Nat := 4254262190675746561872313

theorem tailTrace_8285146 : CollatzResearch.WordTrace tailWord_8285146 prefixEnd_8285146 4254262190675746561872313 := by
  unfold tailWord_8285146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75546025010584626782194823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201456066694892338085852861 75546025010584626782194823)
  ·
    refine ⟨113319037515876940173292235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75546025010584626782194823 113319037515876940173292235)
    ·
      refine ⟨169978556273815410259938353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113319037515876940173292235 169978556273815410259938353)
      ·
        refine ⟨127483917205361557694953765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169978556273815410259938353 127483917205361557694953765)
        ·
          refine ⟨23903234476005292067803831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127483917205361557694953765 23903234476005292067803831)
          ·
            refine ⟨35854851714007938101705747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23903234476005292067803831 35854851714007938101705747)
            ·
              refine ⟨53782277571011907152558621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35854851714007938101705747 53782277571011907152558621)
              ·
                refine ⟨20168354089129465182209483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53782277571011907152558621 20168354089129465182209483)
                ·
                  refine ⟨30252531133694197773314225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20168354089129465182209483 30252531133694197773314225)
                  ·
                    refine ⟨22689398350270648329985669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30252531133694197773314225 22689398350270648329985669)
                    ·
                      refine ⟨4254262190675746561872313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22689398350270648329985669 4254262190675746561872313)
                      ·
                        rfl

theorem cell23_8285146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_8285146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285146 prefixEnd_8285146 := by exact prefixLift 8285146
  have htrace : WordTrace (prefixWord ++ tailWord_8285146) baseStart_8285146 baseEnd_8285146 := by
    simpa [prefixWord, tailWord_8285146, baseEnd_8285146] using wordTrace_append hprefix tailTrace_8285146
  have hstable : (prefixWord ++ tailWord_8285146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285146).length < 2 ^ (prefixWord ++ tailWord_8285146).sum := by decide
  have hdescent : baseEnd_8285146 < baseStart_8285146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285167 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 1, 2, 2]
def baseStart_8285167 : Nat := 118140960795 + 8285167 * 2 ^ 59
def prefixEnd_8285167 : Nat := 4983230072969 + 3 ^ 40 * 8285167 * 2
def baseEnd_8285167 : Nat := 4254272973769490979709717

theorem tailTrace_8285167 : CollatzResearch.WordTrace tailWord_8285167 prefixEnd_8285167 4254272973769490979709717 := by
  unfold tailWord_8285167
  simp only [CollatzResearch.WordTrace]
  refine ⟨302184865975262427715293755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201456577316841618476862503 302184865975262427715293755)
  ·
    refine ⟨453277298962893641572940633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302184865975262427715293755 453277298962893641572940633)
    ·
      refine ⟨339957974222170231179705475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453277298962893641572940633 339957974222170231179705475)
      ·
        refine ⟨509936961333255346769558213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339957974222170231179705475 509936961333255346769558213)
        ·
          refine ⟨95613180249985377519292165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509936961333255346769558213 95613180249985377519292165)
          ·
            refine ⟨17927471296872258284867281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95613180249985377519292165 17927471296872258284867281)
            ·
              refine ⟨13445603472654193713650461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17927471296872258284867281 13445603472654193713650461)
              ·
                refine ⟨5042101302245322642618923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13445603472654193713650461 5042101302245322642618923)
                ·
                  refine ⟨7563151953367983963928385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042101302245322642618923 7563151953367983963928385)
                  ·
                    refine ⟨5672363965025987972946289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7563151953367983963928385 5672363965025987972946289)
                    ·
                      refine ⟨4254272973769490979709717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672363965025987972946289 4254272973769490979709717)
                      ·
                        rfl

theorem cell23_8285167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 2, 2].length) (baseStart_8285167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285167 prefixEnd_8285167 := by exact prefixLift 8285167
  have htrace : WordTrace (prefixWord ++ tailWord_8285167) baseStart_8285167 baseEnd_8285167 := by
    simpa [prefixWord, tailWord_8285167, baseEnd_8285167] using wordTrace_append hprefix tailTrace_8285167
  have hstable : (prefixWord ++ tailWord_8285167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285167).length < 2 ^ (prefixWord ++ tailWord_8285167).sum := by decide
  have hdescent : baseEnd_8285167 < baseStart_8285167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285173 : List Nat := [1, 3, 5, 2, 1, 1, 10]
def baseStart_8285173 : Nat := 118140960795 + 8285173 * 2 ^ 59
def prefixEnd_8285173 : Nat := 4983230072969 + 3 ^ 40 * 8285173 * 2
def baseEnd_8285173 : Nat := 52521926600659480941169

theorem tailTrace_8285173 : CollatzResearch.WordTrace tailWord_8285173 prefixEnd_8285173 52521926600659480941169 := by
  unfold tailWord_8285173
  simp only [CollatzResearch.WordTrace]
  refine ⟨302185084813240690740012173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201456723208827127160008115 302185084813240690740012173)
  ·
    refine ⟨113319406804965259027504565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302185084813240690740012173 113319406804965259027504565)
    ·
      refine ⟨10623694387965493033828553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113319406804965259027504565 10623694387965493033828553)
      ·
        refine ⟨7967770790974119775371415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10623694387965493033828553 7967770790974119775371415)
        ·
          refine ⟨11951656186461179663057123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967770790974119775371415 11951656186461179663057123)
          ·
            refine ⟨17927484279691769494585685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951656186461179663057123 17927484279691769494585685)
            ·
              refine ⟨52521926600659480941169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17927484279691769494585685 52521926600659480941169)
              ·
                rfl

theorem cell23_8285173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 10].length) (baseStart_8285173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285173 prefixEnd_8285173 := by exact prefixLift 8285173
  have htrace : WordTrace (prefixWord ++ tailWord_8285173) baseStart_8285173 baseEnd_8285173 := by
    simpa [prefixWord, tailWord_8285173, baseEnd_8285173] using wordTrace_append hprefix tailTrace_8285173
  have hstable : (prefixWord ++ tailWord_8285173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285173).length < 2 ^ (prefixWord ++ tailWord_8285173).sum := by decide
  have hdescent : baseEnd_8285173 < baseStart_8285173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285210 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_8285210 : Nat := 118140960795 + 8285210 * 2 ^ 59
def prefixEnd_8285210 : Nat := 4983230072969 + 3 ^ 40 * 8285210 * 2
def baseEnd_8285210 : Nat := 4254295053437634311472019

theorem tailTrace_8285210 : CollatzResearch.WordTrace tailWord_8285210 prefixEnd_8285210 4254295053437634311472019 := by
  unfold tailWord_8285210
  simp only [CollatzResearch.WordTrace]
  refine ⟨75546608578526661514777271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201457622876071097372739389 75546608578526661514777271)
  ·
    refine ⟨113319912867789992272165907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75546608578526661514777271 113319912867789992272165907)
    ·
      refine ⟨169979869301684988408248861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113319912867789992272165907 169979869301684988408248861)
      ·
        refine ⟨63742450988131870653093323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169979869301684988408248861 63742450988131870653093323)
        ·
          refine ⟨95613676482197805979639985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63742450988131870653093323 95613676482197805979639985)
          ·
            refine ⟨71710257361648354484729989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95613676482197805979639985 71710257361648354484729989)
            ·
              refine ⟨13445673255309066465886873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71710257361648354484729989 13445673255309066465886873)
              ·
                refine ⟨10084254941481799849415155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13445673255309066465886873 10084254941481799849415155)
                ·
                  refine ⟨15126382412222699774122733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10084254941481799849415155 15126382412222699774122733)
                  ·
                    refine ⟨5672393404583512415296025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15126382412222699774122733 5672393404583512415296025)
                    ·
                      refine ⟨4254295053437634311472019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672393404583512415296025 4254295053437634311472019)
                      ·
                        rfl

theorem cell23_8285210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_8285210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285210 prefixEnd_8285210 := by exact prefixLift 8285210
  have htrace : WordTrace (prefixWord ++ tailWord_8285210) baseStart_8285210 baseEnd_8285210 := by
    simpa [prefixWord, tailWord_8285210, baseEnd_8285210] using wordTrace_append hprefix tailTrace_8285210
  have hstable : (prefixWord ++ tailWord_8285210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285210).length < 2 ^ (prefixWord ++ tailWord_8285210).sum := by decide
  have hdescent : baseEnd_8285210 < baseStart_8285210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_8285239 : Nat := 118140960795 + 8285239 * 2 ^ 59
def prefixEnd_8285239 : Nat := 4983230072969 + 3 ^ 40 * 8285239 * 2
def baseEnd_8285239 : Nat := 4254309944376614698009385

theorem tailTrace_8285239 : CollatzResearch.WordTrace tailWord_8285239 prefixEnd_8285239 4254309944376614698009385 := by
  unfold tailWord_8285239
  simp only [CollatzResearch.WordTrace]
  refine ⟨302187492031001584011914771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201458328020667722674609847 302187492031001584011914771)
  ·
    refine ⟨453281238046502376017872157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302187492031001584011914771 453281238046502376017872157)
    ·
      refine ⟨169980464267438391006702059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453281238046502376017872157 169980464267438391006702059)
      ·
        refine ⟨254970696401157586510053089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169980464267438391006702059 254970696401157586510053089)
        ·
          refine ⟨191228022300868189882539817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254970696401157586510053089 191228022300868189882539817)
          ·
            refine ⟨143421016725651142411904863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191228022300868189882539817 143421016725651142411904863)
            ·
              refine ⟨215131525088476713617857295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143421016725651142411904863 215131525088476713617857295)
              ·
                refine ⟨322697287632715070426785943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215131525088476713617857295 322697287632715070426785943)
                ·
                  refine ⟨484045931449072605640178915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322697287632715070426785943 484045931449072605640178915)
                  ·
                    refine ⟨726068897173608908460268373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484045931449072605640178915 726068897173608908460268373)
                    ·
                      refine ⟨4254309944376614698009385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 726068897173608908460268373 4254309944376614698009385)
                      ·
                        rfl

theorem cell23_8285239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_8285239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285239 prefixEnd_8285239 := by exact prefixLift 8285239
  have htrace : WordTrace (prefixWord ++ tailWord_8285239) baseStart_8285239 baseEnd_8285239 := by
    simpa [prefixWord, tailWord_8285239, baseEnd_8285239] using wordTrace_append hprefix tailTrace_8285239
  have hstable : (prefixWord ++ tailWord_8285239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285239).length < 2 ^ (prefixWord ++ tailWord_8285239).sum := by decide
  have hdescent : baseEnd_8285239 < baseStart_8285239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285240 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_8285240 : Nat := 118140960795 + 8285240 * 2 ^ 59
def prefixEnd_8285240 : Nat := 4983230072969 + 3 ^ 40 * 8285240 * 2
def baseEnd_8285240 : Nat := 4254310457857269194096881

theorem tailTrace_8285240 : CollatzResearch.WordTrace tailWord_8285240 prefixEnd_8285240 4254310457857269194096881 := by
  unfold tailWord_8285240
  simp only [CollatzResearch.WordTrace]
  refine ⟨151093764251998980591350587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201458352335998640788467449 151093764251998980591350587)
  ·
    refine ⟨226640646377998470887025881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151093764251998980591350587 226640646377998470887025881)
    ·
      refine ⟨169980484783498853165269411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226640646377998470887025881 169980484783498853165269411)
      ·
        refine ⟨254970727175248279747904117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169980484783498853165269411 254970727175248279747904117)
        ·
          refine ⟨23903505672679526226366011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 254970727175248279747904117 23903505672679526226366011)
          ·
            refine ⟨35855258509019289339549017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23903505672679526226366011 35855258509019289339549017)
            ·
              refine ⟨26891443881764467004661763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35855258509019289339549017 26891443881764467004661763)
              ·
                refine ⟨40337165822646700506992645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26891443881764467004661763 40337165822646700506992645)
                ·
                  refine ⟨7563218591746256345061121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40337165822646700506992645 7563218591746256345061121)
                  ·
                    refine ⟨5672413943809692258795841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7563218591746256345061121 5672413943809692258795841)
                    ·
                      refine ⟨4254310457857269194096881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672413943809692258795841 4254310457857269194096881)
                      ·
                        rfl

theorem cell23_8285240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_8285240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285240 prefixEnd_8285240 := by exact prefixLift 8285240
  have htrace : WordTrace (prefixWord ++ tailWord_8285240) baseStart_8285240 baseEnd_8285240 := by
    simpa [prefixWord, tailWord_8285240, baseEnd_8285240] using wordTrace_append hprefix tailTrace_8285240
  have hstable : (prefixWord ++ tailWord_8285240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285240).length < 2 ^ (prefixWord ++ tailWord_8285240).sum := by decide
  have hdescent : baseEnd_8285240 < baseStart_8285240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285256 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_8285256 : Nat := 118140960795 + 8285256 * 2 ^ 59
def prefixEnd_8285256 : Nat := 4983230072969 + 3 ^ 40 * 8285256 * 2
def baseEnd_8285256 : Nat := 4254318673547741131496807

theorem tailTrace_8285256 : CollatzResearch.WordTrace tailWord_8285256 prefixEnd_8285256 4254318673547741131496807 := by
  unfold tailWord_8285256
  simp only [CollatzResearch.WordTrace]
  refine ⟨151094056035969997957641811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201458741381293330610189081 151094056035969997957641811)
  ·
    refine ⟨226641084053954996936462717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151094056035969997957641811 226641084053954996936462717)
    ·
      refine ⟨84990406520233123851173519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226641084053954996936462717 84990406520233123851173519)
      ·
        refine ⟨127485609780349685776760279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84990406520233123851173519 127485609780349685776760279)
        ·
          refine ⟨191228414670524528665140419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127485609780349685776760279 191228414670524528665140419)
          ·
            refine ⟨286842622005786792997710629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191228414670524528665140419 286842622005786792997710629)
            ·
              refine ⟨53782991626085023687070743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286842622005786792997710629 53782991626085023687070743)
              ·
                refine ⟨80674487439127535530606115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53782991626085023687070743 80674487439127535530606115)
                ·
                  refine ⟨121011731158691303295909173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80674487439127535530606115 121011731158691303295909173)
                  ·
                    refine ⟨11344849796127309683991485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121011731158691303295909173 11344849796127309683991485)
                    ·
                      refine ⟨4254318673547741131496807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11344849796127309683991485 4254318673547741131496807)
                      ·
                        rfl

theorem cell23_8285256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_8285256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285256 prefixEnd_8285256 := by exact prefixLift 8285256
  have htrace : WordTrace (prefixWord ++ tailWord_8285256) baseStart_8285256 baseEnd_8285256 := by
    simpa [prefixWord, tailWord_8285256, baseEnd_8285256] using wordTrace_append hprefix tailTrace_8285256
  have hstable : (prefixWord ++ tailWord_8285256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285256).length < 2 ^ (prefixWord ++ tailWord_8285256).sum := by decide
  have hdescent : baseEnd_8285256 < baseStart_8285256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285293 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_8285293 : Nat := 118140960795 + 8285293 * 2 ^ 59
def prefixEnd_8285293 : Nat := 4983230072969 + 3 ^ 40 * 8285293 * 2
def baseEnd_8285293 : Nat := 1418112557443985828911379

theorem tailTrace_8285293 : CollatzResearch.WordTrace tailWord_8285293 prefixEnd_8285293 1418112557443985828911379 := by
  unfold tailWord_8285293
  simp only [CollatzResearch.WordTrace]
  refine ⟨302189461572805951234380533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201459641048537300822920355 302189461572805951234380533)
  ·
    refine ⟨28330262022450557928223175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302189461572805951234380533 28330262022450557928223175)
    ·
      refine ⟨42495393033675836892334763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28330262022450557928223175 42495393033675836892334763)
      ·
        refine ⟨63743089550513755338502145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42495393033675836892334763 63743089550513755338502145)
        ·
          refine ⟨47807317162885316503876609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63743089550513755338502145 47807317162885316503876609)
          ·
            refine ⟨35855487872163987377907457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47807317162885316503876609 35855487872163987377907457)
            ·
              refine ⟨26891615904122990533430593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35855487872163987377907457 26891615904122990533430593)
              ·
                refine ⟨20168711928092242900072945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26891615904122990533430593 20168711928092242900072945)
                ·
                  refine ⟨15126533946069182175054709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20168711928092242900072945 15126533946069182175054709)
                  ·
                    refine ⟨1418112557443985828911379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15126533946069182175054709 1418112557443985828911379)
                    ·
                      rfl

theorem cell23_8285293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_8285293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285293 prefixEnd_8285293 := by exact prefixLift 8285293
  have htrace : WordTrace (prefixWord ++ tailWord_8285293) baseStart_8285293 baseEnd_8285293 := by
    simpa [prefixWord, tailWord_8285293, baseEnd_8285293] using wordTrace_append hprefix tailTrace_8285293
  have hstable : (prefixWord ++ tailWord_8285293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285293).length < 2 ^ (prefixWord ++ tailWord_8285293).sum := by decide
  have hdescent : baseEnd_8285293 < baseStart_8285293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285330 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_8285330 : Nat := 118140960795 + 8285330 * 2 ^ 59
def prefixEnd_8285330 : Nat := 4983230072969 + 3 ^ 40 * 8285330 * 2
def baseEnd_8285330 : Nat := 4254356671116173841971467

theorem tailTrace_8285330 : CollatzResearch.WordTrace tailWord_8285330 prefixEnd_8285330 4254356671116173841971467 := by
  unfold tailWord_8285330
  simp only [CollatzResearch.WordTrace]
  refine ⟨75547702768417976638369361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201460540715781271035651629 75547702768417976638369361)
  ·
    refine ⟨56660777076313482478777021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75547702768417976638369361 56660777076313482478777021)
    ·
      refine ⟨21247791403617555929541383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56660777076313482478777021 21247791403617555929541383)
      ·
        refine ⟨31871687105426333894312075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21247791403617555929541383 31871687105426333894312075)
        ·
          refine ⟨47807530658139500841468113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31871687105426333894312075 47807530658139500841468113)
          ·
            refine ⟨35855647993604625631101085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47807530658139500841468113 35855647993604625631101085)
            ·
              refine ⟨13445867997601734611662907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35855647993604625631101085 13445867997601734611662907)
              ·
                refine ⟨20168801996402601917494361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13445867997601734611662907 20168801996402601917494361)
                ·
                  refine ⟨15126601497301951438120771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20168801996402601917494361 15126601497301951438120771)
                  ·
                    refine ⟨22689902245952927157181157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15126601497301951438120771 22689902245952927157181157)
                    ·
                      refine ⟨4254356671116173841971467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22689902245952927157181157 4254356671116173841971467)
                      ·
                        rfl

theorem cell23_8285330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_8285330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285330 prefixEnd_8285330 := by exact prefixLift 8285330
  have htrace : WordTrace (prefixWord ++ tailWord_8285330) baseStart_8285330 baseEnd_8285330 := by
    simpa [prefixWord, tailWord_8285330, baseEnd_8285330] using wordTrace_append hprefix tailTrace_8285330
  have hstable : (prefixWord ++ tailWord_8285330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285330).length < 2 ^ (prefixWord ++ tailWord_8285330).sum := by decide
  have hdescent : baseEnd_8285330 < baseStart_8285330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285333 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_8285333 : Nat := 118140960795 + 8285333 * 2 ^ 59
def prefixEnd_8285333 : Nat := 4983230072969 + 3 ^ 40 * 8285333 * 2
def baseEnd_8285333 : Nat := 4254358211558137330233953

theorem tailTrace_8285333 : CollatzResearch.WordTrace tailWord_8285333 prefixEnd_8285333 4254358211558137330233953 := by
  unfold tailWord_8285333
  simp only [CollatzResearch.WordTrace]
  refine ⟨302190920492661038065836653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201460613661774025377224435 302190920492661038065836653)
  ·
    refine ⟨113321595184747889274688745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302190920492661038065836653 113321595184747889274688745)
    ·
      refine ⟨84991196388560916956016559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113321595184747889274688745 84991196388560916956016559)
      ·
        refine ⟨127486794582841375434024839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84991196388560916956016559 127486794582841375434024839)
        ·
          refine ⟨191230191874262063151037259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127486794582841375434024839 191230191874262063151037259)
          ·
            refine ⟨286845287811393094726555889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191230191874262063151037259 286845287811393094726555889)
            ·
              refine ⟨215133965858544821044916917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286845287811393094726555889 215133965858544821044916917)
              ·
                refine ⟨20168809299238576972960961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215133965858544821044916917 20168809299238576972960961)
                ·
                  refine ⟨15126606974428932729720721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20168809299238576972960961 15126606974428932729720721)
                  ·
                    refine ⟨11344955230821699547290541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15126606974428932729720721 11344955230821699547290541)
                    ·
                      refine ⟨4254358211558137330233953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11344955230821699547290541 4254358211558137330233953)
                      ·
                        rfl

theorem cell23_8285333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_8285333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285333 prefixEnd_8285333 := by exact prefixLift 8285333
  have htrace : WordTrace (prefixWord ++ tailWord_8285333) baseStart_8285333 baseEnd_8285333 := by
    simpa [prefixWord, tailWord_8285333, baseEnd_8285333] using wordTrace_append hprefix tailTrace_8285333
  have hstable : (prefixWord ++ tailWord_8285333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285333).length < 2 ^ (prefixWord ++ tailWord_8285333).sum := by decide
  have hdescent : baseEnd_8285333 < baseStart_8285333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285357 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_8285357 : Nat := 118140960795 + 8285357 * 2 ^ 59
def prefixEnd_8285357 : Nat := 4983230072969 + 3 ^ 40 * 8285357 * 2
def baseEnd_8285357 : Nat := 1418123511697948412111281

theorem tailTrace_8285357 : CollatzResearch.WordTrace tailWord_8285357 prefixEnd_8285357 1418123511697948412111281 := by
  unfold tailWord_8285357
  simp only [CollatzResearch.WordTrace]
  refine ⟨302191795844574090164710325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201461197229716060109806883 302191795844574090164710325)
  ·
    refine ⟨28330480860428820952941593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302191795844574090164710325 28330480860428820952941593)
    ·
      refine ⟨21247860645321615714706195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28330480860428820952941593 21247860645321615714706195)
      ·
        refine ⟨31871790967982423572059293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21247860645321615714706195 31871790967982423572059293)
        ·
          refine ⟨11951921612993408839522235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31871790967982423572059293 11951921612993408839522235)
          ·
            refine ⟨17927882419490113259283353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11951921612993408839522235 17927882419490113259283353)
            ·
              refine ⟨13445911814617584944462515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17927882419490113259283353 13445911814617584944462515)
              ·
                refine ⟨20168867721926377416693773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13445911814617584944462515 20168867721926377416693773)
                ·
                  refine ⟨7563325395722391531260165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20168867721926377416693773 7563325395722391531260165)
                  ·
                    refine ⟨1418123511697948412111281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7563325395722391531260165 1418123511697948412111281)
                    ·
                      rfl

theorem cell23_8285357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_8285357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285357 prefixEnd_8285357 := by exact prefixLift 8285357
  have htrace : WordTrace (prefixWord ++ tailWord_8285357) baseStart_8285357 baseEnd_8285357 := by
    simpa [prefixWord, tailWord_8285357, baseEnd_8285357] using wordTrace_append hprefix tailTrace_8285357
  have hstable : (prefixWord ++ tailWord_8285357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285357).length < 2 ^ (prefixWord ++ tailWord_8285357).sum := by decide
  have hdescent : baseEnd_8285357 < baseStart_8285357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285403 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 6, 2]
def baseStart_8285403 : Nat := 118140960795 + 8285403 * 2 ^ 59
def prefixEnd_8285403 : Nat := 4983230072969 + 3 ^ 40 * 8285403 * 2
def baseEnd_8285403 : Nat := 4254394155203952056358631

theorem tailTrace_8285403 : CollatzResearch.WordTrace tailWord_8285403 prefixEnd_8285403 4254394155203952056358631 := by
  unfold tailWord_8285403
  simp only [CollatzResearch.WordTrace]
  refine ⟨302193473602407440020884863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201462315734938293347256575 302193473602407440020884863)
  ·
    refine ⟨453290210403611160031327295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302193473602407440020884863 453290210403611160031327295)
    ·
      refine ⟨679935315605416740046990943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453290210403611160031327295 679935315605416740046990943)
      ·
        refine ⟨1019902973408125110070486415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679935315605416740046990943 1019902973408125110070486415)
        ·
          refine ⟨1529854460112187665105729623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019902973408125110070486415 1529854460112187665105729623)
          ·
            refine ⟨2294781690168281497658594435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1529854460112187665105729623 2294781690168281497658594435)
            ·
              refine ⟨3442172535252422246487891653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2294781690168281497658594435 3442172535252422246487891653)
              ·
                refine ⟨645407350359829171216479685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3442172535252422246487891653 645407350359829171216479685)
                ·
                  refine ⟨121013878192467969603089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645407350359829171216479685 121013878192467969603089941)
                  ·
                    refine ⟨5672525540271936075144841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121013878192467969603089941 5672525540271936075144841)
                    ·
                      refine ⟨4254394155203952056358631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672525540271936075144841 4254394155203952056358631)
                      ·
                        rfl

theorem cell23_8285403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 6, 2].length) (baseStart_8285403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285403 prefixEnd_8285403 := by exact prefixLift 8285403
  have htrace : WordTrace (prefixWord ++ tailWord_8285403) baseStart_8285403 baseEnd_8285403 := by
    simpa [prefixWord, tailWord_8285403, baseEnd_8285403] using wordTrace_append hprefix tailTrace_8285403
  have hstable : (prefixWord ++ tailWord_8285403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285403).length < 2 ^ (prefixWord ++ tailWord_8285403).sum := by decide
  have hdescent : baseEnd_8285403 < baseStart_8285403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285433 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_8285433 : Nat := 118140960795 + 8285433 * 2 ^ 59
def prefixEnd_8285433 : Nat := 4983230072969 + 3 ^ 40 * 8285433 * 2
def baseEnd_8285433 : Nat := 4254409559623586938983493

theorem tailTrace_8285433 : CollatzResearch.WordTrace tailWord_8285433 prefixEnd_8285433 4254409559623586938983493 := by
  unfold tailWord_8285433
  simp only [CollatzResearch.WordTrace]
  refine ⟨302194567792298755144476953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201463045194865836762984635 302194567792298755144476953)
  ·
    refine ⟨226645925844224066358357715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302194567792298755144476953 226645925844224066358357715)
    ·
      refine ⟨339968888766336099537536573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226645925844224066358357715 339968888766336099537536573)
      ·
        refine ⟨127488333287376037326576215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339968888766336099537536573 127488333287376037326576215)
        ·
          refine ⟨191232499931064055989864323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127488333287376037326576215 191232499931064055989864323)
          ·
            refine ⟨286848749896596083984796485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191232499931064055989864323 286848749896596083984796485)
            ·
              refine ⟨53784140605611765747149341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286848749896596083984796485 53784140605611765747149341)
              ·
                refine ⟨20169052727104412155181003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53784140605611765747149341 20169052727104412155181003)
                ·
                  refine ⟨30253579090656618232771505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20169052727104412155181003 30253579090656618232771505)
                  ·
                    refine ⟨22690184317992463674578629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30253579090656618232771505 22690184317992463674578629)
                    ·
                      refine ⟨4254409559623586938983493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690184317992463674578629 4254409559623586938983493)
                      ·
                        rfl

theorem cell23_8285433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_8285433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285433 prefixEnd_8285433 := by exact prefixLift 8285433
  have htrace : WordTrace (prefixWord ++ tailWord_8285433) baseStart_8285433 baseEnd_8285433 := by
    simpa [prefixWord, tailWord_8285433, baseEnd_8285433] using wordTrace_append hprefix tailTrace_8285433
  have hstable : (prefixWord ++ tailWord_8285433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285433).length < 2 ^ (prefixWord ++ tailWord_8285433).sum := by decide
  have hdescent : baseEnd_8285433 < baseStart_8285433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285457 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_8285457 : Nat := 118140960795 + 8285457 * 2 ^ 59
def prefixEnd_8285457 : Nat := 4983230072969 + 3 ^ 40 * 8285457 * 2
def baseEnd_8285457 : Nat := 4254421883159294845083383

theorem tailTrace_8285457 : CollatzResearch.WordTrace tailWord_8285457 prefixEnd_8285457 4254421883159294845083383 := by
  unfold tailWord_8285457
  simp only [CollatzResearch.WordTrace]
  refine ⟨302195443144211807243350625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201463628762807871495567083 302195443144211807243350625)
  ·
    refine ⟨226646582358158855432512969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302195443144211807243350625 226646582358158855432512969)
    ·
      refine ⟨169984936768619141574384727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226646582358158855432512969 169984936768619141574384727)
      ·
        refine ⟨254977405152928712361577091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169984936768619141574384727 254977405152928712361577091)
        ·
          refine ⟨382466107729393068542365637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254977405152928712361577091 382466107729393068542365637)
          ·
            refine ⟨71712395199261200351693557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382466107729393068542365637 71712395199261200351693557)
            ·
              refine ⟨6723037049930737532971271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71712395199261200351693557 6723037049930737532971271)
              ·
                refine ⟨10084555574896106299456907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723037049930737532971271 10084555574896106299456907)
                ·
                  refine ⟨15126833362344159449185361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10084555574896106299456907 15126833362344159449185361)
                  ·
                    refine ⟨11345125021758119586889021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15126833362344159449185361 11345125021758119586889021)
                    ·
                      refine ⟨4254421883159294845083383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11345125021758119586889021 4254421883159294845083383)
                      ·
                        rfl

theorem cell23_8285457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_8285457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285457 prefixEnd_8285457 := by exact prefixLift 8285457
  have htrace : WordTrace (prefixWord ++ tailWord_8285457) baseStart_8285457 baseEnd_8285457 := by
    simpa [prefixWord, tailWord_8285457, baseEnd_8285457] using wordTrace_append hprefix tailTrace_8285457
  have hstable : (prefixWord ++ tailWord_8285457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285457).length < 2 ^ (prefixWord ++ tailWord_8285457).sum := by decide
  have hdescent : baseEnd_8285457 < baseStart_8285457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285471 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 1, 2, 2]
def baseStart_8285471 : Nat := 118140960795 + 8285471 * 2 ^ 59
def prefixEnd_8285471 : Nat := 4983230072969 + 3 ^ 40 * 8285471 * 2
def baseEnd_8285471 : Nat := 4254429071888457790308319

theorem tailTrace_8285471 : CollatzResearch.WordTrace tailWord_8285471 prefixEnd_8285471 4254429071888457790308319 := by
  unfold tailWord_8285471
  simp only [CollatzResearch.WordTrace]
  refine ⟨302195953766161087634360267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201463969177440725089573511 302195953766161087634360267)
  ·
    refine ⟨453293930649241631451540401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302195953766161087634360267 453293930649241631451540401)
    ·
      refine ⟨339970447986931223588655301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453293930649241631451540401 339970447986931223588655301)
      ·
        refine ⟨63744458997549604422872869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339970447986931223588655301 63744458997549604422872869)
        ·
          refine ⟨11952086062040550829288663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63744458997549604422872869 11952086062040550829288663)
          ·
            refine ⟨17928129093060826243932995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952086062040550829288663 17928129093060826243932995)
            ·
              refine ⟨26892193639591239365899493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17928129093060826243932995 26892193639591239365899493)
              ·
                refine ⟨5042286307423357381106155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26892193639591239365899493 5042286307423357381106155)
                ·
                  refine ⟨7563429461135036071659233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042286307423357381106155 7563429461135036071659233)
                  ·
                    refine ⟨5672572095851277053744425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7563429461135036071659233 5672572095851277053744425)
                    ·
                      refine ⟨4254429071888457790308319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672572095851277053744425 4254429071888457790308319)
                      ·
                        rfl

theorem cell23_8285471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_8285471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285471 prefixEnd_8285471 := by exact prefixLift 8285471
  have htrace : WordTrace (prefixWord ++ tailWord_8285471) baseStart_8285471 baseEnd_8285471 := by
    simpa [prefixWord, tailWord_8285471, baseEnd_8285471] using wordTrace_append hprefix tailTrace_8285471
  have hstable : (prefixWord ++ tailWord_8285471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285471).length < 2 ^ (prefixWord ++ tailWord_8285471).sum := by decide
  have hdescent : baseEnd_8285471 < baseStart_8285471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285494 : List Nat := [5, 1, 2, 3, 1, 1, 3, 7]
def baseStart_8285494 : Nat := 118140960795 + 8285494 * 2 ^ 59
def prefixEnd_8285494 : Nat := 4983230072969 + 3 ^ 40 * 8285494 * 2
def baseEnd_8285494 : Nat := 157571884516426340752619

theorem tailTrace_8285494 : CollatzResearch.WordTrace tailWord_8285494 prefixEnd_8285494 157571884516426340752619 := by
  unfold tailWord_8285494
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887299540317360160152971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201464528430051841708298357 18887299540317360160152971)
  ·
    refine ⟨28330949310476040240229457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18887299540317360160152971 28330949310476040240229457)
    ·
      refine ⟨21248211982857030180172093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28330949310476040240229457 21248211982857030180172093)
      ·
        refine ⟨7968079493571386317564535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21248211982857030180172093 7968079493571386317564535)
        ·
          refine ⟨11952119240357079476346803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968079493571386317564535 11952119240357079476346803)
          ·
            refine ⟨17928178860535619214520205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952119240357079476346803 17928178860535619214520205)
            ·
              refine ⟨6723067072700857205445077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17928178860535619214520205 6723067072700857205445077)
              ·
                refine ⟨157571884516426340752619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6723067072700857205445077 157571884516426340752619)
                ·
                  rfl

theorem cell23_8285494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_8285494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285494 prefixEnd_8285494 := by exact prefixLift 8285494
  have htrace : WordTrace (prefixWord ++ tailWord_8285494) baseStart_8285494 baseEnd_8285494 := by
    simpa [prefixWord, tailWord_8285494, baseEnd_8285494] using wordTrace_append hprefix tailTrace_8285494
  have hstable : (prefixWord ++ tailWord_8285494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285494).length < 2 ^ (prefixWord ++ tailWord_8285494).sum := by decide
  have hdescent : baseEnd_8285494 < baseStart_8285494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285513 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_8285513 : Nat := 118140960795 + 8285513 * 2 ^ 59
def prefixEnd_8285513 : Nat := 4983230072969 + 3 ^ 40 * 8285513 * 2
def baseEnd_8285513 : Nat := 4254450638075946625983125

theorem tailTrace_8285513 : CollatzResearch.WordTrace tailWord_8285513 prefixEnd_8285513 4254450638075946625983125 := by
  unfold tailWord_8285513
  simp only [CollatzResearch.WordTrace]
  refine ⟨302197485632008928807389193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201464990421339285871592795 302197485632008928807389193)
  ·
    refine ⟨226648114224006696605541895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302197485632008928807389193 226648114224006696605541895)
    ·
      refine ⟨339972171336010044908312843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226648114224006696605541895 339972171336010044908312843)
      ·
        refine ⟨509958257004015067362469265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339972171336010044908312843 509958257004015067362469265)
        ·
          refine ⟨382468692753011300521851949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509958257004015067362469265 382468692753011300521851949)
          ·
            refine ⟨143425759782379237695694481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382468692753011300521851949 143425759782379237695694481)
            ·
              refine ⟨107569319836784428271770861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143425759782379237695694481 107569319836784428271770861)
              ·
                refine ⟨40338494938794160601914073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107569319836784428271770861 40338494938794160601914073)
                ·
                  refine ⟨30253871204095620451435555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40338494938794160601914073 30253871204095620451435555)
                  ·
                    refine ⟨45380806806143430677153333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30253871204095620451435555 45380806806143430677153333)
                    ·
                      refine ⟨4254450638075946625983125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45380806806143430677153333 4254450638075946625983125)
                      ·
                        rfl

theorem cell23_8285513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_8285513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285513 prefixEnd_8285513 := by exact prefixLift 8285513
  have htrace : WordTrace (prefixWord ++ tailWord_8285513) baseStart_8285513 baseEnd_8285513 := by
    simpa [prefixWord, tailWord_8285513, baseEnd_8285513] using wordTrace_append hprefix tailTrace_8285513
  have hstable : (prefixWord ++ tailWord_8285513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285513).length < 2 ^ (prefixWord ++ tailWord_8285513).sum := by decide
  have hdescent : baseEnd_8285513 < baseStart_8285513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285523 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_8285523 : Nat := 118140960795 + 8285523 * 2 ^ 59
def prefixEnd_8285523 : Nat := 4983230072969 + 3 ^ 40 * 8285523 * 2
def baseEnd_8285523 : Nat := 4254455772882491586858079

theorem tailTrace_8285523 : CollatzResearch.WordTrace tailWord_8285523 prefixEnd_8285523 4254455772882491586858079 := by
  unfold tailWord_8285523
  simp only [CollatzResearch.WordTrace]
  refine ⟨302197850361972700515253223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201465233574648467010168815 302197850361972700515253223)
  ·
    refine ⟨453296775542959050772879835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302197850361972700515253223 453296775542959050772879835)
    ·
      refine ⟨679945163314438576159319753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453296775542959050772879835 679945163314438576159319753)
      ·
        refine ⟨509958872485828932119489815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 679945163314438576159319753 509958872485828932119489815)
        ·
          refine ⟨764938308728743398179234723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509958872485828932119489815 764938308728743398179234723)
          ·
            refine ⟨1147407463093115097268852085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764938308728743398179234723 1147407463093115097268852085)
            ·
              refine ⟨107569449664979540368954883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1147407463093115097268852085 107569449664979540368954883)
              ·
                refine ⟨161354174497469310553432325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107569449664979540368954883 161354174497469310553432325)
                ·
                  refine ⟨30253907718275495728768561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161354174497469310553432325 30253907718275495728768561)
                  ·
                    refine ⟨22690430788706621796576421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30253907718275495728768561 22690430788706621796576421)
                    ·
                      refine ⟨4254455772882491586858079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690430788706621796576421 4254455772882491586858079)
                      ·
                        rfl

theorem cell23_8285523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_8285523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285523 prefixEnd_8285523 := by exact prefixLift 8285523
  have htrace : WordTrace (prefixWord ++ tailWord_8285523) baseStart_8285523 baseEnd_8285523 := by
    simpa [prefixWord, tailWord_8285523, baseEnd_8285523] using wordTrace_append hprefix tailTrace_8285523
  have hstable : (prefixWord ++ tailWord_8285523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285523).length < 2 ^ (prefixWord ++ tailWord_8285523).sum := by decide
  have hdescent : baseEnd_8285523 < baseStart_8285523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285540 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_8285540 : Nat := 118140960795 + 8285540 * 2 ^ 59
def prefixEnd_8285540 : Nat := 4983230072969 + 3 ^ 40 * 8285540 * 2
def baseEnd_8285540 : Nat := 4254464502053618020345501

theorem tailTrace_8285540 : CollatzResearch.WordTrace tailWord_8285540 prefixEnd_8285540 4254464502053618020345501 := by
  unfold tailWord_8285540
  simp only [CollatzResearch.WordTrace]
  refine ⟨151099235201455556209311037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201465646935274074945748049 151099235201455556209311037)
  ·
    refine ⟨56662213200545833578491639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151099235201455556209311037 56662213200545833578491639)
    ·
      refine ⟨84993319800818750367737459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56662213200545833578491639 84993319800818750367737459)
      ·
        refine ⟨127489979701228125551606189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84993319800818750367737459 127489979701228125551606189)
        ·
          refine ⟨47808742387960547081852321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127489979701228125551606189 47808742387960547081852321)
          ·
            refine ⟨35856556790970410311389241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47808742387960547081852321 35856556790970410311389241)
            ·
              refine ⟨26892417593227807733541931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35856556790970410311389241 26892417593227807733541931)
              ·
                refine ⟨40338626389841711600312897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26892417593227807733541931 40338626389841711600312897)
                ·
                  refine ⟨30253969792381283700234673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40338626389841711600312897 30253969792381283700234673)
                  ·
                    refine ⟨22690477344285962775176005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30253969792381283700234673 22690477344285962775176005)
                    ·
                      refine ⟨4254464502053618020345501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690477344285962775176005 4254464502053618020345501)
                      ·
                        rfl

theorem cell23_8285540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_8285540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285540 prefixEnd_8285540 := by exact prefixLift 8285540
  have htrace : WordTrace (prefixWord ++ tailWord_8285540) baseStart_8285540 baseEnd_8285540 := by
    simpa [prefixWord, tailWord_8285540, baseEnd_8285540] using wordTrace_append hprefix tailTrace_8285540
  have hstable : (prefixWord ++ tailWord_8285540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285540).length < 2 ^ (prefixWord ++ tailWord_8285540).sum := by decide
  have hdescent : baseEnd_8285540 < baseStart_8285540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285563 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 7]
def baseStart_8285563 : Nat := 118140960795 + 8285563 * 2 ^ 59
def prefixEnd_8285563 : Nat := 4983230072969 + 3 ^ 40 * 8285563 * 2
def baseEnd_8285563 : Nat := 1418158770702890476785965

theorem tailTrace_8285563 : CollatzResearch.WordTrace tailWord_8285563 prefixEnd_8285563 1418158770702890476785965 := by
  unfold tailWord_8285563
  simp only [CollatzResearch.WordTrace]
  refine ⟨302199309281827787346709343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201466206187885191564472895 302199309281827787346709343)
  ·
    refine ⟨453298963922741681020064015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302199309281827787346709343 453298963922741681020064015)
    ·
      refine ⟨679948445884112521530096023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453298963922741681020064015 679948445884112521530096023)
      ·
        refine ⟨1019922668826168782295144035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679948445884112521530096023 1019922668826168782295144035)
        ·
          refine ⟨1529884003239253173442716053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019922668826168782295144035 1529884003239253173442716053)
          ·
            refine ⟨71713312651839992505127315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1529884003239253173442716053 71713312651839992505127315)
            ·
              refine ⟨107569968977759988757690973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71713312651839992505127315 107569968977759988757690973)
              ·
                refine ⟨40338738366659995784134115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107569968977759988757690973 40338738366659995784134115)
                ·
                  refine ⟨60508107549989993676201173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40338738366659995784134115 60508107549989993676201173)
                  ·
                    refine ⟨1418158770702890476785965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60508107549989993676201173 1418158770702890476785965)
                    ·
                      rfl

theorem cell23_8285563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_8285563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285563 prefixEnd_8285563 := by exact prefixLift 8285563
  have htrace : WordTrace (prefixWord ++ tailWord_8285563) baseStart_8285563 baseEnd_8285563 := by
    simpa [prefixWord, tailWord_8285563, baseEnd_8285563] using wordTrace_append hprefix tailTrace_8285563
  have hstable : (prefixWord ++ tailWord_8285563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285563).length < 2 ^ (prefixWord ++ tailWord_8285563).sum := by decide
  have hdescent : baseEnd_8285563 < baseStart_8285563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285580 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_8285580 : Nat := 118140960795 + 8285580 * 2 ^ 59
def prefixEnd_8285580 : Nat := 4983230072969 + 3 ^ 40 * 8285580 * 2
def baseEnd_8285580 : Nat := 1418161680426599287948439

theorem tailTrace_8285580 : CollatzResearch.WordTrace tailWord_8285580 prefixEnd_8285580 1418161680426599287948439 := by
  unfold tailWord_8285580
  simp only [CollatzResearch.WordTrace]
  refine ⟨151099964661383099625039097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201466619548510799500052129 151099964661383099625039097)
  ·
    refine ⟨113324973496037324718779323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151099964661383099625039097 113324973496037324718779323)
    ·
      refine ⟨169987460244055987078168985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113324973496037324718779323 169987460244055987078168985)
      ·
        refine ⟨127490595183041990308626739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169987460244055987078168985 127490595183041990308626739)
        ·
          refine ⟨191235892774562985462940109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127490595183041990308626739 191235892774562985462940109)
          ·
            refine ⟨71713459790461119548602541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191235892774562985462940109 71713459790461119548602541)
            ·
              refine ⟨26892547421422919830725953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71713459790461119548602541 26892547421422919830725953)
              ·
                refine ⟨20169410566067189873044465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26892547421422919830725953 20169410566067189873044465)
                ·
                  refine ⟨15127057924550392404783349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20169410566067189873044465 15127057924550392404783349)
                  ·
                    refine ⟨1418161680426599287948439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15127057924550392404783349 1418161680426599287948439)
                    ·
                      rfl

theorem cell23_8285580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_8285580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285580 prefixEnd_8285580 := by exact prefixLift 8285580
  have htrace : WordTrace (prefixWord ++ tailWord_8285580) baseStart_8285580 baseEnd_8285580 := by
    simpa [prefixWord, tailWord_8285580, baseEnd_8285580] using wordTrace_append hprefix tailTrace_8285580
  have hstable : (prefixWord ++ tailWord_8285580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285580).length < 2 ^ (prefixWord ++ tailWord_8285580).sum := by decide
  have hdescent : baseEnd_8285580 < baseStart_8285580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285583 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_8285583 : Nat := 118140960795 + 8285583 * 2 ^ 59
def prefixEnd_8285583 : Nat := 4983230072969 + 3 ^ 40 * 8285583 * 2
def baseEnd_8285583 : Nat := 4254486581721761352107803

theorem tailTrace_8285583 : CollatzResearch.WordTrace tailWord_8285583 prefixEnd_8285583 4254486581721761352107803 := by
  unfold tailWord_8285583
  simp only [CollatzResearch.WordTrace]
  refine ⟨302200038741755330762437403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201466692494503553841624935 302200038741755330762437403)
  ·
    refine ⟨453300058112632996143656105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302200038741755330762437403 453300058112632996143656105)
    ·
      refine ⟨339975043584474747107742079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453300058112632996143656105 339975043584474747107742079)
      ·
        refine ⟨509962565376712120661613119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339975043584474747107742079 509962565376712120661613119)
        ·
          refine ⟨764943848065068180992419679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509962565376712120661613119 764943848065068180992419679)
          ·
            refine ⟨1147415772097602271488629519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764943848065068180992419679 1147415772097602271488629519)
            ·
              refine ⟨1721123658146403407232944279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147415772097602271488629519 1721123658146403407232944279)
              ·
                refine ⟨2581685487219605110849416419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1721123658146403407232944279 2581685487219605110849416419)
                ·
                  refine ⟨3872528230829407666274124629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581685487219605110849416419 3872528230829407666274124629)
                  ·
                    refine ⟨22690595102516060544574949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3872528230829407666274124629 22690595102516060544574949)
                    ·
                      refine ⟨4254486581721761352107803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690595102516060544574949 4254486581721761352107803)
                      ·
                        rfl

theorem cell23_8285583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_8285583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285583 prefixEnd_8285583 := by exact prefixLift 8285583
  have htrace : WordTrace (prefixWord ++ tailWord_8285583) baseStart_8285583 baseEnd_8285583 := by
    simpa [prefixWord, tailWord_8285583, baseEnd_8285583] using wordTrace_append hprefix tailTrace_8285583
  have hstable : (prefixWord ++ tailWord_8285583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285583).length < 2 ^ (prefixWord ++ tailWord_8285583).sum := by decide
  have hdescent : baseEnd_8285583 < baseStart_8285583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285600 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_8285600 : Nat := 118140960795 + 8285600 * 2 ^ 59
def prefixEnd_8285600 : Nat := 4983230072969 + 3 ^ 40 * 8285600 * 2
def baseEnd_8285600 : Nat := 4254495310892887785595225

theorem tailTrace_8285600 : CollatzResearch.WordTrace tailWord_8285600 prefixEnd_8285600 4254495310892887785595225 := by
  unfold tailWord_8285600
  simp only [CollatzResearch.WordTrace]
  refine ⟨151100329391346871332903127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201467105855129161777204169 151100329391346871332903127)
  ·
    refine ⟨226650494087020306999354691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151100329391346871332903127 226650494087020306999354691)
    ·
      refine ⟨339975741130530460499032037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226650494087020306999354691 339975741130530460499032037)
      ·
        refine ⟨63745451461974461343568507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339975741130530460499032037 63745451461974461343568507)
        ·
          refine ⟨95618177192961692015352761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63745451461974461343568507 95618177192961692015352761)
          ·
            refine ⟨71713632894721269011514571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95618177192961692015352761 71713632894721269011514571)
            ·
              refine ⟨107570449342081903517271857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71713632894721269011514571 107570449342081903517271857)
              ·
                refine ⟨80677837006561427637953893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107570449342081903517271857 80677837006561427637953893)
                ·
                  refine ⟨15127094438730267682116355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80677837006561427637953893 15127094438730267682116355)
                  ·
                    refine ⟨22690641658095401523174533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15127094438730267682116355 22690641658095401523174533)
                    ·
                      refine ⟨4254495310892887785595225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690641658095401523174533 4254495310892887785595225)
                      ·
                        rfl

theorem cell23_8285600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_8285600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285600 prefixEnd_8285600 := by exact prefixLift 8285600
  have htrace : WordTrace (prefixWord ++ tailWord_8285600) baseStart_8285600 baseEnd_8285600 := by
    simpa [prefixWord, tailWord_8285600, baseEnd_8285600] using wordTrace_append hprefix tailTrace_8285600
  have hstable : (prefixWord ++ tailWord_8285600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285600).length < 2 ^ (prefixWord ++ tailWord_8285600).sum := by decide
  have hdescent : baseEnd_8285600 < baseStart_8285600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285617 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_8285617 : Nat := 118140960795 + 8285617 * 2 ^ 59
def prefixEnd_8285617 : Nat := 4983230072969 + 3 ^ 40 * 8285617 * 2
def baseEnd_8285617 : Nat := 4254504040064014219082647

theorem tailTrace_8285617 : CollatzResearch.WordTrace tailWord_8285617 prefixEnd_8285617 4254504040064014219082647 := by
  unfold tailWord_8285617
  simp only [CollatzResearch.WordTrace]
  refine ⟨302201278823632154569175105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201467519215754769712783403 302201278823632154569175105)
  ·
    refine ⟨226650959117724115926881329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302201278823632154569175105 226650959117724115926881329)
    ·
      refine ⟨169988219338293086945160997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226650959117724115926881329 169988219338293086945160997)
      ·
        refine ⟨31872791125929953802217687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169988219338293086945160997 31872791125929953802217687)
        ·
          refine ⟨47809186688894930703326531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31872791125929953802217687 47809186688894930703326531)
          ·
            refine ⟨71713780033342396054989797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47809186688894930703326531 71713780033342396054989797)
            ·
              refine ⟨13446333756251699260310587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71713780033342396054989797 13446333756251699260310587)
              ·
                refine ⟨20169500634377548890465881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13446333756251699260310587 20169500634377548890465881)
                ·
                  refine ⟨15127125475783161667849411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20169500634377548890465881 15127125475783161667849411)
                  ·
                    refine ⟨22690688213674742501774117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15127125475783161667849411 22690688213674742501774117)
                    ·
                      refine ⟨4254504040064014219082647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690688213674742501774117 4254504040064014219082647)
                      ·
                        rfl

theorem cell23_8285617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_8285617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285617 prefixEnd_8285617 := by exact prefixLift 8285617
  have htrace : WordTrace (prefixWord ++ tailWord_8285617) baseStart_8285617 baseEnd_8285617 := by
    simpa [prefixWord, tailWord_8285617, baseEnd_8285617] using wordTrace_append hprefix tailTrace_8285617
  have hstable : (prefixWord ++ tailWord_8285617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285617).length < 2 ^ (prefixWord ++ tailWord_8285617).sum := by decide
  have hdescent : baseEnd_8285617 < baseStart_8285617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285630 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_8285630 : Nat := 118140960795 + 8285630 * 2 ^ 59
def prefixEnd_8285630 : Nat := 4983230072969 + 3 ^ 40 * 8285630 * 2
def baseEnd_8285630 : Nat := 4254510715312522668220087

theorem tailTrace_8285630 : CollatzResearch.WordTrace tailWord_8285630 prefixEnd_8285630 4254510715312522668220087 := by
  unfold tailWord_8285630
  simp only [CollatzResearch.WordTrace]
  refine ⟨37775219121573132223674793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201467835315056705192932229 37775219121573132223674793)
  ·
    refine ⟨28331414341179849167756095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37775219121573132223674793 28331414341179849167756095)
    ·
      refine ⟨42497121511769773751634143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28331414341179849167756095 42497121511769773751634143)
      ·
        refine ⟨63745682267654660627451215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42497121511769773751634143 63745682267654660627451215)
        ·
          refine ⟨95618523401481990941176823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63745682267654660627451215 95618523401481990941176823)
          ·
            refine ⟨143427785102222986411765235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95618523401481990941176823 143427785102222986411765235)
            ·
              refine ⟨215141677653334479617647853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143427785102222986411765235 215141677653334479617647853)
              ·
                refine ⟨80678129120000429856617945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215141677653334479617647853 80678129120000429856617945)
                ·
                  refine ⟨60508596840000322392463459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80678129120000429856617945 60508596840000322392463459)
                  ·
                    refine ⟨90762895260000483588695189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60508596840000322392463459 90762895260000483588695189)
                    ·
                      refine ⟨4254510715312522668220087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90762895260000483588695189 4254510715312522668220087)
                      ·
                        rfl

theorem cell23_8285630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_8285630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285630 prefixEnd_8285630 := by exact prefixLift 8285630
  have htrace : WordTrace (prefixWord ++ tailWord_8285630) baseStart_8285630 baseEnd_8285630 := by
    simpa [prefixWord, tailWord_8285630, baseEnd_8285630] using wordTrace_append hprefix tailTrace_8285630
  have hstable : (prefixWord ++ tailWord_8285630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285630).length < 2 ^ (prefixWord ++ tailWord_8285630).sum := by decide
  have hdescent : baseEnd_8285630 < baseStart_8285630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285717 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_8285717 : Nat := 118140960795 + 8285717 * 2 ^ 59
def prefixEnd_8285717 : Nat := 4983230072969 + 3 ^ 40 * 8285717 * 2
def baseEnd_8285717 : Nat := 1418185129376487942610729

theorem tailTrace_8285717 : CollatzResearch.WordTrace tailWord_8285717 prefixEnd_8285717 1418185129376487942610729 := by
  unfold tailWord_8285717
  simp only [CollatzResearch.WordTrace]
  refine ⟨302204926123269871647815405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201469950748846581098543603 302204926123269871647815405)
  ·
    refine ⟨113326847296226201867930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302204926123269871647815405 113326847296226201867930777)
    ·
      refine ⟨84995135472169651400948083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113326847296226201867930777 84995135472169651400948083)
      ·
        refine ⟨127492703208254477101422125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84995135472169651400948083 127492703208254477101422125)
        ·
          refine ⟨47809763703095428913033297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127492703208254477101422125 47809763703095428913033297)
          ·
            refine ⟨35857322777321571684774973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47809763703095428913033297 35857322777321571684774973)
            ·
              refine ⟨13446496041495589381790615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35857322777321571684774973 13446496041495589381790615)
              ·
                refine ⟨20169744062243384072685923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13446496041495589381790615 20169744062243384072685923)
                ·
                  refine ⟨30254616093365076109028885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20169744062243384072685923 30254616093365076109028885)
                  ·
                    refine ⟨1418185129376487942610729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30254616093365076109028885 1418185129376487942610729)
                    ·
                      rfl

theorem cell23_8285717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_8285717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285717 prefixEnd_8285717 := by exact prefixLift 8285717
  have htrace : WordTrace (prefixWord ++ tailWord_8285717) baseStart_8285717 baseEnd_8285717 := by
    simpa [prefixWord, tailWord_8285717, baseEnd_8285717] using wordTrace_append hprefix tailTrace_8285717
  have hstable : (prefixWord ++ tailWord_8285717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285717).length < 2 ^ (prefixWord ++ tailWord_8285717).sum := by decide
  have hdescent : baseEnd_8285717 < baseStart_8285717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285724 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_8285724 : Nat := 118140960795 + 8285724 * 2 ^ 59
def prefixEnd_8285724 : Nat := 4983230072969 + 3 ^ 40 * 8285724 * 2
def baseEnd_8285724 : Nat := 4254558982494045300444655

theorem tailTrace_8285724 : CollatzResearch.WordTrace tailWord_8285724 prefixEnd_8285724 4254558982494045300444655 := by
  unfold tailWord_8285724
  simp only [CollatzResearch.WordTrace]
  refine ⟨151102590717122255921660113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201470120956163007895546817 151102590717122255921660113)
  ·
    refine ⟨113326943037841691941245085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151102590717122255921660113 113326943037841691941245085)
    ·
      refine ⟨42497603639190634477966907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113326943037841691941245085 42497603639190634477966907)
      ·
        refine ⟨63746405458785951716950361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42497603639190634477966907 63746405458785951716950361)
        ·
          refine ⟨47809804094089463787712771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63746405458785951716950361 47809804094089463787712771)
          ·
            refine ⟨71714706141134195681569157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47809804094089463787712771 71714706141134195681569157)
            ·
              refine ⟨13446507401462661690294217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71714706141134195681569157 13446507401462661690294217)
              ·
                refine ⟨10084880551096996267720663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13446507401462661690294217 10084880551096996267720663)
                ·
                  refine ⟨15127320826645494401580995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10084880551096996267720663 15127320826645494401580995)
                  ·
                    refine ⟨22690981239968241602371493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15127320826645494401580995 22690981239968241602371493)
                    ·
                      refine ⟨4254558982494045300444655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22690981239968241602371493 4254558982494045300444655)
                      ·
                        rfl

theorem cell23_8285724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_8285724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285724 prefixEnd_8285724 := by exact prefixLift 8285724
  have htrace : WordTrace (prefixWord ++ tailWord_8285724) baseStart_8285724 baseEnd_8285724 := by
    simpa [prefixWord, tailWord_8285724, baseEnd_8285724] using wordTrace_append hprefix tailTrace_8285724
  have hstable : (prefixWord ++ tailWord_8285724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285724).length < 2 ^ (prefixWord ++ tailWord_8285724).sum := by decide
  have hdescent : baseEnd_8285724 < baseStart_8285724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285727 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_8285727 : Nat := 118140960795 + 8285727 * 2 ^ 59
def prefixEnd_8285727 : Nat := 4983230072969 + 3 ^ 40 * 8285727 * 2
def baseEnd_8285727 : Nat := 4254560522936008788707141

theorem tailTrace_8285727 : CollatzResearch.WordTrace tailWord_8285727 prefixEnd_8285727 4254560522936008788707141 := by
  unfold tailWord_8285727
  simp only [CollatzResearch.WordTrace]
  refine ⟨302205290853233643355679435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201470193902155762237119623 302205290853233643355679435)
  ·
    refine ⟨453307936279850465033519153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302205290853233643355679435 453307936279850465033519153)
    ·
      refine ⟨339980952209887848775139365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453307936279850465033519153 339980952209887848775139365)
      ·
        refine ⟨63746428539353971645338631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 339980952209887848775139365 63746428539353971645338631)
        ·
          refine ⟨95619642809030957468007947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63746428539353971645338631 95619642809030957468007947)
          ·
            refine ⟨143429464213546436202011921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95619642809030957468007947 143429464213546436202011921)
            ·
              refine ⟨107572098160159827151508941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143429464213546436202011921 107572098160159827151508941)
              ·
                refine ⟨40339536810059935181815853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107572098160159827151508941 40339536810059935181815853)
                ·
                  refine ⟨15127326303772475693180945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40339536810059935181815853 15127326303772475693180945)
                  ·
                    refine ⟨11345494727829356769885709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15127326303772475693180945 11345494727829356769885709)
                    ·
                      refine ⟨4254560522936008788707141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11345494727829356769885709 4254560522936008788707141)
                      ·
                        rfl

theorem cell23_8285727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_8285727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285727 prefixEnd_8285727 := by exact prefixLift 8285727
  have htrace : WordTrace (prefixWord ++ tailWord_8285727) baseStart_8285727 baseEnd_8285727 := by
    simpa [prefixWord, tailWord_8285727, baseEnd_8285727] using wordTrace_append hprefix tailTrace_8285727
  have hstable : (prefixWord ++ tailWord_8285727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285727).length < 2 ^ (prefixWord ++ tailWord_8285727).sum := by decide
  have hdescent : baseEnd_8285727 < baseStart_8285727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285760 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_8285760 : Nat := 118140960795 + 8285760 * 2 ^ 59
def prefixEnd_8285760 : Nat := 4983230072969 + 3 ^ 40 * 8285760 * 2
def baseEnd_8285760 : Nat := 1418192489265869053198163

theorem tailTrace_8285760 : CollatzResearch.WordTrace tailWord_8285760 prefixEnd_8285760 1418192489265869053198163 := by
  unfold tailWord_8285760
  simp only [CollatzResearch.WordTrace]
  refine ⟨151103247231057044995815367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201470996308076059994420489 151103247231057044995815367)
  ·
    refine ⟨226654870846585567493723051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151103247231057044995815367 226654870846585567493723051)
    ·
      refine ⟨339982306269878351240584577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226654870846585567493723051 339982306269878351240584577)
      ·
        refine ⟨254986729702408763430438433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339982306269878351240584577 254986729702408763430438433)
        ·
          refine ⟨191240047276806572572828825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254986729702408763430438433 191240047276806572572828825)
          ·
            refine ⟨143430035457604929429621619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191240047276806572572828825 143430035457604929429621619)
            ·
              refine ⟨215145053186407394144432429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143430035457604929429621619 215145053186407394144432429)
              ·
                refine ⟨80679394944902772804162161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215145053186407394144432429 80679394944902772804162161)
                ·
                  refine ⟨60509546208677079603121621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80679394944902772804162161 60509546208677079603121621)
                  ·
                    refine ⟨1418192489265869053198163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60509546208677079603121621 1418192489265869053198163)
                    ·
                      rfl

theorem cell23_8285760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_8285760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285760 prefixEnd_8285760 := by exact prefixLift 8285760
  have htrace : WordTrace (prefixWord ++ tailWord_8285760) baseStart_8285760 baseEnd_8285760 := by
    simpa [prefixWord, tailWord_8285760, baseEnd_8285760] using wordTrace_append hprefix tailTrace_8285760
  have hstable : (prefixWord ++ tailWord_8285760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285760).length < 2 ^ (prefixWord ++ tailWord_8285760).sum := by decide
  have hdescent : baseEnd_8285760 < baseStart_8285760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285814 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_8285814 : Nat := 118140960795 + 8285814 * 2 ^ 59
def prefixEnd_8285814 : Nat := 4983230072969 + 3 ^ 40 * 8285814 * 2
def baseEnd_8285814 : Nat := 4254605195752949948319241

theorem tailTrace_8285814 : CollatzResearch.WordTrace tailWord_8285814 prefixEnd_8285814 4254605195752949948319241 := by
  unfold tailWord_8285814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888029000244903575881031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201472309335945638142730997 18888029000244903575881031)
  ·
    refine ⟨28332043500367355363821547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888029000244903575881031 28332043500367355363821547)
    ·
      refine ⟨42498065250551033045732321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28332043500367355363821547 42498065250551033045732321)
      ·
        refine ⟨31873548937913274784299241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42498065250551033045732321 31873548937913274784299241)
        ·
          refine ⟨23905161703434956088224431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31873548937913274784299241 23905161703434956088224431)
          ·
            refine ⟨35857742555152434132336647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23905161703434956088224431 35857742555152434132336647)
            ·
              refine ⟨53786613832728651198504971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35857742555152434132336647 53786613832728651198504971)
              ·
                refine ⟨80679920749092976797757457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53786613832728651198504971 80679920749092976797757457)
                ·
                  refine ⟨60509940561819732598318093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80679920749092976797757457 60509940561819732598318093)
                  ·
                    refine ⟨22691227710682399724369285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60509940561819732598318093 22691227710682399724369285)
                    ·
                      refine ⟨4254605195752949948319241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22691227710682399724369285 4254605195752949948319241)
                      ·
                        rfl

theorem cell23_8285814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_8285814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285814 prefixEnd_8285814 := by exact prefixLift 8285814
  have htrace : WordTrace (prefixWord ++ tailWord_8285814) baseStart_8285814 baseEnd_8285814 := by
    simpa [prefixWord, tailWord_8285814, baseEnd_8285814] using wordTrace_append hprefix tailTrace_8285814
  have hstable : (prefixWord ++ tailWord_8285814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285814).length < 2 ^ (prefixWord ++ tailWord_8285814).sum := by decide
  have hdescent : baseEnd_8285814 < baseStart_8285814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285817 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_8285817 : Nat := 118140960795 + 8285817 * 2 ^ 59
def prefixEnd_8285817 : Nat := 4983230072969 + 3 ^ 40 * 8285817 * 2
def baseEnd_8285817 : Nat := 4254606736194913436581727

theorem tailTrace_8285817 : CollatzResearch.WordTrace tailWord_8285817 prefixEnd_8285817 4254606736194913436581727 := by
  unfold tailWord_8285817
  simp only [CollatzResearch.WordTrace]
  refine ⟨302208573422907588726455705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201472382281938392484303803 302208573422907588726455705)
  ·
    refine ⟨226656430067180691544841779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302208573422907588726455705 226656430067180691544841779)
    ·
      refine ⟨339984645100771037317262669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226656430067180691544841779 339984645100771037317262669)
      ·
        refine ⟨127494241912789138993973501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339984645100771037317262669 127494241912789138993973501)
        ·
          refine ⟨47810340717295927122740063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127494241912789138993973501 47810340717295927122740063)
          ·
            refine ⟨71715511075943890684110095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47810340717295927122740063 71715511075943890684110095)
            ·
              refine ⟨107573266613915836026165143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71715511075943890684110095 107573266613915836026165143)
              ·
                refine ⟨161359899920873754039247715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107573266613915836026165143 161359899920873754039247715)
                ·
                  refine ⟨242039849881310631058871573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161359899920873754039247715 242039849881310631058871573)
                  ·
                    refine ⟨11345617963186435830884605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242039849881310631058871573 11345617963186435830884605)
                    ·
                      refine ⟨4254606736194913436581727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11345617963186435830884605 4254606736194913436581727)
                      ·
                        rfl

theorem cell23_8285817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_8285817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285817 prefixEnd_8285817 := by exact prefixLift 8285817
  have htrace : WordTrace (prefixWord ++ tailWord_8285817) baseStart_8285817 baseEnd_8285817 := by
    simpa [prefixWord, tailWord_8285817, baseEnd_8285817] using wordTrace_append hprefix tailTrace_8285817
  have hstable : (prefixWord ++ tailWord_8285817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285817).length < 2 ^ (prefixWord ++ tailWord_8285817).sum := by decide
  have hdescent : baseEnd_8285817 < baseStart_8285817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285831 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_8285831 : Nat := 118140960795 + 8285831 * 2 ^ 59
def prefixEnd_8285831 : Nat := 4983230072969 + 3 ^ 40 * 8285831 * 2
def baseEnd_8285831 : Nat := 4254613924924076381806663

theorem tailTrace_8285831 : CollatzResearch.WordTrace tailWord_8285831 prefixEnd_8285831 4254613924924076381806663 := by
  unfold tailWord_8285831
  simp only [CollatzResearch.WordTrace]
  refine ⟨302209084044856869117465347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201472722696571246078310231 302209084044856869117465347)
  ·
    refine ⟨453313626067285303676198021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302209084044856869117465347 453313626067285303676198021)
    ·
      refine ⟨84996304887615994439287129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453313626067285303676198021 84996304887615994439287129)
      ·
        refine ⟨63747228665711995829465347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84996304887615994439287129 63747228665711995829465347)
        ·
          refine ⟨95620842998567993744198021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63747228665711995829465347 95620842998567993744198021)
          ·
            refine ⟨17928908062231498827037129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95620842998567993744198021 17928908062231498827037129)
            ·
              refine ⟨13446681046673624120277847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17928908062231498827037129 13446681046673624120277847)
              ·
                refine ⟨20170021570010436180416771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13446681046673624120277847 20170021570010436180416771)
                ·
                  refine ⟨30255032355015654270625157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20170021570010436180416771 30255032355015654270625157)
                  ·
                    refine ⟨5672818566565435175742217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30255032355015654270625157 5672818566565435175742217)
                    ·
                      refine ⟨4254613924924076381806663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672818566565435175742217 4254613924924076381806663)
                      ·
                        rfl

theorem cell23_8285831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_8285831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285831 prefixEnd_8285831 := by exact prefixLift 8285831
  have htrace : WordTrace (prefixWord ++ tailWord_8285831) baseStart_8285831 baseEnd_8285831 := by
    simpa [prefixWord, tailWord_8285831, baseEnd_8285831] using wordTrace_append hprefix tailTrace_8285831
  have hstable : (prefixWord ++ tailWord_8285831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285831).length < 2 ^ (prefixWord ++ tailWord_8285831).sum := by decide
  have hdescent : baseEnd_8285831 < baseStart_8285831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285852 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_8285852 : Nat := 118140960795 + 8285852 * 2 ^ 59
def prefixEnd_8285852 : Nat := 4983230072969 + 3 ^ 40 * 8285852 * 2
def baseEnd_8285852 : Nat := 4254624708017820799644067

theorem tailTrace_8285852 : CollatzResearch.WordTrace tailWord_8285852 prefixEnd_8285852 4254624708017820799644067 := by
  unfold tailWord_8285852
  simp only [CollatzResearch.WordTrace]
  refine ⟨151104924988890394851989905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201473233318520526469319873 151104924988890394851989905)
  ·
    refine ⟨113328693741667796138992429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151104924988890394851989905 113328693741667796138992429)
    ·
      refine ⟨42498260153125423552122161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113328693741667796138992429 42498260153125423552122161)
      ·
        refine ⟨31873695114844067664091621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42498260153125423552122161 31873695114844067664091621)
        ·
          refine ⟨5976317834033262687017179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31873695114844067664091621 5976317834033262687017179)
          ·
            refine ⟨8964476751049894030525769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976317834033262687017179 8964476751049894030525769)
            ·
              refine ⟨6723357563287420522894327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8964476751049894030525769 6723357563287420522894327)
              ·
                refine ⟨10085036344931130784341491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723357563287420522894327 10085036344931130784341491)
                ·
                  refine ⟨15127554517396696176512237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10085036344931130784341491 15127554517396696176512237)
                  ·
                    refine ⟨5672832944023761066192089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15127554517396696176512237 5672832944023761066192089)
                    ·
                      refine ⟨4254624708017820799644067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672832944023761066192089 4254624708017820799644067)
                      ·
                        rfl

theorem cell23_8285852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_8285852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285852 prefixEnd_8285852 := by exact prefixLift 8285852
  have htrace : WordTrace (prefixWord ++ tailWord_8285852) baseStart_8285852 baseEnd_8285852 := by
    simpa [prefixWord, tailWord_8285852, baseEnd_8285852] using wordTrace_append hprefix tailTrace_8285852
  have hstable : (prefixWord ++ tailWord_8285852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285852).length < 2 ^ (prefixWord ++ tailWord_8285852).sum := by decide
  have hdescent : baseEnd_8285852 < baseStart_8285852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285874 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_8285874 : Nat := 118140960795 + 8285874 * 2 ^ 59
def prefixEnd_8285874 : Nat := 4983230072969 + 3 ^ 40 * 8285874 * 2
def baseEnd_8285874 : Nat := 4254636004592219713568965

theorem tailTrace_8285874 : CollatzResearch.WordTrace tailWord_8285874 prefixEnd_8285874 4254636004592219713568965 := by
  unfold tailWord_8285874
  simp only [CollatzResearch.WordTrace]
  refine ⟨75552663095925271865320169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201473768255800724974187117 75552663095925271865320169)
  ·
    refine ⟨56664497321943953898990127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75552663095925271865320169 56664497321943953898990127)
    ·
      refine ⟨84996745982915930848485191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56664497321943953898990127 84996745982915930848485191)
      ·
        refine ⟨127495118974373896272727787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84996745982915930848485191 127495118974373896272727787)
        ·
          refine ⟨191242678461560844409091681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127495118974373896272727787 191242678461560844409091681)
          ·
            refine ⟨143432008846170633306818761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191242678461560844409091681 143432008846170633306818761)
            ·
              refine ⟨107574006634627974980114071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143432008846170633306818761 107574006634627974980114071)
              ·
                refine ⟨161361009951941962470171107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107574006634627974980114071 161361009951941962470171107)
                ·
                  refine ⟨242041514927912943705256661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161361009951941962470171107 242041514927912943705256661)
                  ·
                    refine ⟨5672848006122959618091953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 242041514927912943705256661 5672848006122959618091953)
                    ·
                      refine ⟨4254636004592219713568965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672848006122959618091953 4254636004592219713568965)
                      ·
                        rfl

theorem cell23_8285874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_8285874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285874 prefixEnd_8285874 := by exact prefixLift 8285874
  have htrace : WordTrace (prefixWord ++ tailWord_8285874) baseStart_8285874 baseEnd_8285874 := by
    simpa [prefixWord, tailWord_8285874, baseEnd_8285874] using wordTrace_append hprefix tailTrace_8285874
  have hstable : (prefixWord ++ tailWord_8285874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285874).length < 2 ^ (prefixWord ++ tailWord_8285874).sum := by decide
  have hdescent : baseEnd_8285874 < baseStart_8285874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285887 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_8285887 : Nat := 118140960795 + 8285887 * 2 ^ 59
def prefixEnd_8285887 : Nat := 4983230072969 + 3 ^ 40 * 8285887 * 2
def baseEnd_8285887 : Nat := 4254642679840728162706405

theorem tailTrace_8285887 : CollatzResearch.WordTrace tailWord_8285887 prefixEnd_8285887 4254642679840728162706405 := by
  unfold tailWord_8285887
  simp only [CollatzResearch.WordTrace]
  refine ⟨302211126532653990681503915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201474084355102660454335943 302211126532653990681503915)
  ·
    refine ⟨453316689798980986022255873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302211126532653990681503915 453316689798980986022255873)
    ·
      refine ⟨339987517349235739516691905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453316689798980986022255873 339987517349235739516691905)
      ·
        refine ⟨254990638011926804637518929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339987517349235739516691905 254990638011926804637518929)
        ·
          refine ⟨191242978508945103478139197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254990638011926804637518929 191242978508945103478139197)
          ·
            refine ⟨71716116940854413804302199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191242978508945103478139197 71716116940854413804302199)
            ·
              refine ⟨107574175411281620706453299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71716116940854413804302199 107574175411281620706453299)
              ·
                refine ⟨161361263116922431059679949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107574175411281620706453299 161361263116922431059679949)
                ·
                  refine ⟨60510473668845911647379981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161361263116922431059679949 60510473668845911647379981)
                  ·
                    refine ⟨22691427625817216867767493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60510473668845911647379981 22691427625817216867767493)
                    ·
                      refine ⟨4254642679840728162706405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22691427625817216867767493 4254642679840728162706405)
                      ·
                        rfl

theorem cell23_8285887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_8285887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285887 prefixEnd_8285887 := by exact prefixLift 8285887
  have htrace : WordTrace (prefixWord ++ tailWord_8285887) baseStart_8285887 baseEnd_8285887 := by
    simpa [prefixWord, tailWord_8285887, baseEnd_8285887] using wordTrace_append hprefix tailTrace_8285887
  have hstable : (prefixWord ++ tailWord_8285887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285887).length < 2 ^ (prefixWord ++ tailWord_8285887).sum := by decide
  have hdescent : baseEnd_8285887 < baseStart_8285887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285901 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_8285901 : Nat := 118140960795 + 8285901 * 2 ^ 59
def prefixEnd_8285901 : Nat := 4983230072969 + 3 ^ 40 * 8285901 * 2
def baseEnd_8285901 : Nat := 1418216622856630369310447

theorem tailTrace_8285901 : CollatzResearch.WordTrace tailWord_8285901 prefixEnd_8285901 1418216622856630369310447 := by
  unfold tailWord_8285901
  simp only [CollatzResearch.WordTrace]
  refine ⟨302211637154603271072513557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201474424769735514048342371 302211637154603271072513557)
  ·
    refine ⟨14166170491622028331524073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302211637154603271072513557 14166170491622028331524073)
    ·
      refine ⟨10624627868716521248643055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14166170491622028331524073 10624627868716521248643055)
      ·
        refine ⟨15936941803074781872964583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624627868716521248643055 15936941803074781872964583)
        ·
          refine ⟨23905412704612172809446875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15936941803074781872964583 23905412704612172809446875)
          ·
            refine ⟨35858119056918259214170313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23905412704612172809446875 35858119056918259214170313)
            ·
              refine ⟨26893589292688694410627735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35858119056918259214170313 26893589292688694410627735)
              ·
                refine ⟨40340383939033041615941603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26893589292688694410627735 40340383939033041615941603)
                ·
                  refine ⟨60510575908549562423912405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40340383939033041615941603 60510575908549562423912405)
                  ·
                    refine ⟨1418216622856630369310447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60510575908549562423912405 1418216622856630369310447)
                    ·
                      rfl

theorem cell23_8285901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_8285901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285901 prefixEnd_8285901 := by exact prefixLift 8285901
  have htrace : WordTrace (prefixWord ++ tailWord_8285901) baseStart_8285901 baseEnd_8285901 := by
    simpa [prefixWord, tailWord_8285901, baseEnd_8285901] using wordTrace_append hprefix tailTrace_8285901
  have hstable : (prefixWord ++ tailWord_8285901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285901).length < 2 ^ (prefixWord ++ tailWord_8285901).sum := by decide
  have hdescent : baseEnd_8285901 < baseStart_8285901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285904 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2]
def baseStart_8285904 : Nat := 118140960795 + 8285904 * 2 ^ 59
def prefixEnd_8285904 : Nat := 4983230072969 + 3 ^ 40 * 8285904 * 2
def baseEnd_8285904 : Nat := 4254651409011854596193827

theorem tailTrace_8285904 : CollatzResearch.WordTrace tailWord_8285904 prefixEnd_8285904 4254651409011854596193827 := by
  unfold tailWord_8285904
  simp only [CollatzResearch.WordTrace]
  refine ⟨151105873286796201292436383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201474497715728268389915177 151105873286796201292436383)
  ·
    refine ⟨226658809930194301938654575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151105873286796201292436383 226658809930194301938654575)
    ·
      refine ⟨339988214895291452907981863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226658809930194301938654575 339988214895291452907981863)
      ·
        refine ⟨509982322342937179361972795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339988214895291452907981863 509982322342937179361972795)
        ·
          refine ⟨764973483514405769042959193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509982322342937179361972795 764973483514405769042959193)
          ·
            refine ⟨573730112635804326782219395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 764973483514405769042959193 573730112635804326782219395)
            ·
              refine ⟨860595168953706490173329093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573730112635804326782219395 860595168953706490173329093)
              ·
                refine ⟨161361594178819966907499205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 860595168953706490173329093 161361594178819966907499205)
                ·
                  refine ⟨30255298908528743795156101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161361594178819966907499205 30255298908528743795156101)
                  ·
                    refine ⟨5672868545349139461591769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30255298908528743795156101 5672868545349139461591769)
                    ·
                      refine ⟨4254651409011854596193827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672868545349139461591769 4254651409011854596193827)
                      ·
                        rfl

theorem cell23_8285904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 4, 2].length) (baseStart_8285904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285904 prefixEnd_8285904 := by exact prefixLift 8285904
  have htrace : WordTrace (prefixWord ++ tailWord_8285904) baseStart_8285904 baseEnd_8285904 := by
    simpa [prefixWord, tailWord_8285904, baseEnd_8285904] using wordTrace_append hprefix tailTrace_8285904
  have hstable : (prefixWord ++ tailWord_8285904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285904).length < 2 ^ (prefixWord ++ tailWord_8285904).sum := by decide
  have hdescent : baseEnd_8285904 < baseStart_8285904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285921 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_8285921 : Nat := 118140960795 + 8285921 * 2 ^ 59
def prefixEnd_8285921 : Nat := 4983230072969 + 3 ^ 40 * 8285921 * 2
def baseEnd_8285921 : Nat := 4254660138182981029681249

theorem tailTrace_8285921 : CollatzResearch.WordTrace tailWord_8285921 prefixEnd_8285921 4254660138182981029681249 := by
  unfold tailWord_8285921
  simp only [CollatzResearch.WordTrace]
  refine ⟨302212366614530814488241617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201474911076353876325494411 302212366614530814488241617)
  ·
    refine ⟨226659274960898110866181213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302212366614530814488241617 226659274960898110866181213)
    ·
      refine ⟨84997228110336791574817955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226659274960898110866181213 84997228110336791574817955)
      ·
        refine ⟨127495842165505187362226933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84997228110336791574817955 127495842165505187362226933)
        ·
          refine ⟨11952735203016111315208775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127495842165505187362226933 11952735203016111315208775)
          ·
            refine ⟨17929102804524166972813163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952735203016111315208775 17929102804524166972813163)
            ·
              refine ⟨26893654206786250459219745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17929102804524166972813163 26893654206786250459219745)
              ·
                refine ⟨20170240655089687844414809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26893654206786250459219745 20170240655089687844414809)
                ·
                  refine ⟨15127680491317265883311107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20170240655089687844414809 15127680491317265883311107)
                  ·
                    refine ⟨22691520736975898824966661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15127680491317265883311107 22691520736975898824966661)
                    ·
                      refine ⟨4254660138182981029681249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22691520736975898824966661 4254660138182981029681249)
                      ·
                        rfl

theorem cell23_8285921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_8285921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285921 prefixEnd_8285921 := by exact prefixLift 8285921
  have htrace : WordTrace (prefixWord ++ tailWord_8285921) baseStart_8285921 baseEnd_8285921 := by
    simpa [prefixWord, tailWord_8285921, baseEnd_8285921] using wordTrace_append hprefix tailTrace_8285921
  have hstable : (prefixWord ++ tailWord_8285921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285921).length < 2 ^ (prefixWord ++ tailWord_8285921).sum := by decide
  have hdescent : baseEnd_8285921 < baseStart_8285921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285931 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 1, 4]
def baseStart_8285931 : Nat := 118140960795 + 8285931 * 2 ^ 59
def prefixEnd_8285931 : Nat := 4983230072969 + 3 ^ 40 * 8285931 * 2
def baseEnd_8285931 : Nat := 1418221757663175330185401

theorem tailTrace_8285931 : CollatzResearch.WordTrace tailWord_8285931 prefixEnd_8285931 1418221757663175330185401 := by
  unfold tailWord_8285931
  simp only [CollatzResearch.WordTrace]
  refine ⟨302212731344494586196105647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201475154229663057464070431 302212731344494586196105647)
  ·
    refine ⟨453319097016741879294158471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302212731344494586196105647 453319097016741879294158471)
    ·
      refine ⟨679978645525112818941237707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453319097016741879294158471 679978645525112818941237707)
      ·
        refine ⟨1019967968287669228411856561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679978645525112818941237707 1019967968287669228411856561)
        ·
          refine ⟨764975976215751921308892421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1019967968287669228411856561 764975976215751921308892421)
          ·
            refine ⟨143432995540453485245417329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 764975976215751921308892421 143432995540453485245417329)
            ·
              refine ⟨107574746655340113934062997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143432995540453485245417329 107574746655340113934062997)
              ·
                refine ⟨5042566249469067840659203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107574746655340113934062997 5042566249469067840659203)
                ·
                  refine ⟨7563849374203601760988805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042566249469067840659203 7563849374203601760988805)
                  ·
                    refine ⟨1418221757663175330185401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7563849374203601760988805 1418221757663175330185401)
                    ·
                      rfl

theorem cell23_8285931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 4].length) (baseStart_8285931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285931 prefixEnd_8285931 := by exact prefixLift 8285931
  have htrace : WordTrace (prefixWord ++ tailWord_8285931) baseStart_8285931 baseEnd_8285931 := by
    simpa [prefixWord, tailWord_8285931, baseEnd_8285931] using wordTrace_append hprefix tailTrace_8285931
  have hstable : (prefixWord ++ tailWord_8285931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285931).length < 2 ^ (prefixWord ++ tailWord_8285931).sum := by decide
  have hdescent : baseEnd_8285931 < baseStart_8285931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8285967 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_8285967 : Nat := 118140960795 + 8285967 * 2 ^ 59
def prefixEnd_8285967 : Nat := 4983230072969 + 3 ^ 40 * 8285967 * 2
def baseEnd_8285967 : Nat := 4254683758293087849706037

theorem tailTrace_8285967 : CollatzResearch.WordTrace tailWord_8285967 prefixEnd_8285967 4254683758293087849706037 := by
  unfold tailWord_8285967
  simp only [CollatzResearch.WordTrace]
  refine ⟨302214044372364164344416155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201476029581576109562944103 302214044372364164344416155)
  ·
    refine ⟨453321066558546246516624233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302214044372364164344416155 453321066558546246516624233)
    ·
      refine ⟨339990799918909684887468175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453321066558546246516624233 339990799918909684887468175)
      ·
        refine ⟨509986199878364527331202263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339990799918909684887468175 509986199878364527331202263)
        ·
          refine ⟨764979299817546790996803395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 509986199878364527331202263 764979299817546790996803395)
          ·
            refine ⟨1147468949726320186495205093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764979299817546790996803395 1147468949726320186495205093)
            ·
              refine ⟨215150428073685034967850955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1147468949726320186495205093 215150428073685034967850955)
              ·
                refine ⟨322725642110527552451776433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215150428073685034967850955 322725642110527552451776433)
                ·
                  refine ⟨242044231582895664338832325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322725642110527552451776433 242044231582895664338832325)
                  ·
                    refine ⟨45383293421792937063531061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242044231582895664338832325 45383293421792937063531061)
                    ·
                      refine ⟨4254683758293087849706037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45383293421792937063531061 4254683758293087849706037)
                      ·
                        rfl

theorem cell23_8285967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_8285967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8285967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8285967 prefixEnd_8285967 := by exact prefixLift 8285967
  have htrace : WordTrace (prefixWord ++ tailWord_8285967) baseStart_8285967 baseEnd_8285967 := by
    simpa [prefixWord, tailWord_8285967, baseEnd_8285967] using wordTrace_append hprefix tailTrace_8285967
  have hstable : (prefixWord ++ tailWord_8285967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8285967).length < 2 ^ (prefixWord ++ tailWord_8285967).sum := by decide
  have hdescent : baseEnd_8285967 < baseStart_8285967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8285967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286015 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 2, 3, 2]
def baseStart_8286015 : Nat := 118140960795 + 8286015 * 2 ^ 59
def prefixEnd_8286015 : Nat := 4983230072969 + 3 ^ 40 * 8286015 * 2
def baseEnd_8286015 : Nat := 4254708405364503661905817

theorem tailTrace_8286015 : CollatzResearch.WordTrace tailWord_8286015 prefixEnd_8286015 4254708405364503661905817 := by
  unfold tailWord_8286015
  simp only [CollatzResearch.WordTrace]
  refine ⟨302215795076190268542163499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201477196717460179028108999 302215795076190268542163499)
  ·
    refine ⟨453323692614285402813245249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302215795076190268542163499 453323692614285402813245249)
    ·
      refine ⟨339992769460714052109933937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453323692614285402813245249 339992769460714052109933937)
      ·
        refine ⟨254994577095535539082450453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339992769460714052109933937 254994577095535539082450453)
        ·
          refine ⟨11952870801353228394489865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 254994577095535539082450453 11952870801353228394489865)
          ·
            refine ⟨8964653101014921295867399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11952870801353228394489865 8964653101014921295867399)
            ·
              refine ⟨13446979651522381943801099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964653101014921295867399 13446979651522381943801099)
              ·
                refine ⟨20170469477283572915701649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13446979651522381943801099 20170469477283572915701649)
                ·
                  refine ⟨15127852107962679686776237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20170469477283572915701649 15127852107962679686776237)
                  ·
                    refine ⟨5672944540486004882541089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15127852107962679686776237 5672944540486004882541089)
                    ·
                      refine ⟨4254708405364503661905817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5672944540486004882541089 4254708405364503661905817)
                      ·
                        rfl

theorem cell23_8286015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_8286015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286015 prefixEnd_8286015 := by exact prefixLift 8286015
  have htrace : WordTrace (prefixWord ++ tailWord_8286015) baseStart_8286015 baseEnd_8286015 := by
    simpa [prefixWord, tailWord_8286015, baseEnd_8286015] using wordTrace_append hprefix tailTrace_8286015
  have hstable : (prefixWord ++ tailWord_8286015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286015).length < 2 ^ (prefixWord ++ tailWord_8286015).sum := by decide
  have hdescent : baseEnd_8286015 < baseStart_8286015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286028 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_8286028 : Nat := 118140960795 + 8286028 * 2 ^ 59
def prefixEnd_8286028 : Nat := 4983230072969 + 3 ^ 40 * 8286028 * 2
def baseEnd_8286028 : Nat := 4254715080613012111043257

theorem tailTrace_8286028 : CollatzResearch.WordTrace tailWord_8286028 prefixEnd_8286028 4254715080613012111043257 := by
  unfold tailWord_8286028
  simp only [CollatzResearch.WordTrace]
  refine ⟨151108134612571585881193369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201477512816762114508257825 151108134612571585881193369)
  ·
    refine ⟨113331100959428689410895027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151108134612571585881193369 113331100959428689410895027)
    ·
      refine ⟨169996651439143034116342541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113331100959428689410895027 169996651439143034116342541)
      ·
        refine ⟨63748744289678637793628453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169996651439143034116342541 63748744289678637793628453)
        ·
          refine ⟨11952889554314744586305335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63748744289678637793628453 11952889554314744586305335)
          ·
            refine ⟨17929334331472116879458003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952889554314744586305335 17929334331472116879458003)
            ·
              refine ⟨26894001497208175319187005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17929334331472116879458003 26894001497208175319187005)
              ·
                refine ⟨10085250561453065744695127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26894001497208175319187005 10085250561453065744695127)
                ·
                  refine ⟨15127875842179598617042691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10085250561453065744695127 15127875842179598617042691)
                  ·
                    refine ⟨22691813763269397925564037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15127875842179598617042691 22691813763269397925564037)
                    ·
                      refine ⟨4254715080613012111043257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22691813763269397925564037 4254715080613012111043257)
                      ·
                        rfl

theorem cell23_8286028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_8286028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286028 prefixEnd_8286028 := by exact prefixLift 8286028
  have htrace : WordTrace (prefixWord ++ tailWord_8286028) baseStart_8286028 baseEnd_8286028 := by
    simpa [prefixWord, tailWord_8286028, baseEnd_8286028] using wordTrace_append hprefix tailTrace_8286028
  have hstable : (prefixWord ++ tailWord_8286028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286028).length < 2 ^ (prefixWord ++ tailWord_8286028).sum := by decide
  have hdescent : baseEnd_8286028 < baseStart_8286028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286034 : List Nat := [3, 2, 2, 1, 1, 4, 10]
def baseStart_8286034 : Nat := 118140960795 + 8286034 * 2 ^ 59
def prefixEnd_8286034 : Nat := 4983230072969 + 3 ^ 40 * 8286034 * 2
def baseEnd_8286034 : Nat := 52527384709838754167509

theorem tailTrace_8286034 : CollatzResearch.WordTrace tailWord_8286034 prefixEnd_8286034 52527384709838754167509 := by
  unfold tailWord_8286034
  simp only [CollatzResearch.WordTrace]
  refine ⟨75554122015780358696776289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201477658708747623191403437 75554122015780358696776289)
  ·
    refine ⟨56665591511835269022582217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75554122015780358696776289 56665591511835269022582217)
    ·
      refine ⟨42499193633876451766936663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56665591511835269022582217 42499193633876451766936663)
      ·
        refine ⟨63748790450814677650404995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42499193633876451766936663 63748790450814677650404995)
        ·
          refine ⟨95623185676222016475607493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63748790450814677650404995 95623185676222016475607493)
          ·
            refine ⟨17929347314291628089176405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95623185676222016475607493 17929347314291628089176405)
            ·
              refine ⟨52527384709838754167509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17929347314291628089176405 52527384709838754167509)
              ·
                rfl

theorem cell23_8286034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 10].length) (baseStart_8286034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286034 prefixEnd_8286034 := by exact prefixLift 8286034
  have htrace : WordTrace (prefixWord ++ tailWord_8286034) baseStart_8286034 baseEnd_8286034 := by
    simpa [prefixWord, tailWord_8286034, baseEnd_8286034] using wordTrace_append hprefix tailTrace_8286034
  have hstable : (prefixWord ++ tailWord_8286034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286034).length < 2 ^ (prefixWord ++ tailWord_8286034).sum := by decide
  have hdescent : baseEnd_8286034 < baseStart_8286034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286058 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_8286058 : Nat := 118140960795 + 8286058 * 2 ^ 59
def prefixEnd_8286058 : Nat := 4983230072969 + 3 ^ 40 * 8286058 * 2
def baseEnd_8286058 : Nat := 4254730485032646993668119

theorem tailTrace_8286058 : CollatzResearch.WordTrace tailWord_8286058 prefixEnd_8286058 4254730485032646993668119 := by
  unfold tailWord_8286058
  simp only [CollatzResearch.WordTrace]
  refine ⟨75554340853758621721494707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201478242276689657923985885 75554340853758621721494707)
  ·
    refine ⟨113331511280637932582242061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75554340853758621721494707 113331511280637932582242061)
    ·
      refine ⟨42499316730239224718340773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113331511280637932582242061 42499316730239224718340773)
      ·
        refine ⟨7968621886919854634688895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42499316730239224718340773 7968621886919854634688895)
        ·
          refine ⟨11952932830379781952033343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968621886919854634688895 11952932830379781952033343)
          ·
            refine ⟨17929399245569672928050015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11952932830379781952033343 17929399245569672928050015)
            ·
              refine ⟨26894098868354509392075023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17929399245569672928050015 26894098868354509392075023)
              ·
                refine ⟨40341148302531764088112535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26894098868354509392075023 40341148302531764088112535)
                ·
                  refine ⟨60511722453797646132168803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40341148302531764088112535 60511722453797646132168803)
                  ·
                    refine ⟨90767583680696469198253205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60511722453797646132168803 90767583680696469198253205)
                    ·
                      refine ⟨4254730485032646993668119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90767583680696469198253205 4254730485032646993668119)
                      ·
                        rfl

theorem cell23_8286058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_8286058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286058 prefixEnd_8286058 := by exact prefixLift 8286058
  have htrace : WordTrace (prefixWord ++ tailWord_8286058) baseStart_8286058 baseEnd_8286058 := by
    simpa [prefixWord, tailWord_8286058, baseEnd_8286058] using wordTrace_append hprefix tailTrace_8286058
  have hstable : (prefixWord ++ tailWord_8286058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286058).length < 2 ^ (prefixWord ++ tailWord_8286058).sum := by decide
  have hdescent : baseEnd_8286058 < baseStart_8286058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286074 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_8286074 : Nat := 118140960795 + 8286074 * 2 ^ 59
def prefixEnd_8286074 : Nat := 4983230072969 + 3 ^ 40 * 8286074 * 2
def baseEnd_8286074 : Nat := 4254738700723118931068045

theorem tailTrace_8286074 : CollatzResearch.WordTrace tailWord_8286074 prefixEnd_8286074 4254738700723118931068045 := by
  unfold tailWord_8286074
  simp only [CollatzResearch.WordTrace]
  refine ⟨75554486745744130404640319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201478631321984347745707517 75554486745744130404640319)
  ·
    refine ⟨113331730118616195606960479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75554486745744130404640319 113331730118616195606960479)
    ·
      refine ⟨169997595177924293410440719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113331730118616195606960479 169997595177924293410440719)
      ·
        refine ⟨254996392766886440115661079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169997595177924293410440719 254996392766886440115661079)
        ·
          refine ⟨382494589150329660173491619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254996392766886440115661079 382494589150329660173491619)
          ·
            refine ⟨573741883725494490260237429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382494589150329660173491619 573741883725494490260237429)
            ·
              refine ⟨53788301599265108461897259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 573741883725494490260237429 53788301599265108461897259)
              ·
                refine ⟨80682452398897662692845889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53788301599265108461897259 80682452398897662692845889)
                ·
                  refine ⟨60511839299173247019634417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80682452398897662692845889 60511839299173247019634417)
                  ·
                    refine ⟨45383879474379935264725813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60511839299173247019634417 45383879474379935264725813)
                    ·
                      refine ⟨4254738700723118931068045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45383879474379935264725813 4254738700723118931068045)
                      ·
                        rfl

theorem cell23_8286074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_8286074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286074 prefixEnd_8286074 := by exact prefixLift 8286074
  have htrace : WordTrace (prefixWord ++ tailWord_8286074) baseStart_8286074 baseEnd_8286074 := by
    simpa [prefixWord, tailWord_8286074, baseEnd_8286074] using wordTrace_append hprefix tailTrace_8286074
  have hstable : (prefixWord ++ tailWord_8286074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286074).length < 2 ^ (prefixWord ++ tailWord_8286074).sum := by decide
  have hdescent : baseEnd_8286074 < baseStart_8286074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286151 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_8286151 : Nat := 118140960795 + 8286151 * 2 ^ 59
def prefixEnd_8286151 : Nat := 4983230072969 + 3 ^ 40 * 8286151 * 2
def baseEnd_8286151 : Nat := 4254778238733515129805191

theorem tailTrace_8286151 : CollatzResearch.WordTrace tailWord_8286151 prefixEnd_8286151 4254778238733515129805191 := by
  unfold tailWord_8286151
  simp only [CollatzResearch.WordTrace]
  refine ⟨302220755403697563769114307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201480503602465042512742871 302220755403697563769114307)
  ·
    refine ⟨453331133105546345653671461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302220755403697563769114307 453331133105546345653671461)
    ·
      refine ⟨84999587457289939810063399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453331133105546345653671461 84999587457289939810063399)
      ·
        refine ⟨127499381185934909715095099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84999587457289939810063399 127499381185934909715095099)
        ·
          refine ⟨191249071778902364572642649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127499381185934909715095099 191249071778902364572642649)
          ·
            refine ⟨143436803834176773429481987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191249071778902364572642649 143436803834176773429481987)
            ·
              refine ⟨215155205751265160144222981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143436803834176773429481987 215155205751265160144222981)
              ·
                refine ⟨40341601078362217527041809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215155205751265160144222981 40341601078362217527041809)
                ·
                  refine ⟨30256200808771663145281357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40341601078362217527041809 30256200808771663145281357)
                  ·
                    refine ⟨11346075303289373679480509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30256200808771663145281357 11346075303289373679480509)
                    ·
                      refine ⟨4254778238733515129805191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11346075303289373679480509 4254778238733515129805191)
                      ·
                        rfl

theorem cell23_8286151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_8286151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286151 prefixEnd_8286151 := by exact prefixLift 8286151
  have htrace : WordTrace (prefixWord ++ tailWord_8286151) baseStart_8286151 baseEnd_8286151 := by
    simpa [prefixWord, tailWord_8286151, baseEnd_8286151] using wordTrace_append hprefix tailTrace_8286151
  have hstable : (prefixWord ++ tailWord_8286151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286151).length < 2 ^ (prefixWord ++ tailWord_8286151).sum := by decide
  have hdescent : baseEnd_8286151 < baseStart_8286151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286152 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_8286152 : Nat := 118140960795 + 8286152 * 2 ^ 59
def prefixEnd_8286152 : Nat := 4983230072969 + 3 ^ 40 * 8286152 * 2
def baseEnd_8286152 : Nat := 4254778752214169625892687

theorem tailTrace_8286152 : CollatzResearch.WordTrace tailWord_8286152 prefixEnd_8286152 4254778752214169625892687 := by
  unfold tailWord_8286152
  simp only [CollatzResearch.WordTrace]
  refine ⟨151110395938346970469950355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201480527917795960626600473 151110395938346970469950355)
  ·
    refine ⟨226665593907520455704925533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151110395938346970469950355 226665593907520455704925533)
    ·
      refine ⟨84999597715320170889347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226665593907520455704925533 84999597715320170889347075)
      ·
        refine ⟨127499396572980256334020613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84999597715320170889347075 127499396572980256334020613)
        ·
          refine ⟨23906136857433798062628865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127499396572980256334020613 23906136857433798062628865)
          ·
            refine ⟨17929602643075348546971649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23906136857433798062628865 17929602643075348546971649)
            ·
              refine ⟨13447201982306511410228737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17929602643075348546971649 13447201982306511410228737)
              ·
                refine ⟨10085401486729883557671553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13447201982306511410228737 10085401486729883557671553)
                ·
                  refine ⟨7564051115047412668253665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10085401486729883557671553 7564051115047412668253665)
                  ·
                    refine ⟨5673038336285559501190249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7564051115047412668253665 5673038336285559501190249)
                    ·
                      refine ⟨4254778752214169625892687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673038336285559501190249 4254778752214169625892687)
                      ·
                        rfl

theorem cell23_8286152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_8286152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286152 prefixEnd_8286152 := by exact prefixLift 8286152
  have htrace : WordTrace (prefixWord ++ tailWord_8286152) baseStart_8286152 baseEnd_8286152 := by
    simpa [prefixWord, tailWord_8286152, baseEnd_8286152] using wordTrace_append hprefix tailTrace_8286152
  have hstable : (prefixWord ++ tailWord_8286152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286152).length < 2 ^ (prefixWord ++ tailWord_8286152).sum := by decide
  have hdescent : baseEnd_8286152 < baseStart_8286152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286158 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 5]
def baseStart_8286158 : Nat := 118140960795 + 8286158 * 2 ^ 59
def prefixEnd_8286158 : Nat := 4983230072969 + 3 ^ 40 * 8286158 * 2
def baseEnd_8286158 : Nat := 472753537010899622490851

theorem tailTrace_8286158 : CollatzResearch.WordTrace tailWord_8286158 prefixEnd_8286158 472753537010899622490851 := by
  unfold tailWord_8286158
  simp only [CollatzResearch.WordTrace]
  refine ⟨37777626339334025495577391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201480673809781469309746085 37777626339334025495577391)
  ·
    refine ⟨56666439509001038243366087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37777626339334025495577391 56666439509001038243366087)
    ·
      refine ⟨84999659263501557365049131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56666439509001038243366087 84999659263501557365049131)
      ·
        refine ⟨127499488895252336047573697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84999659263501557365049131 127499488895252336047573697)
        ·
          refine ⟨95624616671439252035680273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127499488895252336047573697 95624616671439252035680273)
          ·
            refine ⟨71718462503579439026760205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95624616671439252035680273 71718462503579439026760205)
            ·
              refine ⟨26894423438842289635035077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71718462503579439026760205 26894423438842289635035077)
              ·
                refine ⟨5042704394782929306569077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26894423438842289635035077 5042704394782929306569077)
                ·
                  refine ⟨472753537010899622490851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042704394782929306569077 472753537010899622490851)
                  ·
                    rfl

theorem cell23_8286158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_8286158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286158 prefixEnd_8286158 := by exact prefixLift 8286158
  have htrace : WordTrace (prefixWord ++ tailWord_8286158) baseStart_8286158 baseEnd_8286158 := by
    simpa [prefixWord, tailWord_8286158, baseEnd_8286158] using wordTrace_append hprefix tailTrace_8286158
  have hstable : (prefixWord ++ tailWord_8286158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286158).length < 2 ^ (prefixWord ++ tailWord_8286158).sum := by decide
  have hdescent : baseEnd_8286158 < baseStart_8286158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286191 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_8286191 : Nat := 118140960795 + 8286191 * 2 ^ 59
def prefixEnd_8286191 : Nat := 4983230072969 + 3 ^ 40 * 8286191 * 2
def baseEnd_8286191 : Nat := 4254798777959694973305007

theorem tailTrace_8286191 : CollatzResearch.WordTrace tailWord_8286191 prefixEnd_8286191 4254798777959694973305007 := by
  unfold tailWord_8286191
  simp only [CollatzResearch.WordTrace]
  refine ⟨302222214323552650600570427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201481476215701767067046951 302222214323552650600570427)
  ·
    refine ⟨453333321485328975900855641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302222214323552650600570427 453333321485328975900855641)
    ·
      refine ⟨339999991113996731925641731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453333321485328975900855641 339999991113996731925641731)
      ·
        refine ⟨509999986670995097888462597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339999991113996731925641731 509999986670995097888462597)
        ·
          refine ⟨95624997500811580854086737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 509999986670995097888462597 95624997500811580854086737)
          ·
            refine ⟨71718748125608685640565053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95624997500811580854086737 71718748125608685640565053)
            ·
              refine ⟨26894530547103257115211895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71718748125608685640565053 26894530547103257115211895)
              ·
                refine ⟨40341795820654885672817843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26894530547103257115211895 40341795820654885672817843)
                ·
                  refine ⟨60512693730982328509226765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40341795820654885672817843 60512693730982328509226765)
                  ·
                    refine ⟨22692260149118373190960037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60512693730982328509226765 22692260149118373190960037)
                    ·
                      refine ⟨4254798777959694973305007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22692260149118373190960037 4254798777959694973305007)
                      ·
                        rfl

theorem cell23_8286191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_8286191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286191 prefixEnd_8286191 := by exact prefixLift 8286191
  have htrace : WordTrace (prefixWord ++ tailWord_8286191) baseStart_8286191 baseEnd_8286191 := by
    simpa [prefixWord, tailWord_8286191, baseEnd_8286191] using wordTrace_append hprefix tailTrace_8286191
  have hstable : (prefixWord ++ tailWord_8286191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286191).length < 2 ^ (prefixWord ++ tailWord_8286191).sum := by decide
  have hdescent : baseEnd_8286191 < baseStart_8286191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286298 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_8286298 : Nat := 118140960795 + 8286298 * 2 ^ 59
def prefixEnd_8286298 : Nat := 4983230072969 + 3 ^ 40 * 8286298 * 2
def baseEnd_8286298 : Nat := 4254853720389726054667015

theorem tailTrace_8286298 : CollatzResearch.WordTrace tailWord_8286298 prefixEnd_8286298 4254853720389726054667015 := by
  unfold tailWord_8286298
  simp only [CollatzResearch.WordTrace]
  refine ⟨75556529233541251968678887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201484077956110005249810365 75556529233541251968678887)
  ·
    refine ⟨113334793850311877953018331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75556529233541251968678887 113334793850311877953018331)
    ·
      refine ⟨170002190775467816929527497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113334793850311877953018331 170002190775467816929527497)
      ·
        refine ⟨127501643081600862697145623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170002190775467816929527497 127501643081600862697145623)
        ·
          refine ⟨191252464622401294045718435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127501643081600862697145623 191252464622401294045718435)
          ·
            refine ⟨286878696933601941068577653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191252464622401294045718435 286878696933601941068577653)
            ·
              refine ⟨26894877837525181975179155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286878696933601941068577653 26894877837525181975179155)
              ·
                refine ⟨40342316756287772962768733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26894877837525181975179155 40342316756287772962768733)
                ·
                  refine ⟨15128368783607914861038275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40342316756287772962768733 15128368783607914861038275)
                  ·
                    refine ⟨22692553175411872291557413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15128368783607914861038275 22692553175411872291557413)
                    ·
                      refine ⟨4254853720389726054667015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22692553175411872291557413 4254853720389726054667015)
                      ·
                        rfl

theorem cell23_8286298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_8286298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286298 prefixEnd_8286298 := by exact prefixLift 8286298
  have htrace : WordTrace (prefixWord ++ tailWord_8286298) baseStart_8286298 baseEnd_8286298 := by
    simpa [prefixWord, tailWord_8286298, baseEnd_8286298] using wordTrace_append hprefix tailTrace_8286298
  have hstable : (prefixWord ++ tailWord_8286298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286298).length < 2 ^ (prefixWord ++ tailWord_8286298).sum := by decide
  have hdescent : baseEnd_8286298 < baseStart_8286298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286308 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_8286308 : Nat := 118140960795 + 8286308 * 2 ^ 59
def prefixEnd_8286308 : Nat := 4983230072969 + 3 ^ 40 * 8286308 * 2
def baseEnd_8286308 : Nat := 1418286285065423671847323

theorem tailTrace_8286308 : CollatzResearch.WordTrace tailWord_8286308 prefixEnd_8286308 1418286285065423671847323 := by
  unfold tailWord_8286308
  simp only [CollatzResearch.WordTrace]
  refine ⟨151113240832064389791289789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201484321109419186388386385 151113240832064389791289789)
  ·
    refine ⟨56667465312024146171733671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151113240832064389791289789 56667465312024146171733671)
    ·
      refine ⟨85001197968036219257600507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56667465312024146171733671 85001197968036219257600507)
      ·
        refine ⟨127501796952054328886400761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85001197968036219257600507 127501796952054328886400761)
        ·
          refine ⟨95626347714040746664800571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127501796952054328886400761 95626347714040746664800571)
          ·
            refine ⟨143439521571061119997200857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95626347714040746664800571 143439521571061119997200857)
            ·
              refine ⟨107579641178295839997900643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143439521571061119997200857 107579641178295839997900643)
              ·
                refine ⟨161369461767443759996850965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107579641178295839997900643 161369461767443759996850965)
                ·
                  refine ⟨7564193520348926249852389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161369461767443759996850965 7564193520348926249852389)
                  ·
                    refine ⟨1418286285065423671847323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564193520348926249852389 1418286285065423671847323)
                    ·
                      rfl

theorem cell23_8286308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_8286308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286308 prefixEnd_8286308 := by exact prefixLift 8286308
  have htrace : WordTrace (prefixWord ++ tailWord_8286308) baseStart_8286308 baseEnd_8286308 := by
    simpa [prefixWord, tailWord_8286308, baseEnd_8286308] using wordTrace_append hprefix tailTrace_8286308
  have hstable : (prefixWord ++ tailWord_8286308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286308).length < 2 ^ (prefixWord ++ tailWord_8286308).sum := by decide
  have hdescent : baseEnd_8286308 < baseStart_8286308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286326 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_8286326 : Nat := 118140960795 + 8286326 * 2 ^ 59
def prefixEnd_8286326 : Nat := 4983230072969 + 3 ^ 40 * 8286326 * 2
def baseEnd_8286326 : Nat := 4254868097848051945116887

theorem tailTrace_8286326 : CollatzResearch.WordTrace tailWord_8286326 prefixEnd_8286326 4254868097848051945116887 := by
  unfold tailWord_8286326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889196136128973041045927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201484758785375712437823221 18889196136128973041045927)
  ·
    refine ⟨28333794204193459561568891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889196136128973041045927 28333794204193459561568891)
    ·
      refine ⟨42500691306290189342353337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28333794204193459561568891 42500691306290189342353337)
      ·
        refine ⟨31875518479717642006765003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42500691306290189342353337 31875518479717642006765003)
        ·
          refine ⟨47813277719576463010147505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31875518479717642006765003 47813277719576463010147505)
          ·
            refine ⟨35859958289682347257610629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47813277719576463010147505 35859958289682347257610629)
            ·
              refine ⟨6723742179315440110801993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35859958289682347257610629 6723742179315440110801993)
              ·
                refine ⟨5042806634486580083101495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6723742179315440110801993 5042806634486580083101495)
                ·
                  refine ⟨7564209951729870124652243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5042806634486580083101495 7564209951729870124652243)
                  ·
                    refine ⟨11346314927594805186978365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7564209951729870124652243 11346314927594805186978365)
                    ·
                      refine ⟨4254868097848051945116887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11346314927594805186978365 4254868097848051945116887)
                      ·
                        rfl

theorem cell23_8286326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_8286326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286326 prefixEnd_8286326 := by exact prefixLift 8286326
  have htrace : WordTrace (prefixWord ++ tailWord_8286326) baseStart_8286326 baseEnd_8286326 := by
    simpa [prefixWord, tailWord_8286326, baseEnd_8286326] using wordTrace_append hprefix tailTrace_8286326
  have hstable : (prefixWord ++ tailWord_8286326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286326).length < 2 ^ (prefixWord ++ tailWord_8286326).sum := by decide
  have hdescent : baseEnd_8286326 < baseStart_8286326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286365 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_8286365 : Nat := 118140960795 + 8286365 * 2 ^ 59
def prefixEnd_8286365 : Nat := 4983230072969 + 3 ^ 40 * 8286365 * 2
def baseEnd_8286365 : Nat := 4254888123593577292529207

theorem tailTrace_8286365 : CollatzResearch.WordTrace tailWord_8286365 prefixEnd_8286365 4254888123593577292529207 := by
  unfold tailWord_8286365
  simp only [CollatzResearch.WordTrace]
  refine ⟨302228560624922278317404549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201485707083281518878269699 302228560624922278317404549)
  ·
    refine ⟨56667855117172927184513353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302228560624922278317404549 56667855117172927184513353)
    ·
      refine ⟨42500891337879695388385015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56667855117172927184513353 42500891337879695388385015)
      ·
        refine ⟨63751337006819543082577523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42500891337879695388385015 63751337006819543082577523)
        ·
          refine ⟨95627005510229314623866285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63751337006819543082577523 95627005510229314623866285)
          ·
            refine ⟨35860127066335992983949857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95627005510229314623866285 35860127066335992983949857)
            ·
              refine ⟨26895095299751994737962393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35860127066335992983949857 26895095299751994737962393)
              ·
                refine ⟨20171321474813996053471795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26895095299751994737962393 20171321474813996053471795)
                ·
                  refine ⟨30256982212220994080207693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20171321474813996053471795 30256982212220994080207693)
                  ·
                    refine ⟨11346368329582872780077885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30256982212220994080207693 11346368329582872780077885)
                    ·
                      refine ⟨4254888123593577292529207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11346368329582872780077885 4254888123593577292529207)
                      ·
                        rfl

theorem cell23_8286365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_8286365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286365 prefixEnd_8286365 := by exact prefixLift 8286365
  have htrace : WordTrace (prefixWord ++ tailWord_8286365) baseStart_8286365 baseEnd_8286365 := by
    simpa [prefixWord, tailWord_8286365, baseEnd_8286365] using wordTrace_append hprefix tailTrace_8286365
  have hstable : (prefixWord ++ tailWord_8286365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286365).length < 2 ^ (prefixWord ++ tailWord_8286365).sum := by decide
  have hdescent : baseEnd_8286365 < baseStart_8286365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286366 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_8286366 : Nat := 118140960795 + 8286366 * 2 ^ 59
def prefixEnd_8286366 : Nat := 4983230072969 + 3 ^ 40 * 8286366 * 2
def baseEnd_8286366 : Nat := 4254888637074231788616703

theorem tailTrace_8286366 : CollatzResearch.WordTrace tailWord_8286366 prefixEnd_8286366 4254888637074231788616703 := by
  unfold tailWord_8286366
  simp only [CollatzResearch.WordTrace]
  refine ⟨37778574637239831936023869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201485731398612436992127301 37778574637239831936023869)
  ·
    refine ⟨14166965488964936976008951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37778574637239831936023869 14166965488964936976008951)
    ·
      refine ⟨21250448233447405464013427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14166965488964936976008951 21250448233447405464013427)
      ·
        refine ⟨31875672350171108196020141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21250448233447405464013427 31875672350171108196020141)
        ·
          refine ⟨11953377131314165573507553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31875672350171108196020141 11953377131314165573507553)
          ·
            refine ⟨8965032848485624180130665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11953377131314165573507553 8965032848485624180130665)
            ·
              refine ⟨6723774636364218135097999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8965032848485624180130665 6723774636364218135097999)
              ·
                refine ⟨10085661954546327202646999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723774636364218135097999 10085661954546327202646999)
                ·
                  refine ⟨15128492931819490803970499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10085661954546327202646999 15128492931819490803970499)
                  ·
                    refine ⟨22692739397729236205955749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15128492931819490803970499 22692739397729236205955749)
                    ·
                      refine ⟨4254888637074231788616703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22692739397729236205955749 4254888637074231788616703)
                      ·
                        rfl

theorem cell23_8286366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_8286366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286366 prefixEnd_8286366 := by exact prefixLift 8286366
  have htrace : WordTrace (prefixWord ++ tailWord_8286366) baseStart_8286366 baseEnd_8286366 := by
    simpa [prefixWord, tailWord_8286366, baseEnd_8286366] using wordTrace_append hprefix tailTrace_8286366
  have hstable : (prefixWord ++ tailWord_8286366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286366).length < 2 ^ (prefixWord ++ tailWord_8286366).sum := by decide
  have hdescent : baseEnd_8286366 < baseStart_8286366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286369 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_8286369 : Nat := 118140960795 + 8286369 * 2 ^ 59
def prefixEnd_8286369 : Nat := 4983230072969 + 3 ^ 40 * 8286369 * 2
def baseEnd_8286369 : Nat := 4254890177516195276879189

theorem tailTrace_8286369 : CollatzResearch.WordTrace tailWord_8286369 prefixEnd_8286369 4254890177516195276879189 := by
  unfold tailWord_8286369
  simp only [CollatzResearch.WordTrace]
  refine ⟨302228706516907787000550161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201485804344605191333700107 302228706516907787000550161)
  ·
    refine ⟨226671529887680840250412621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302228706516907787000550161 226671529887680840250412621)
    ·
      refine ⟨85001823707880315093904733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226671529887680840250412621 85001823707880315093904733)
      ·
        refine ⟨31875683890455118160214275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85001823707880315093904733 31875683890455118160214275)
        ·
          refine ⟨47813525835682677240321413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31875683890455118160214275 47813525835682677240321413)
          ·
            refine ⟨8965036094190501982560265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47813525835682677240321413 8965036094190501982560265)
            ·
              refine ⟨6723777070642876486920199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8965036094190501982560265 6723777070642876486920199)
              ·
                refine ⟨10085665605964314730380299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6723777070642876486920199 10085665605964314730380299)
                ·
                  refine ⟨15128498408946472095570449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10085665605964314730380299 15128498408946472095570449)
                  ·
                    refine ⟨11346373806709854071677837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15128498408946472095570449 11346373806709854071677837)
                    ·
                      refine ⟨4254890177516195276879189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11346373806709854071677837 4254890177516195276879189)
                      ·
                        rfl

theorem cell23_8286369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_8286369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286369 prefixEnd_8286369 := by exact prefixLift 8286369
  have htrace : WordTrace (prefixWord ++ tailWord_8286369) baseStart_8286369 baseEnd_8286369 := by
    simpa [prefixWord, tailWord_8286369, baseEnd_8286369] using wordTrace_append hprefix tailTrace_8286369
  have hstable : (prefixWord ++ tailWord_8286369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286369).length < 2 ^ (prefixWord ++ tailWord_8286369).sum := by decide
  have hdescent : baseEnd_8286369 < baseStart_8286369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286408 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_8286408 : Nat := 118140960795 + 8286408 * 2 ^ 59
def prefixEnd_8286408 : Nat := 4983230072969 + 3 ^ 40 * 8286408 * 2
def baseEnd_8286408 : Nat := 4254910203261720624291509

theorem tailTrace_8286408 : CollatzResearch.WordTrace tailWord_8286408 prefixEnd_8286408 4254910203261720624291509 := by
  unfold tailWord_8286408
  simp only [CollatzResearch.WordTrace]
  refine ⟨151115064481883248330609939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201486752642510997774146585 151115064481883248330609939)
  ·
    refine ⟨226672596722824872495914909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151115064481883248330609939 226672596722824872495914909)
    ·
      refine ⟨85002223771059327185968091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226672596722824872495914909 85002223771059327185968091)
      ·
        refine ⟨127503335656588990778952137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85002223771059327185968091 127503335656588990778952137)
        ·
          refine ⟨95627501742441743084214103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127503335656588990778952137 95627501742441743084214103)
          ·
            refine ⟨143441252613662614626321155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95627501742441743084214103 143441252613662614626321155)
            ·
              refine ⟨215161878920493921939481733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143441252613662614626321155 215161878920493921939481733)
              ·
                refine ⟨40342852297592610363652825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215161878920493921939481733 40342852297592610363652825)
                ·
                  refine ⟨30257139223194457772739619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40342852297592610363652825 30257139223194457772739619)
                  ·
                    refine ⟨45385708834791686659109429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30257139223194457772739619 45385708834791686659109429)
                    ·
                      refine ⟨4254910203261720624291509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45385708834791686659109429 4254910203261720624291509)
                      ·
                        rfl

theorem cell23_8286408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_8286408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286408 prefixEnd_8286408 := by exact prefixLift 8286408
  have htrace : WordTrace (prefixWord ++ tailWord_8286408) baseStart_8286408 baseEnd_8286408 := by
    simpa [prefixWord, tailWord_8286408, baseEnd_8286408] using wordTrace_append hprefix tailTrace_8286408
  have hstable : (prefixWord ++ tailWord_8286408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286408).length < 2 ^ (prefixWord ++ tailWord_8286408).sum := by decide
  have hdescent : baseEnd_8286408 < baseStart_8286408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286439 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8286439 : Nat := 118140960795 + 8286439 * 2 ^ 59
def prefixEnd_8286439 : Nat := 4983230072969 + 3 ^ 40 * 8286439 * 2
def baseEnd_8286439 : Nat := 4254926121162010003003867

theorem tailTrace_8286439 : CollatzResearch.WordTrace tailWord_8286439 prefixEnd_8286439 4254926121162010003003867 := by
  unfold tailWord_8286439
  simp only [CollatzResearch.WordTrace]
  refine ⟨302231259626654188955598371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201487506417769459303732247 302231259626654188955598371)
  ·
    refine ⟨453346889439981283433397557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302231259626654188955598371 453346889439981283433397557)
    ·
      refine ⟨42501270884998245321881021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453346889439981283433397557 42501270884998245321881021)
      ·
        refine ⟨15937976581874341995705383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42501270884998245321881021 15937976581874341995705383)
        ·
          refine ⟨23906964872811512993558075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15937976581874341995705383 23906964872811512993558075)
          ·
            refine ⟨35860447309217269490337113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23906964872811512993558075 35860447309217269490337113)
            ·
              refine ⟨26895335481912952117752835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35860447309217269490337113 26895335481912952117752835)
              ·
                refine ⟨40343003222869428176629253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26895335481912952117752835 40343003222869428176629253)
                ·
                  refine ⟨7564313104288017783117985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40343003222869428176629253 7564313104288017783117985)
                  ·
                    refine ⟨5673234828216013337338489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7564313104288017783117985 5673234828216013337338489)
                    ·
                      refine ⟨4254926121162010003003867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673234828216013337338489 4254926121162010003003867)
                      ·
                        rfl

theorem cell23_8286439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8286439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286439 prefixEnd_8286439 := by exact prefixLift 8286439
  have htrace : WordTrace (prefixWord ++ tailWord_8286439) baseStart_8286439 baseEnd_8286439 := by
    simpa [prefixWord, tailWord_8286439, baseEnd_8286439] using wordTrace_append hprefix tailTrace_8286439
  have hstable : (prefixWord ++ tailWord_8286439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286439).length < 2 ^ (prefixWord ++ tailWord_8286439).sum := by decide
  have hdescent : baseEnd_8286439 < baseStart_8286439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
