import V185TrunkScan23Chunk0578

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3423929 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3423929 : Nat := 118140960795 + 3423929 * 2 ^ 59
def prefixEnd_3423929 : Nat := 4983230072969 + 3 ^ 40 * 3423929 * 2
def baseEnd_3423929 : Nat := 1758121303868239595741143

theorem tailTrace_3423929 : CollatzResearch.WordTrace tailWord_3423929 prefixEnd_3423929 1758121303868239595741143 := by
  unfold tailWord_3423929
  simp only [CollatzResearch.WordTrace]
  refine ⟨124880950012697468363146841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83253966675131645575431227 124880950012697468363146841)
  ·
    refine ⟨93660712509523101272360131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124880950012697468363146841 93660712509523101272360131)
    ·
      refine ⟨140491068764284651908540197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93660712509523101272360131 140491068764284651908540197)
      ·
        refine ⟨26342075393303372232851287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140491068764284651908540197 26342075393303372232851287)
        ·
          refine ⟨39513113089955058349276931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26342075393303372232851287 39513113089955058349276931)
          ·
            refine ⟨59269669634932587523915397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39513113089955058349276931 59269669634932587523915397)
            ·
              refine ⟨11113063056549860160734137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59269669634932587523915397 11113063056549860160734137)
              ·
                refine ⟨8334797292412395120550603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11113063056549860160734137 8334797292412395120550603)
                ·
                  refine ⟨12502195938618592680825905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8334797292412395120550603 12502195938618592680825905)
                  ·
                    refine ⟨9376646953963944510619429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12502195938618592680825905 9376646953963944510619429)
                    ·
                      refine ⟨1758121303868239595741143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9376646953963944510619429 1758121303868239595741143)
                      ·
                        rfl

theorem cell23_3423929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3423929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423929 prefixEnd_3423929 := by exact prefixLift 3423929
  have htrace : WordTrace (prefixWord ++ tailWord_3423929) baseStart_3423929 baseEnd_3423929 := by
    simpa [prefixWord, tailWord_3423929, baseEnd_3423929] using wordTrace_append hprefix tailTrace_3423929
  have hstable : (prefixWord ++ tailWord_3423929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423929).length < 2 ^ (prefixWord ++ tailWord_3423929).sum := by decide
  have hdescent : baseEnd_3423929 < baseStart_3423929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423936 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_3423936 : Nat := 118140960795 + 3423936 * 2 ^ 59
def prefixEnd_3423936 : Nat := 4983230072969 + 3 ^ 40 * 3423936 * 2
def baseEnd_3423936 : Nat := 1758124898232821068353611

theorem tailTrace_3423936 : CollatzResearch.WordTrace tailWord_3423936 prefixEnd_3423936 1758124898232821068353611 := by
  unfold tailWord_3423936
  simp only [CollatzResearch.WordTrace]
  refine ⟨62440602661836054279325831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83254136882448072372434441 62440602661836054279325831)
  ·
    refine ⟨93660903992754081418988747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62440602661836054279325831 93660903992754081418988747)
    ·
      refine ⟨140491355989131122128483121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93660903992754081418988747 140491355989131122128483121)
      ·
        refine ⟨105368516991848341596362341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140491355989131122128483121 105368516991848341596362341)
        ·
          refine ⟨19756596935971564049317939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105368516991848341596362341 19756596935971564049317939)
          ·
            refine ⟨29634895403957346073976909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19756596935971564049317939 29634895403957346073976909)
            ·
              refine ⟨11113085776484004777741341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29634895403957346073976909 11113085776484004777741341)
              ·
                refine ⟨4167407166181501791653003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11113085776484004777741341 4167407166181501791653003)
                ·
                  refine ⟨6251110749272252687479505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167407166181501791653003 6251110749272252687479505)
                  ·
                    refine ⟨4688333061954189515609629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6251110749272252687479505 4688333061954189515609629)
                    ·
                      refine ⟨1758124898232821068353611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688333061954189515609629 1758124898232821068353611)
                      ·
                        rfl

theorem cell23_3423936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_3423936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423936 prefixEnd_3423936 := by exact prefixLift 3423936
  have htrace : WordTrace (prefixWord ++ tailWord_3423936) baseStart_3423936 baseEnd_3423936 := by
    simpa [prefixWord, tailWord_3423936, baseEnd_3423936] using wordTrace_append hprefix tailTrace_3423936
  have hstable : (prefixWord ++ tailWord_3423936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423936).length < 2 ^ (prefixWord ++ tailWord_3423936).sum := by decide
  have hdescent : baseEnd_3423936 < baseStart_3423936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423950 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_3423950 : Nat := 118140960795 + 3423950 * 2 ^ 59
def prefixEnd_3423950 : Nat := 4983230072969 + 3 ^ 40 * 3423950 * 2
def baseEnd_3423950 : Nat := 1758132086961984013578547

theorem tailTrace_3423950 : CollatzResearch.WordTrace tailWord_3423950 prefixEnd_3423950 1758132086961984013578547 := by
  unfold tailWord_3423950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15610214493202673618707663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83254477297080925966440869 15610214493202673618707663)
  ·
    refine ⟨23415321739804010428061495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15610214493202673618707663 23415321739804010428061495)
    ·
      refine ⟨35122982609706015642092243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23415321739804010428061495 35122982609706015642092243)
      ·
        refine ⟨52684473914559023463138365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35122982609706015642092243 52684473914559023463138365)
        ·
          refine ⟨19756677717959633798676887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52684473914559023463138365 19756677717959633798676887)
          ·
            refine ⟨29635016576939450698015331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19756677717959633798676887 29635016576939450698015331)
            ·
              refine ⟨44452524865409176047022997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29635016576939450698015331 44452524865409176047022997)
              ·
                refine ⟨2083712103066055127204203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44452524865409176047022997 2083712103066055127204203)
                ·
                  refine ⟨3125568154599082690806305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083712103066055127204203 3125568154599082690806305)
                  ·
                    refine ⟨2344176115949312018104729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3125568154599082690806305 2344176115949312018104729)
                    ·
                      refine ⟨1758132086961984013578547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344176115949312018104729 1758132086961984013578547)
                      ·
                        rfl

theorem cell23_3423950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_3423950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423950 prefixEnd_3423950 := by exact prefixLift 3423950
  have htrace : WordTrace (prefixWord ++ tailWord_3423950) baseStart_3423950 baseEnd_3423950 := by
    simpa [prefixWord, tailWord_3423950, baseEnd_3423950] using wordTrace_append hprefix tailTrace_3423950
  have hstable : (prefixWord ++ tailWord_3423950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423950).length < 2 ^ (prefixWord ++ tailWord_3423950).sum := by decide
  have hdescent : baseEnd_3423950 < baseStart_3423950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3423952 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_3423952 : Nat := 118140960795 + 3423952 * 2 ^ 59
def prefixEnd_3423952 : Nat := 4983230072969 + 3 ^ 40 * 3423952 * 2
def baseEnd_3423952 : Nat := 586044371307764335251179

theorem tailTrace_3423952 : CollatzResearch.WordTrace tailWord_3423952 prefixEnd_3423952 586044371307764335251179 := by
  unfold tailWord_3423952
  simp only [CollatzResearch.WordTrace]
  refine ⟨62440894445807071645617055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83254525927742762194156073 62440894445807071645617055)
  ·
    refine ⟨93661341668710607468425583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62440894445807071645617055 93661341668710607468425583)
    ·
      refine ⟨140492012503065911202638375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93661341668710607468425583 140492012503065911202638375)
      ·
        refine ⟨210738018754598866803957563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140492012503065911202638375 210738018754598866803957563)
        ·
          refine ⟨316107028131898300205936345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210738018754598866803957563 316107028131898300205936345)
          ·
            refine ⟨237080271098923725154452259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316107028131898300205936345 237080271098923725154452259)
            ·
              refine ⟨355620406648385587731678389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237080271098923725154452259 355620406648385587731678389)
              ·
                refine ⟨33339413123286148849844849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355620406648385587731678389 33339413123286148849844849)
                ·
                  refine ⟨25004559842464611637383637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33339413123286148849844849 25004559842464611637383637)
                  ·
                    refine ⟨586044371307764335251179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25004559842464611637383637 586044371307764335251179)
                    ·
                      rfl

theorem cell23_3423952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_3423952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3423952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3423952 prefixEnd_3423952 := by exact prefixLift 3423952
  have htrace : WordTrace (prefixWord ++ tailWord_3423952) baseStart_3423952 baseEnd_3423952 := by
    simpa [prefixWord, tailWord_3423952, baseEnd_3423952] using wordTrace_append hprefix tailTrace_3423952
  have hstable : (prefixWord ++ tailWord_3423952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3423952).length < 2 ^ (prefixWord ++ tailWord_3423952).sum := by decide
  have hdescent : baseEnd_3423952 < baseStart_3423952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3423952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424009 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_3424009 : Nat := 118140960795 + 3424009 * 2 ^ 59
def prefixEnd_3424009 : Nat := 4983230072969 + 3 ^ 40 * 3424009 * 2
def baseEnd_3424009 : Nat := 1758162382320599282740775

theorem tailTrace_3424009 : CollatzResearch.WordTrace tailWord_3424009 prefixEnd_3424009 1758162382320599282740775 := by
  unfold tailWord_3424009
  simp only [CollatzResearch.WordTrace]
  refine ⟨124883867852407642026059081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83255911901605094684039387 124883867852407642026059081)
  ·
    refine ⟨93662900889305731519544311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124883867852407642026059081 93662900889305731519544311)
    ·
      refine ⟨140494351333958597279316467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93662900889305731519544311 140494351333958597279316467)
      ·
        refine ⟨210741527000937895918974701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140494351333958597279316467 210741527000937895918974701)
        ·
          refine ⟨79028072625351710969615513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210741527000937895918974701 79028072625351710969615513)
          ·
            refine ⟨59271054469013783227211635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79028072625351710969615513 59271054469013783227211635)
            ·
              refine ⟨88906581703520674840817453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59271054469013783227211635 88906581703520674840817453)
              ·
                refine ⟨33339968138820253065306545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88906581703520674840817453 33339968138820253065306545)
                ·
                  refine ⟨25004976104115189798979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33339968138820253065306545 25004976104115189798979909)
                  ·
                    refine ⟨4688433019521598087308733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25004976104115189798979909 4688433019521598087308733)
                    ·
                      refine ⟨1758162382320599282740775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688433019521598087308733 1758162382320599282740775)
                      ·
                        rfl

theorem cell23_3424009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_3424009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424009 prefixEnd_3424009 := by exact prefixLift 3424009
  have htrace : WordTrace (prefixWord ++ tailWord_3424009) baseStart_3424009 baseEnd_3424009 := by
    simpa [prefixWord, tailWord_3424009, baseEnd_3424009] using wordTrace_append hprefix tailTrace_3424009
  have hstable : (prefixWord ++ tailWord_3424009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424009).length < 2 ^ (prefixWord ++ tailWord_3424009).sum := by decide
  have hdescent : baseEnd_3424009 < baseStart_3424009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424063 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 5]
def baseStart_3424063 : Nat := 118140960795 + 3424063 * 2 ^ 59
def prefixEnd_3424063 : Nat := 4983230072969 + 3 ^ 40 * 3424063 * 2
def baseEnd_3424063 : Nat := 195354456697326896829503

theorem tailTrace_3424063 : CollatzResearch.WordTrace tailWord_3424063 prefixEnd_3424063 195354456697326896829503 := by
  unfold tailWord_3424063
  simp only [CollatzResearch.WordTrace]
  refine ⟨124885837394212009248524843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83257224929474672832349895 124885837394212009248524843)
  ·
    refine ⟨187328756091318013872787265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124885837394212009248524843 187328756091318013872787265)
    ·
      refine ⟨140496567068488510404590449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187328756091318013872787265 140496567068488510404590449)
      ·
        refine ⟨105372425301366382803442837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140496567068488510404590449 105372425301366382803442837)
        ·
          refine ⟨4939332436001549193911383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105372425301366382803442837 4939332436001549193911383)
          ·
            refine ⟨7408998654002323790867075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939332436001549193911383 7408998654002323790867075)
            ·
              refine ⟨11113497981003485686300613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408998654002323790867075 11113497981003485686300613)
              ·
                refine ⟨2083780871438153566181365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11113497981003485686300613 2083780871438153566181365)
                ·
                  refine ⟨195354456697326896829503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083780871438153566181365 195354456697326896829503)
                  ·
                    rfl

theorem cell23_3424063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 5].length) (baseStart_3424063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424063 prefixEnd_3424063 := by exact prefixLift 3424063
  have htrace : WordTrace (prefixWord ++ tailWord_3424063) baseStart_3424063 baseEnd_3424063 := by
    simpa [prefixWord, tailWord_3424063, baseEnd_3424063] using wordTrace_append hprefix tailTrace_3424063
  have hstable : (prefixWord ++ tailWord_3424063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424063).length < 2 ^ (prefixWord ++ tailWord_3424063).sum := by decide
  have hdescent : baseEnd_3424063 < baseStart_3424063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424069 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_3424069 : Nat := 118140960795 + 3424069 * 2 ^ 59
def prefixEnd_3424069 : Nat := 4983230072969 + 3 ^ 40 * 3424069 * 2
def baseEnd_3424069 : Nat := 1758193191159869047990499

theorem tailTrace_3424069 : CollatzResearch.WordTrace tailWord_3424069 prefixEnd_3424069 1758193191159869047990499 := by
  unfold tailWord_3424069
  simp only [CollatzResearch.WordTrace]
  refine ⟨124886056232190272273243261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83257370821460181515495507 124886056232190272273243261)
  ·
    refine ⟨46832271087071352102466223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124886056232190272273243261 46832271087071352102466223)
    ·
      refine ⟨70248406630607028153699335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46832271087071352102466223 70248406630607028153699335)
      ·
        refine ⟨105372609945910542230549003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70248406630607028153699335 105372609945910542230549003)
        ·
          refine ⟨158058914918865813345823505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105372609945910542230549003 158058914918865813345823505)
          ·
            refine ⟨118544186189149360009367629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158058914918865813345823505 118544186189149360009367629)
            ·
              refine ⟨44454069820931010003512861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118544186189149360009367629 44454069820931010003512861)
              ·
                refine ⟨16670276182849128751317323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44454069820931010003512861 16670276182849128751317323)
                ·
                  refine ⟨25005414274273693126975985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16670276182849128751317323 25005414274273693126975985)
                  ·
                    refine ⟨18754060705705269845231989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25005414274273693126975985 18754060705705269845231989)
                    ·
                      refine ⟨1758193191159869047990499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18754060705705269845231989 1758193191159869047990499)
                      ·
                        rfl

theorem cell23_3424069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_3424069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424069 prefixEnd_3424069 := by exact prefixLift 3424069
  have htrace : WordTrace (prefixWord ++ tailWord_3424069) baseStart_3424069 baseEnd_3424069 := by
    simpa [prefixWord, tailWord_3424069, baseEnd_3424069] using wordTrace_append hprefix tailTrace_3424069
  have hstable : (prefixWord ++ tailWord_3424069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424069).length < 2 ^ (prefixWord ++ tailWord_3424069).sum := by decide
  have hdescent : baseEnd_3424069 < baseStart_3424069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424070 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3424070 : Nat := 118140960795 + 3424070 * 2 ^ 59
def prefixEnd_3424070 : Nat := 4983230072969 + 3 ^ 40 * 3424070 * 2
def baseEnd_3424070 : Nat := 1758193704640523544077995

theorem tailTrace_3424070 : CollatzResearch.WordTrace tailWord_3424070 prefixEnd_3424070 1758193704640523544077995 := by
  unfold tailWord_3424070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902690397037082795125927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83257395136791099629353109 3902690397037082795125927)
  ·
    refine ⟨5854035595555624192688891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3902690397037082795125927 5854035595555624192688891)
    ·
      refine ⟨8781053393333436289033337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854035595555624192688891 8781053393333436289033337)
      ·
        refine ⟨6585790045000077216775003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8781053393333436289033337 6585790045000077216775003)
        ·
          refine ⟨9878685067500115825162505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585790045000077216775003 9878685067500115825162505)
          ·
            refine ⟨7409013800625086868871879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9878685067500115825162505 7409013800625086868871879)
            ·
              refine ⟨11113520700937630303307819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409013800625086868871879 11113520700937630303307819)
              ·
                refine ⟨16670281051406445454961729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11113520700937630303307819 16670281051406445454961729)
                ·
                  refine ⟨12502710788554834091221297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16670281051406445454961729 12502710788554834091221297)
                  ·
                    refine ⟨9377033091416125568415973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12502710788554834091221297 9377033091416125568415973)
                    ·
                      refine ⟨1758193704640523544077995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9377033091416125568415973 1758193704640523544077995)
                      ·
                        rfl

theorem cell23_3424070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3424070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424070 prefixEnd_3424070 := by exact prefixLift 3424070
  have htrace : WordTrace (prefixWord ++ tailWord_3424070) baseStart_3424070 baseEnd_3424070 := by
    simpa [prefixWord, tailWord_3424070, baseEnd_3424070] using wordTrace_append hprefix tailTrace_3424070
  have hstable : (prefixWord ++ tailWord_3424070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424070).length < 2 ^ (prefixWord ++ tailWord_3424070).sum := by decide
  have hdescent : baseEnd_3424070 < baseStart_3424070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424096 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_3424096 : Nat := 118140960795 + 3424096 * 2 ^ 59
def prefixEnd_3424096 : Nat := 4983230072969 + 3 ^ 40 * 3424096 * 2
def baseEnd_3424096 : Nat := 1758207055137540442352875

theorem tailTrace_3424096 : CollatzResearch.WordTrace tailWord_3424096 prefixEnd_3424096 1758207055137540442352875 := by
  unfold tailWord_3424096
  simp only [CollatzResearch.WordTrace]
  refine ⟨62443520501546227942238071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83258027335394970589650761 62443520501546227942238071)
  ·
    refine ⟨93665280752319341913357107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62443520501546227942238071 93665280752319341913357107)
    ·
      refine ⟨140497921128479012870035661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93665280752319341913357107 140497921128479012870035661)
      ·
        refine ⟨52686720423179629826263373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140497921128479012870035661 52686720423179629826263373)
        ·
          refine ⟨19757520158692361184848765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52686720423179629826263373 19757520158692361184848765)
          ·
            refine ⟨7409070059509635444318287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19757520158692361184848765 7409070059509635444318287)
            ·
              refine ⟨11113605089264453166477431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409070059509635444318287 11113605089264453166477431)
              ·
                refine ⟨16670407633896679749716147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11113605089264453166477431 16670407633896679749716147)
                ·
                  refine ⟨25005611450845019624574221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16670407633896679749716147 25005611450845019624574221)
                  ·
                    refine ⟨9377104294066882359215333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25005611450845019624574221 9377104294066882359215333)
                    ·
                      refine ⟨1758207055137540442352875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9377104294066882359215333 1758207055137540442352875)
                      ·
                        rfl

theorem cell23_3424096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_3424096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424096 prefixEnd_3424096 := by exact prefixLift 3424096
  have htrace : WordTrace (prefixWord ++ tailWord_3424096) baseStart_3424096 baseEnd_3424096 := by
    simpa [prefixWord, tailWord_3424096, baseEnd_3424096] using wordTrace_append hprefix tailTrace_3424096
  have hstable : (prefixWord ++ tailWord_3424096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424096).length < 2 ^ (prefixWord ++ tailWord_3424096).sum := by decide
  have hdescent : baseEnd_3424096 < baseStart_3424096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424139 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6]
def baseStart_3424139 : Nat := 118140960795 + 3424139 * 2 ^ 59
def prefixEnd_3424139 : Nat := 4983230072969 + 3 ^ 40 * 3424139 * 2
def baseEnd_3424139 : Nat := 1758229134805683774115177

theorem tailTrace_3424139 : CollatzResearch.WordTrace tailWord_3424139 prefixEnd_3424139 1758229134805683774115177 := by
  unfold tailWord_3424139
  simp only [CollatzResearch.WordTrace]
  refine ⟨124888609341936674228291471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83259072894624449485527647 124888609341936674228291471)
  ·
    refine ⟨187332914012905011342437207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124888609341936674228291471 187332914012905011342437207)
    ·
      refine ⟨280999371019357517013655811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187332914012905011342437207 280999371019357517013655811)
      ·
        refine ⟨421499056529036275520483717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280999371019357517013655811 421499056529036275520483717)
        ·
          refine ⟨79031073099194301660090697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421499056529036275520483717 79031073099194301660090697)
          ·
            refine ⟨59273304824395726245068023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79031073099194301660090697 59273304824395726245068023)
            ·
              refine ⟨88909957236593589367602035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59273304824395726245068023 88909957236593589367602035)
              ·
                refine ⟨133364935854890384051403053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88909957236593589367602035 133364935854890384051403053)
                ·
                  refine ⟨50011850945583894019276145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133364935854890384051403053 50011850945583894019276145)
                  ·
                    refine ⟨37508888209187920514457109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50011850945583894019276145 37508888209187920514457109)
                    ·
                      refine ⟨1758229134805683774115177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37508888209187920514457109 1758229134805683774115177)
                      ·
                        rfl

theorem cell23_3424139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_3424139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424139 prefixEnd_3424139 := by exact prefixLift 3424139
  have htrace : WordTrace (prefixWord ++ tailWord_3424139) baseStart_3424139 baseEnd_3424139 := by
    simpa [prefixWord, tailWord_3424139, baseEnd_3424139] using wordTrace_append hprefix tailTrace_3424139
  have hstable : (prefixWord ++ tailWord_3424139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424139).length < 2 ^ (prefixWord ++ tailWord_3424139).sum := by decide
  have hdescent : baseEnd_3424139 < baseStart_3424139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424157 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_3424157 : Nat := 118140960795 + 3424157 * 2 ^ 59
def prefixEnd_3424157 : Nat := 4983230072969 + 3 ^ 40 * 3424157 * 2
def baseEnd_3424157 : Nat := 586079459152488234563365

theorem tailTrace_3424157 : CollatzResearch.WordTrace tailWord_3424157 prefixEnd_3424157 586079459152488234563365 := by
  unfold tailWord_3424157
  simp only [CollatzResearch.WordTrace]
  refine ⟨124889265855871463302446725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83259510570580975534964483 124889265855871463302446725)
  ·
    refine ⟨23416737347975899369208761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124889265855871463302446725 23416737347975899369208761)
    ·
      refine ⟨17562553010981924526906571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23416737347975899369208761 17562553010981924526906571)
      ·
        refine ⟨26343829516472886790359857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17562553010981924526906571 26343829516472886790359857)
        ·
          refine ⟨19757872137354665092769893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26343829516472886790359857 19757872137354665092769893)
          ·
            refine ⟨3704601025753999704894355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19757872137354665092769893 3704601025753999704894355)
            ·
              refine ⟨5556901538630999557341533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704601025753999704894355 5556901538630999557341533)
              ·
                refine ⟨2083838076986624834003075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5556901538630999557341533 2083838076986624834003075)
                ·
                  refine ⟨3125757115479937251004613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083838076986624834003075 3125757115479937251004613)
                  ·
                    refine ⟨586079459152488234563365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125757115479937251004613 586079459152488234563365)
                    ·
                      rfl

theorem cell23_3424157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_3424157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424157 prefixEnd_3424157 := by exact prefixLift 3424157
  have htrace : WordTrace (prefixWord ++ tailWord_3424157) baseStart_3424157 baseEnd_3424157 := by
    simpa [prefixWord, tailWord_3424157, baseEnd_3424157] using wordTrace_append hprefix tailTrace_3424157
  have hstable : (prefixWord ++ tailWord_3424157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424157).length < 2 ^ (prefixWord ++ tailWord_3424157).sum := by decide
  have hdescent : baseEnd_3424157 < baseStart_3424157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424200 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_3424200 : Nat := 118140960795 + 3424200 * 2 ^ 59
def prefixEnd_3424200 : Nat := 4983230072969 + 3 ^ 40 * 3424200 * 2
def baseEnd_3424200 : Nat := 586086819041869345150799

theorem tailTrace_3424200 : CollatzResearch.WordTrace tailWord_3424200 prefixEnd_3424200 586086819041869345150799 := by
  unfold tailWord_3424200
  simp only [CollatzResearch.WordTrace]
  refine ⟨62445417097357840823131027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83260556129810454430841369 62445417097357840823131027)
  ·
    refine ⟨93668125646036761234696541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62445417097357840823131027 93668125646036761234696541)
    ·
      refine ⟨35125547117263785463011203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93668125646036761234696541 35125547117263785463011203)
      ·
        refine ⟨52688320675895678194516805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35125547117263785463011203 52688320675895678194516805)
        ·
          refine ⟨9879060126730439661471901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52688320675895678194516805 9879060126730439661471901)
          ·
            refine ⟨3704647547523914873051963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9879060126730439661471901 3704647547523914873051963)
            ·
              refine ⟨5556971321285872309577945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704647547523914873051963 5556971321285872309577945)
              ·
                refine ⟨4167728490964404232183459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5556971321285872309577945 4167728490964404232183459)
                ·
                  refine ⟨6251592736446606348275189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167728490964404232183459 6251592736446606348275189)
                  ·
                    refine ⟨586086819041869345150799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6251592736446606348275189 586086819041869345150799)
                    ·
                      rfl

theorem cell23_3424200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_3424200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424200 prefixEnd_3424200 := by exact prefixLift 3424200
  have htrace : WordTrace (prefixWord ++ tailWord_3424200) baseStart_3424200 baseEnd_3424200 := by
    simpa [prefixWord, tailWord_3424200, baseEnd_3424200] using wordTrace_append hprefix tailTrace_3424200
  have hstable : (prefixWord ++ tailWord_3424200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424200).length < 2 ^ (prefixWord ++ tailWord_3424200).sum := by decide
  have hdescent : baseEnd_3424200 < baseStart_3424200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424213 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3424213 : Nat := 118140960795 + 3424213 * 2 ^ 59
def prefixEnd_3424213 : Nat := 4983230072969 + 3 ^ 40 * 3424213 * 2
def baseEnd_3424213 : Nat := 586089044124705494863279

theorem tailTrace_3424213 : CollatzResearch.WordTrace tailWord_3424213 prefixEnd_3424213 586089044124705494863279 := by
  unfold tailWord_3424213
  simp only [CollatzResearch.WordTrace]
  refine ⟨124891308343668584866485293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83260872229112389910990195 124891308343668584866485293)
  ·
    refine ⟨46834240628875719324931985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124891308343668584866485293 46834240628875719324931985)
    ·
      refine ⟨35125680471656789493698989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46834240628875719324931985 35125680471656789493698989)
      ·
        refine ⟨13172130176871296060137121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35125680471656789493698989 13172130176871296060137121)
        ·
          refine ⟨9879097632653472045102841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13172130176871296060137121 9879097632653472045102841)
          ·
            refine ⟨7409323224490104033827131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9879097632653472045102841 7409323224490104033827131)
            ·
              refine ⟨11113984836735156050740697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409323224490104033827131 11113984836735156050740697)
              ·
                refine ⟨8335488627551367038055523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11113984836735156050740697 8335488627551367038055523)
                ·
                  refine ⟨12503232941327050557083285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8335488627551367038055523 12503232941327050557083285)
                  ·
                    refine ⟨586089044124705494863279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12503232941327050557083285 586089044124705494863279)
                    ·
                      rfl

theorem cell23_3424213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3424213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424213 prefixEnd_3424213 := by exact prefixLift 3424213
  have htrace : WordTrace (prefixWord ++ tailWord_3424213) baseStart_3424213 baseEnd_3424213 := by
    simpa [prefixWord, tailWord_3424213, baseEnd_3424213] using wordTrace_append hprefix tailTrace_3424213
  have hstable : (prefixWord ++ tailWord_3424213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424213).length < 2 ^ (prefixWord ++ tailWord_3424213).sum := by decide
  have hdescent : baseEnd_3424213 < baseStart_3424213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424223 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_3424223 : Nat := 118140960795 + 3424223 * 2 ^ 59
def prefixEnd_3424223 : Nat := 4983230072969 + 3 ^ 40 * 3424223 * 2
def baseEnd_3424223 : Nat := 1758272267180661445464791

theorem tailTrace_3424223 : CollatzResearch.WordTrace tailWord_3424223 prefixEnd_3424223 1758272267180661445464791 := by
  unfold tailWord_3424223
  simp only [CollatzResearch.WordTrace]
  refine ⟨124891673073632356574349323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83261115382421571049566215 124891673073632356574349323)
  ·
    refine ⟨187337509610448534861523985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124891673073632356574349323 187337509610448534861523985)
    ·
      refine ⟨140503132207836401146142989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187337509610448534861523985 140503132207836401146142989)
      ·
        refine ⟨52688674577938650429803621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140503132207836401146142989 52688674577938650429803621)
        ·
          refine ⟨9879126483363496955588179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52688674577938650429803621 9879126483363496955588179)
          ·
            refine ⟨14818689725045245433382269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879126483363496955588179 14818689725045245433382269)
            ·
              refine ⟨5557008646891967037518351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14818689725045245433382269 5557008646891967037518351)
              ·
                refine ⟨8335512970337950556277527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557008646891967037518351 8335512970337950556277527)
                ·
                  refine ⟨12503269455506925834416291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8335512970337950556277527 12503269455506925834416291)
                  ·
                    refine ⟨18754904183260388751624437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12503269455506925834416291 18754904183260388751624437)
                    ·
                      refine ⟨1758272267180661445464791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18754904183260388751624437 1758272267180661445464791)
                      ·
                        rfl

theorem cell23_3424223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_3424223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424223 prefixEnd_3424223 := by exact prefixLift 3424223
  have htrace : WordTrace (prefixWord ++ tailWord_3424223) baseStart_3424223 baseEnd_3424223 := by
    simpa [prefixWord, tailWord_3424223, baseEnd_3424223] using wordTrace_append hprefix tailTrace_3424223
  have hstable : (prefixWord ++ tailWord_3424223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424223).length < 2 ^ (prefixWord ++ tailWord_3424223).sum := by decide
  have hdescent : baseEnd_3424223 < baseStart_3424223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424231 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3424231 : Nat := 118140960795 + 3424231 * 2 ^ 59
def prefixEnd_3424231 : Nat := 4983230072969 + 3 ^ 40 * 3424231 * 2
def baseEnd_3424231 : Nat := 1758276375025897414164755

theorem tailTrace_3424231 : CollatzResearch.WordTrace tailWord_3424231 prefixEnd_3424231 1758276375025897414164755 := by
  unfold tailWord_3424231
  simp only [CollatzResearch.WordTrace]
  refine ⟨124891964857603373940640547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83261309905068915960427031 124891964857603373940640547)
  ·
    refine ⟨187337947286405060910960821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124891964857603373940640547 187337947286405060910960821)
    ·
      refine ⟨17562932558100474460402577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187337947286405060910960821 17562932558100474460402577)
      ·
        refine ⟨13172199418575355845301933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17562932558100474460402577 13172199418575355845301933)
        ·
          refine ⟨4939574781965758441988225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13172199418575355845301933 4939574781965758441988225)
          ·
            refine ⟨3704681086474318831491169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4939574781965758441988225 3704681086474318831491169)
            ·
              refine ⟨2778510814855739123618377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704681086474318831491169 2778510814855739123618377)
              ·
                refine ⟨2083883111141804342713783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778510814855739123618377 2083883111141804342713783)
                ·
                  refine ⟨3125824666712706514070675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083883111141804342713783 3125824666712706514070675)
                  ·
                    refine ⟨4688737000069059771106013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125824666712706514070675 4688737000069059771106013)
                    ·
                      refine ⟨1758276375025897414164755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688737000069059771106013 1758276375025897414164755)
                      ·
                        rfl

theorem cell23_3424231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3424231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424231 prefixEnd_3424231 := by exact prefixLift 3424231
  have htrace : WordTrace (prefixWord ++ tailWord_3424231) baseStart_3424231 baseEnd_3424231 := by
    simpa [prefixWord, tailWord_3424231, baseEnd_3424231] using wordTrace_append hprefix tailTrace_3424231
  have hstable : (prefixWord ++ tailWord_3424231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424231).length < 2 ^ (prefixWord ++ tailWord_3424231).sum := by decide
  have hdescent : baseEnd_3424231 < baseStart_3424231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424253 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_3424253 : Nat := 118140960795 + 3424253 * 2 ^ 59
def prefixEnd_3424253 : Nat := 4983230072969 + 3 ^ 40 * 3424253 * 2
def baseEnd_3424253 : Nat := 1758287671600296328089653

theorem tailTrace_3424253 : CollatzResearch.WordTrace tailWord_3424253 prefixEnd_3424253 1758287671600296328089653 := by
  unfold tailWord_3424253
  simp only [CollatzResearch.WordTrace]
  refine ⟨124892767263523671697941413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83261844842349114465294275 124892767263523671697941413)
  ·
    refine ⟨23417393861910688443364015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124892767263523671697941413 23417393861910688443364015)
    ·
      refine ⟨35126090792866032665046023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23417393861910688443364015 35126090792866032665046023)
      ·
        refine ⟨52689136189299048997569035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35126090792866032665046023 52689136189299048997569035)
        ·
          refine ⟨79033704283948573496353553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52689136189299048997569035 79033704283948573496353553)
          ·
            refine ⟨59275278212961430122265165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79033704283948573496353553 59275278212961430122265165)
            ·
              refine ⟨22228229329860536295849437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59275278212961430122265165 22228229329860536295849437)
              ·
                refine ⟨8335585998697701110943539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22228229329860536295849437 8335585998697701110943539)
                ·
                  refine ⟨12503378998046551666415309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8335585998697701110943539 12503378998046551666415309)
                  ·
                    refine ⟨4688767124267456874905741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12503378998046551666415309 4688767124267456874905741)
                    ·
                      refine ⟨1758287671600296328089653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688767124267456874905741 1758287671600296328089653)
                      ·
                        rfl

theorem cell23_3424253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_3424253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424253 prefixEnd_3424253 := by exact prefixLift 3424253
  have htrace : WordTrace (prefixWord ++ tailWord_3424253) baseStart_3424253 baseEnd_3424253 := by
    simpa [prefixWord, tailWord_3424253, baseEnd_3424253] using wordTrace_append hprefix tailTrace_3424253
  have hstable : (prefixWord ++ tailWord_3424253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424253).length < 2 ^ (prefixWord ++ tailWord_3424253).sum := by decide
  have hdescent : baseEnd_3424253 < baseStart_3424253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424254 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3424254 : Nat := 118140960795 + 3424254 * 2 ^ 59
def prefixEnd_3424254 : Nat := 4983230072969 + 3 ^ 40 * 3424254 * 2
def baseEnd_3424254 : Nat := 1758288185080950824177149

theorem tailTrace_3424254 : CollatzResearch.WordTrace tailWord_3424254 prefixEnd_3424254 1758288185080950824177149 := by
  unfold tailWord_3424254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611600467065006108590977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83261869157680032579151877 15611600467065006108590977)
  ·
    refine ⟨11708700350298754581443233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15611600467065006108590977 11708700350298754581443233)
    ·
      refine ⟨8781525262724065936082425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11708700350298754581443233 8781525262724065936082425)
      ·
        refine ⟨6586143947043049452061819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8781525262724065936082425 6586143947043049452061819)
        ·
          refine ⟨9879215920564574178092729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586143947043049452061819 9879215920564574178092729)
          ·
            refine ⟨7409411940423430633569547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9879215920564574178092729 7409411940423430633569547)
            ·
              refine ⟨11114117910635145950354321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409411940423430633569547 11114117910635145950354321)
              ·
                refine ⟨8335588432976359462765741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11114117910635145950354321 8335588432976359462765741)
                ·
                  refine ⟨3125845662366134798537153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8335588432976359462765741 3125845662366134798537153)
                  ·
                    refine ⟨2344384246774601098902865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3125845662366134798537153 2344384246774601098902865)
                    ·
                      refine ⟨1758288185080950824177149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344384246774601098902865 1758288185080950824177149)
                      ·
                        rfl

theorem cell23_3424254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3424254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424254 prefixEnd_3424254 := by exact prefixLift 3424254
  have htrace : WordTrace (prefixWord ++ tailWord_3424254) baseStart_3424254 baseEnd_3424254 := by
    simpa [prefixWord, tailWord_3424254, baseEnd_3424254] using wordTrace_append hprefix tailTrace_3424254
  have hstable : (prefixWord ++ tailWord_3424254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424254).length < 2 ^ (prefixWord ++ tailWord_3424254).sum := by decide
  have hdescent : baseEnd_3424254 < baseStart_3424254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424270 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3424270 : Nat := 118140960795 + 3424270 * 2 ^ 59
def prefixEnd_3424270 : Nat := 4983230072969 + 3 ^ 40 * 3424270 * 2
def baseEnd_3424270 : Nat := 1758296400771422761577075

theorem tailTrace_3424270 : CollatzResearch.WordTrace tailWord_3424270 prefixEnd_3424270 1758296400771422761577075 := by
  unfold tailWord_3424270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611673413057760450163783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83262258202974722400873509 15611673413057760450163783)
  ·
    refine ⟨23417510119586640675245675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15611673413057760450163783 23417510119586640675245675)
    ·
      refine ⟨35126265179379961012868513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23417510119586640675245675 35126265179379961012868513)
      ·
        refine ⟨26344698884534970759651385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35126265179379961012868513 26344698884534970759651385)
        ·
          refine ⟨19758524163401228069738539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26344698884534970759651385 19758524163401228069738539)
          ·
            refine ⟨29637786245101842104607809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19758524163401228069738539 29637786245101842104607809)
            ·
              refine ⟨22228339683826381578455857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29637786245101842104607809 22228339683826381578455857)
              ·
                refine ⟨16671254762869786183841893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22228339683826381578455857 16671254762869786183841893)
                ·
                  refine ⟨3125860268038084909470355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16671254762869786183841893 3125860268038084909470355)
                  ·
                    refine ⟨4688790402057127364205533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125860268038084909470355 4688790402057127364205533)
                    ·
                      refine ⟨1758296400771422761577075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688790402057127364205533 1758296400771422761577075)
                      ·
                        rfl

theorem cell23_3424270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3424270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424270 prefixEnd_3424270 := by exact prefixLift 3424270
  have htrace : WordTrace (prefixWord ++ tailWord_3424270) baseStart_3424270 baseEnd_3424270 := by
    simpa [prefixWord, tailWord_3424270, baseEnd_3424270] using wordTrace_append hprefix tailTrace_3424270
  have hstable : (prefixWord ++ tailWord_3424270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424270).length < 2 ^ (prefixWord ++ tailWord_3424270).sum := by decide
  have hdescent : baseEnd_3424270 < baseStart_3424270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424336 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_3424336 : Nat := 118140960795 + 3424336 * 2 ^ 59
def prefixEnd_3424336 : Nat := 4983230072969 + 3 ^ 40 * 3424336 * 2
def baseEnd_3424336 : Nat := 1758330290494619503351771

theorem tailTrace_3424336 : CollatzResearch.WordTrace tailWord_3424336 prefixEnd_3424336 1758330290494619503351771 := by
  unfold tailWord_3424336
  simp only [CollatzResearch.WordTrace]
  refine ⟨62447897261111488436606431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83263863014815317915475241 62447897261111488436606431)
  ·
    refine ⟨93671845891667232654909647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62447897261111488436606431 93671845891667232654909647)
    ·
      refine ⟨140507768837500848982364471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93671845891667232654909647 140507768837500848982364471)
      ·
        refine ⟨210761653256251273473546707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140507768837500848982364471 210761653256251273473546707)
        ·
          refine ⟨316142479884376910210320061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210761653256251273473546707 316142479884376910210320061)
          ·
            refine ⟨118553429956641341328870023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316142479884376910210320061 118553429956641341328870023)
            ·
              refine ⟨177830144934962011993305035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118553429956641341328870023 177830144934962011993305035)
              ·
                refine ⟨266745217402443017989957553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177830144934962011993305035 266745217402443017989957553)
                ·
                  refine ⟨200058913051832263492468165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266745217402443017989957553 200058913051832263492468165)
                  ·
                    refine ⟨37511046197218549404837781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200058913051832263492468165 37511046197218549404837781)
                    ·
                      refine ⟨1758330290494619503351771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37511046197218549404837781 1758330290494619503351771)
                      ·
                        rfl

theorem cell23_3424336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_3424336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424336 prefixEnd_3424336 := by exact prefixLift 3424336
  have htrace : WordTrace (prefixWord ++ tailWord_3424336) baseStart_3424336 baseEnd_3424336 := by
    simpa [prefixWord, tailWord_3424336, baseEnd_3424336] using wordTrace_append hprefix tailTrace_3424336
  have hstable : (prefixWord ++ tailWord_3424336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424336).length < 2 ^ (prefixWord ++ tailWord_3424336).sum := by decide
  have hdescent : baseEnd_3424336 < baseStart_3424336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424343 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_3424343 : Nat := 118140960795 + 3424343 * 2 ^ 59
def prefixEnd_3424343 : Nat := 4983230072969 + 3 ^ 40 * 3424343 * 2
def baseEnd_3424343 : Nat := 1758333884859200975964239

theorem tailTrace_3424343 : CollatzResearch.WordTrace tailWord_3424343 prefixEnd_3424343 1758333884859200975964239 := by
  unfold tailWord_3424343
  simp only [CollatzResearch.WordTrace]
  refine ⟨124896049833197617068717683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83264033222131744712478455 124896049833197617068717683)
  ·
    refine ⟨187344074749796425603076525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124896049833197617068717683 187344074749796425603076525)
    ·
      refine ⟨70254028031173659601153697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187344074749796425603076525 70254028031173659601153697)
      ·
        refine ⟨52690521023380244700865273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70254028031173659601153697 52690521023380244700865273)
        ·
          refine ⟨39517890767535183525648955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52690521023380244700865273 39517890767535183525648955)
          ·
            refine ⟨59276836151302775288473433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39517890767535183525648955 59276836151302775288473433)
            ·
              refine ⟨44457627113477081466355075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59276836151302775288473433 44457627113477081466355075)
              ·
                refine ⟨66686440670215622199532613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44457627113477081466355075 66686440670215622199532613)
                ·
                  refine ⟨12503707625665429162412365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66686440670215622199532613 12503707625665429162412365)
                  ·
                    refine ⟨4688890359624535935904637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12503707625665429162412365 4688890359624535935904637)
                    ·
                      refine ⟨1758333884859200975964239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688890359624535935904637 1758333884859200975964239)
                      ·
                        rfl

theorem cell23_3424343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_3424343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424343 prefixEnd_3424343 := by exact prefixLift 3424343
  have htrace : WordTrace (prefixWord ++ tailWord_3424343) baseStart_3424343 baseEnd_3424343 := by
    simpa [prefixWord, tailWord_3424343, baseEnd_3424343] using wordTrace_append hprefix tailTrace_3424343
  have hstable : (prefixWord ++ tailWord_3424343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424343).length < 2 ^ (prefixWord ++ tailWord_3424343).sum := by decide
  have hdescent : baseEnd_3424343 < baseStart_3424343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424380 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_3424380 : Nat := 118140960795 + 3424380 * 2 ^ 59
def prefixEnd_3424380 : Nat := 4983230072969 + 3 ^ 40 * 3424380 * 2
def baseEnd_3424380 : Nat := 586117627881139110400523

theorem tailTrace_3424380 : CollatzResearch.WordTrace tailWord_3424380 prefixEnd_3424380 586117627881139110400523 := by
  unfold tailWord_3424380
  simp only [CollatzResearch.WordTrace]
  refine ⟨62448699667031786193907297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83264932889375714925209729 62448699667031786193907297)
  ·
    refine ⟨46836524750273839645430473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62448699667031786193907297 46836524750273839645430473)
    ·
      refine ⟨35127393562705379734072855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46836524750273839645430473 35127393562705379734072855)
      ·
        refine ⟨52691090344058069601109283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35127393562705379734072855 52691090344058069601109283)
        ·
          refine ⟨79036635516087104401663925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52691090344058069601109283 79036635516087104401663925)
          ·
            refine ⟨7409684579633166037655993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79036635516087104401663925 7409684579633166037655993)
            ·
              refine ⟨5557263434724874528241995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409684579633166037655993 5557263434724874528241995)
              ·
                refine ⟨8335895152087311792362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557263434724874528241995 8335895152087311792362993)
                ·
                  refine ⟨6251921364065483844272245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8335895152087311792362993 6251921364065483844272245)
                  ·
                    refine ⟨586117627881139110400523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6251921364065483844272245 586117627881139110400523)
                    ·
                      rfl

theorem cell23_3424380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_3424380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424380 prefixEnd_3424380 := by exact prefixLift 3424380
  have htrace : WordTrace (prefixWord ++ tailWord_3424380) baseStart_3424380 baseEnd_3424380 := by
    simpa [prefixWord, tailWord_3424380, baseEnd_3424380] using wordTrace_append hprefix tailTrace_3424380
  have hstable : (prefixWord ++ tailWord_3424380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424380).length < 2 ^ (prefixWord ++ tailWord_3424380).sum := by decide
  have hdescent : baseEnd_3424380 < baseStart_3424380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424400 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2]
def baseStart_3424400 : Nat := 118140960795 + 3424400 * 2 ^ 59
def prefixEnd_3424400 : Nat := 4983230072969 + 3 ^ 40 * 3424400 * 2
def baseEnd_3424400 : Nat := 1758363153256507252951477

theorem tailTrace_3424400 : CollatzResearch.WordTrace tailWord_3424400 prefixEnd_3424400 1758363153256507252951477 := by
  unfold tailWord_3424400
  simp only [CollatzResearch.WordTrace]
  refine ⟨62449064396995557901771327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83265419195994077202361769 62449064396995557901771327)
  ·
    refine ⟨93673596595493336852656991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62449064396995557901771327 93673596595493336852656991)
    ·
      refine ⟨140510394893240005278985487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93673596595493336852656991 140510394893240005278985487)
      ·
        refine ⟨210765592339860007918478231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140510394893240005278985487 210765592339860007918478231)
        ·
          refine ⟨316148388509790011877717347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210765592339860007918478231 316148388509790011877717347)
          ·
            refine ⟨474222582764685017816576021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316148388509790011877717347 474222582764685017816576021)
            ·
              refine ⟨22229183567094610210152001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 474222582764685017816576021 22229183567094610210152001)
              ·
                refine ⟨16671887675320957657614001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22229183567094610210152001 16671887675320957657614001)
                ·
                  refine ⟨12503915756490718243210501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16671887675320957657614001 12503915756490718243210501)
                  ·
                    refine ⟨2344484204342009670601969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12503915756490718243210501 2344484204342009670601969)
                    ·
                      refine ⟨1758363153256507252951477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344484204342009670601969 1758363153256507252951477)
                      ·
                        rfl

theorem cell23_3424400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2].length) (baseStart_3424400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424400 prefixEnd_3424400 := by exact prefixLift 3424400
  have htrace : WordTrace (prefixWord ++ tailWord_3424400) baseStart_3424400 baseEnd_3424400 := by
    simpa [prefixWord, tailWord_3424400, baseEnd_3424400] using wordTrace_append hprefix tailTrace_3424400
  have hstable : (prefixWord ++ tailWord_3424400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424400).length < 2 ^ (prefixWord ++ tailWord_3424400).sum := by decide
  have hdescent : baseEnd_3424400 < baseStart_3424400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424403 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3]
def baseStart_3424403 : Nat := 118140960795 + 3424403 * 2 ^ 59
def prefixEnd_3424403 : Nat := 4983230072969 + 3 ^ 40 * 3424403 * 2
def baseEnd_3424403 : Nat := 1758364693698470741213963

theorem tailTrace_3424403 : CollatzResearch.WordTrace tailWord_3424403 prefixEnd_3424403 1758364693698470741213963 := by
  unfold tailWord_3424403
  simp only [CollatzResearch.WordTrace]
  refine ⟨124898238212980247315901863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83265492141986831543934575 124898238212980247315901863)
  ·
    refine ⟨187347357319470370973852795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124898238212980247315901863 187347357319470370973852795)
    ·
      refine ⟨281021035979205556460779193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187347357319470370973852795 281021035979205556460779193)
      ·
        refine ⟨210765776984404167345584395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281021035979205556460779193 210765776984404167345584395)
        ·
          refine ⟨316148665476606251018376593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210765776984404167345584395 316148665476606251018376593)
          ·
            refine ⟨237111499107454688263782445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316148665476606251018376593 237111499107454688263782445)
            ·
              refine ⟨88916812165295508098918417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237111499107454688263782445 88916812165295508098918417)
              ·
                refine ⟨66687609123971631074188813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88916812165295508098918417 66687609123971631074188813)
                ·
                  refine ⟨25007853421489361652820805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66687609123971631074188813 25007853421489361652820805)
                  ·
                    refine ⟨4688972516529255309903901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25007853421489361652820805 4688972516529255309903901)
                    ·
                      refine ⟨1758364693698470741213963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4688972516529255309903901 1758364693698470741213963)
                      ·
                        rfl

theorem cell23_3424403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_3424403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424403 prefixEnd_3424403 := by exact prefixLift 3424403
  have htrace : WordTrace (prefixWord ++ tailWord_3424403) baseStart_3424403 baseEnd_3424403 := by
    simpa [prefixWord, tailWord_3424403, baseEnd_3424403] using wordTrace_append hprefix tailTrace_3424403
  have hstable : (prefixWord ++ tailWord_3424403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424403).length < 2 ^ (prefixWord ++ tailWord_3424403).sum := by decide
  have hdescent : baseEnd_3424403 < baseStart_3424403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424417 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3424417 : Nat := 118140960795 + 3424417 * 2 ^ 59
def prefixEnd_3424417 : Nat := 4983230072969 + 3 ^ 40 * 3424417 * 2
def baseEnd_3424417 : Nat := 1758371882427633686438899

theorem tailTrace_3424417 : CollatzResearch.WordTrace tailWord_3424417 prefixEnd_3424417 1758371882427633686438899 := by
  unfold tailWord_3424417
  simp only [CollatzResearch.WordTrace]
  refine ⟨124898748834929527706911505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83265832556619685137941003 124898748834929527706911505)
  ·
    refine ⟨93674061626197145780183629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124898748834929527706911505 93674061626197145780183629)
    ·
      refine ⟨35127773109823929667568861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93674061626197145780183629 35127773109823929667568861)
      ·
        refine ⟨13172914916183973625338323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35127773109823929667568861 13172914916183973625338323)
        ·
          refine ⟨19759372374275960438007485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13172914916183973625338323 19759372374275960438007485)
          ·
            refine ⟨7409764640353485164252807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19759372374275960438007485 7409764640353485164252807)
            ·
              refine ⟨11114646960530227746379211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409764640353485164252807 11114646960530227746379211)
              ·
                refine ⟨16671970440795341619568817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114646960530227746379211 16671970440795341619568817)
                ·
                  refine ⟨12503977830596506214676613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16671970440795341619568817 12503977830596506214676613)
                  ·
                    refine ⟨2344495843236844915251865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12503977830596506214676613 2344495843236844915251865)
                    ·
                      refine ⟨1758371882427633686438899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344495843236844915251865 1758371882427633686438899)
                      ·
                        rfl

theorem cell23_3424417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3424417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424417 prefixEnd_3424417 := by exact prefixLift 3424417
  have htrace : WordTrace (prefixWord ++ tailWord_3424417) baseStart_3424417 baseEnd_3424417 := by
    simpa [prefixWord, tailWord_3424417, baseEnd_3424417] using wordTrace_append hprefix tailTrace_3424417
  have hstable : (prefixWord ++ tailWord_3424417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424417).length < 2 ^ (prefixWord ++ tailWord_3424417).sum := by decide
  have hdescent : baseEnd_3424417 < baseStart_3424417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424487 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3424487 : Nat := 118140960795 + 3424487 * 2 ^ 59
def prefixEnd_3424487 : Nat := 4983230072969 + 3 ^ 40 * 3424487 * 2
def baseEnd_3424487 : Nat := 586135942024482804187859

theorem tailTrace_3424487 : CollatzResearch.WordTrace tailWord_3424487 prefixEnd_3424487 586135942024482804187859 := by
  unfold tailWord_3424487
  simp only [CollatzResearch.WordTrace]
  refine ⟨124901301944675929661959715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83267534629783953107973143 124901301944675929661959715)
  ·
    refine ⟨187351952917013894492939573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124901301944675929661959715 187351952917013894492939573)
    ·
      refine ⟨17564245585970052608713085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187351952917013894492939573 17564245585970052608713085)
      ·
        refine ⟨6586592094738769728267407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17564245585970052608713085 6586592094738769728267407)
        ·
          refine ⟨9879888142108154592401111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586592094738769728267407 9879888142108154592401111)
          ·
            refine ⟨14819832213162231888601667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879888142108154592401111 14819832213162231888601667)
            ·
              refine ⟨22229748319743347832902501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14819832213162231888601667 22229748319743347832902501)
              ·
                refine ⟨4168077809951877718669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22229748319743347832902501 4168077809951877718669219)
                ·
                  refine ⟨6252116714927816578003829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168077809951877718669219 6252116714927816578003829)
                  ·
                    refine ⟨586135942024482804187859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6252116714927816578003829 586135942024482804187859)
                    ·
                      rfl

theorem cell23_3424487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3424487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424487 prefixEnd_3424487 := by exact prefixLift 3424487
  have htrace : WordTrace (prefixWord ++ tailWord_3424487) baseStart_3424487 baseEnd_3424487 := by
    simpa [prefixWord, tailWord_3424487, baseEnd_3424487] using wordTrace_append hprefix tailTrace_3424487
  have hstable : (prefixWord ++ tailWord_3424487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424487).length < 2 ^ (prefixWord ++ tailWord_3424487).sum := by decide
  have hdescent : baseEnd_3424487 < baseStart_3424487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424503 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_3424503 : Nat := 118140960795 + 3424503 * 2 ^ 59
def prefixEnd_3424503 : Nat := 4983230072969 + 3 ^ 40 * 3424503 * 2
def baseEnd_3424503 : Nat := 1758416041763920349963503

theorem tailTrace_3424503 : CollatzResearch.WordTrace tailWord_3424503 prefixEnd_3424503 1758416041763920349963503 := by
  unfold tailWord_3424503
  simp only [CollatzResearch.WordTrace]
  refine ⟨124901885512617964394542163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83267923675078642929694775 124901885512617964394542163)
  ·
    refine ⟨187352828268926946591813245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124901885512617964394542163 187352828268926946591813245)
    ·
      refine ⟨70257310600847604971929967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187352828268926946591813245 70257310600847604971929967)
      ·
        refine ⟨105385965901271407457894951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70257310600847604971929967 105385965901271407457894951)
        ·
          refine ⟨158078948851907111186842427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105385965901271407457894951 158078948851907111186842427)
          ·
            refine ⟨237118423277860666780263641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158078948851907111186842427 237118423277860666780263641)
            ·
              refine ⟨177838817458395500085197731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237118423277860666780263641 177838817458395500085197731)
              ·
                refine ⟨266758226187593250127796597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177838817458395500085197731 266758226187593250127796597)
                ·
                  refine ⟨25008583705086867199480931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266758226187593250127796597 25008583705086867199480931)
                  ·
                    refine ⟨37512875557630300799221397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25008583705086867199480931 37512875557630300799221397)
                    ·
                      refine ⟨1758416041763920349963503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37512875557630300799221397 1758416041763920349963503)
                      ·
                        rfl

theorem cell23_3424503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_3424503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424503 prefixEnd_3424503 := by exact prefixLift 3424503
  have htrace : WordTrace (prefixWord ++ tailWord_3424503) baseStart_3424503 baseEnd_3424503 := by
    simpa [prefixWord, tailWord_3424503, baseEnd_3424503] using wordTrace_append hprefix tailTrace_3424503
  have hstable : (prefixWord ++ tailWord_3424503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424503).length < 2 ^ (prefixWord ++ tailWord_3424503).sum := by decide
  have hdescent : baseEnd_3424503 < baseStart_3424503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424520 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3424520 : Nat := 118140960795 + 3424520 * 2 ^ 59
def prefixEnd_3424520 : Nat := 4983230072969 + 3 ^ 40 * 3424520 * 2
def baseEnd_3424520 : Nat := 1758424770935046783450925

theorem tailTrace_3424520 : CollatzResearch.WordTrace tailWord_3424520 prefixEnd_3424520 1758424770935046783450925 := by
  unfold tailWord_3424520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62451252776778188148955507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83268337035704250865274009 62451252776778188148955507)
  ·
    refine ⟨93676879165167282223433261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62451252776778188148955507 93676879165167282223433261)
    ·
      refine ⟨35128829686937730833787473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93676879165167282223433261 35128829686937730833787473)
      ·
        refine ⟨26346622265203298125340605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35128829686937730833787473 26346622265203298125340605)
        ·
          refine ⟨9879983349451236797002727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26346622265203298125340605 9879983349451236797002727)
          ·
            refine ⟨14819975024176855195504091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879983349451236797002727 14819975024176855195504091)
            ·
              refine ⟨22229962536265282793256137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14819975024176855195504091 22229962536265282793256137)
              ·
                refine ⟨16672471902198962094942103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22229962536265282793256137 16672471902198962094942103)
                ·
                  refine ⟨25008707853298443142413155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16672471902198962094942103 25008707853298443142413155)
                  ·
                    refine ⟨37513061779947664713619733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25008707853298443142413155 37513061779947664713619733)
                    ·
                      refine ⟨1758424770935046783450925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37513061779947664713619733 1758424770935046783450925)
                      ·
                        rfl

theorem cell23_3424520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3424520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424520 prefixEnd_3424520 := by exact prefixLift 3424520
  have htrace : WordTrace (prefixWord ++ tailWord_3424520) baseStart_3424520 baseEnd_3424520 := by
    simpa [prefixWord, tailWord_3424520, baseEnd_3424520] using wordTrace_append hprefix tailTrace_3424520
  have hstable : (prefixWord ++ tailWord_3424520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424520).length < 2 ^ (prefixWord ++ tailWord_3424520).sum := by decide
  have hdescent : baseEnd_3424520 < baseStart_3424520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424541 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3424541 : Nat := 118140960795 + 3424541 * 2 ^ 59
def prefixEnd_3424541 : Nat := 4983230072969 + 3 ^ 40 * 3424541 * 2
def baseEnd_3424541 : Nat := 1758435554028791201288329

theorem tailTrace_3424541 : CollatzResearch.WordTrace tailWord_3424541 prefixEnd_3424541 1758435554028791201288329 := by
  unfold tailWord_3424541
  simp only [CollatzResearch.WordTrace]
  refine ⟨124903271486480296884425477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83268847657653531256283651 124903271486480296884425477)
  ·
    refine ⟨23419363403715055665829777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124903271486480296884425477 23419363403715055665829777)
    ·
      refine ⟨17564522552786291749372333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23419363403715055665829777 17564522552786291749372333)
      ·
        refine ⟨6586695957294859406014625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17564522552786291749372333 6586695957294859406014625)
        ·
          refine ⟨4940021967971144554510969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6586695957294859406014625 4940021967971144554510969)
          ·
            refine ⟨3705016475978358415883227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4940021967971144554510969 3705016475978358415883227)
            ·
              refine ⟨5557524713967537623824841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705016475978358415883227 5557524713967537623824841)
              ·
                refine ⟨4168143535475653217868631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557524713967537623824841 4168143535475653217868631)
                ·
                  refine ⟨6252215303213479826802947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168143535475653217868631 6252215303213479826802947)
                  ·
                    refine ⟨9378322954820219740204421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252215303213479826802947 9378322954820219740204421)
                    ·
                      refine ⟨1758435554028791201288329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9378322954820219740204421 1758435554028791201288329)
                      ·
                        rfl

theorem cell23_3424541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3424541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424541 prefixEnd_3424541 := by exact prefixLift 3424541
  have htrace : WordTrace (prefixWord ++ tailWord_3424541) baseStart_3424541 baseEnd_3424541 := by
    simpa [prefixWord, tailWord_3424541, baseEnd_3424541] using wordTrace_append hprefix tailTrace_3424541
  have hstable : (prefixWord ++ tailWord_3424541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424541).length < 2 ^ (prefixWord ++ tailWord_3424541).sum := by decide
  have hdescent : baseEnd_3424541 < baseStart_3424541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424544 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3424544 : Nat := 118140960795 + 3424544 * 2 ^ 59
def prefixEnd_3424544 : Nat := 4983230072969 + 3 ^ 40 * 3424544 * 2
def baseEnd_3424544 : Nat := 1758437094470754689550815

theorem tailTrace_3424544 : CollatzResearch.WordTrace tailWord_3424544 prefixEnd_3424544 1758437094470754689550815 := by
  unfold tailWord_3424544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62451690452734714198392343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83268920603646285597856457 62451690452734714198392343)
  ·
    refine ⟨93677535679102071297588515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62451690452734714198392343 93677535679102071297588515)
    ·
      refine ⟨140516303518653106946382773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93677535679102071297588515 140516303518653106946382773)
      ·
        refine ⟨13173403454873728776223385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140516303518653106946382773 13173403454873728776223385)
        ·
          refine ⟨9880052591155296582167539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13173403454873728776223385 9880052591155296582167539)
          ·
            refine ⟨14820078886732944873251309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880052591155296582167539 14820078886732944873251309)
            ·
              refine ⟨5557529582524854327469241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14820078886732944873251309 5557529582524854327469241)
              ·
                refine ⟨4168147186893640745601931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557529582524854327469241 4168147186893640745601931)
                ·
                  refine ⟨6252220780340461118402897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168147186893640745601931 6252220780340461118402897)
                  ·
                    refine ⟨4689165585255345838802173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252220780340461118402897 4689165585255345838802173)
                    ·
                      refine ⟨1758437094470754689550815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689165585255345838802173 1758437094470754689550815)
                      ·
                        rfl

theorem cell23_3424544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3424544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424544 prefixEnd_3424544 := by exact prefixLift 3424544
  have htrace : WordTrace (prefixWord ++ tailWord_3424544) baseStart_3424544 baseEnd_3424544 := by
    simpa [prefixWord, tailWord_3424544, baseEnd_3424544] using wordTrace_append hprefix tailTrace_3424544
  have hstable : (prefixWord ++ tailWord_3424544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424544).length < 2 ^ (prefixWord ++ tailWord_3424544).sum := by decide
  have hdescent : baseEnd_3424544 < baseStart_3424544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424551 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3424551 : Nat := 118140960795 + 3424551 * 2 ^ 59
def prefixEnd_3424551 : Nat := 4983230072969 + 3 ^ 40 * 3424551 * 2
def baseEnd_3424551 : Nat := 586146896278445387387761

theorem tailTrace_3424551 : CollatzResearch.WordTrace tailWord_3424551 prefixEnd_3424551 586146896278445387387761 := by
  unfold tailWord_3424551
  simp only [CollatzResearch.WordTrace]
  refine ⟨124903636216444068592289507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83269090810962712394859671 124903636216444068592289507)
  ·
    refine ⟨187355454324666102888434261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124903636216444068592289507 187355454324666102888434261)
    ·
      refine ⟨2195571730367180893223839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 187355454324666102888434261 2195571730367180893223839)
      ·
        refine ⟨3293357595550771339835759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195571730367180893223839 3293357595550771339835759)
        ·
          refine ⟨4940036393326157009753639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293357595550771339835759 4940036393326157009753639)
          ·
            refine ⟨7410054589989235514630459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940036393326157009753639 7410054589989235514630459)
            ·
              refine ⟨11115081884983853271945689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410054589989235514630459 11115081884983853271945689)
              ·
                refine ⟨8336311413737889953959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11115081884983853271945689 8336311413737889953959267)
                ·
                  refine ⟨12504467120606834930938901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336311413737889953959267 12504467120606834930938901)
                  ·
                    refine ⟨586146896278445387387761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12504467120606834930938901 586146896278445387387761)
                    ·
                      rfl

theorem cell23_3424551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3424551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424551 prefixEnd_3424551 := by exact prefixLift 3424551
  have htrace : WordTrace (prefixWord ++ tailWord_3424551) baseStart_3424551 baseEnd_3424551 := by
    simpa [prefixWord, tailWord_3424551, baseEnd_3424551] using wordTrace_append hprefix tailTrace_3424551
  have hstable : (prefixWord ++ tailWord_3424551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424551).length < 2 ^ (prefixWord ++ tailWord_3424551).sum := by decide
  have hdescent : baseEnd_3424551 < baseStart_3424551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424554 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3424554 : Nat := 118140960795 + 3424554 * 2 ^ 59
def prefixEnd_3424554 : Nat := 4983230072969 + 3 ^ 40 * 3424554 * 2
def baseEnd_3424554 : Nat := 1758442229277299650425769

theorem tailTrace_3424554 : CollatzResearch.WordTrace tailWord_3424554 prefixEnd_3424554 1758442229277299650425769 := by
  unfold tailWord_3424554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225936408858300026162179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83269163756955466736432477 31225936408858300026162179)
  ·
    refine ⟨46838904613287450039243269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31225936408858300026162179 46838904613287450039243269)
    ·
      refine ⟨8782294614991396882358113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46838904613287450039243269 8782294614991396882358113)
      ·
        refine ⟨6586720961243547661768585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8782294614991396882358113 6586720961243547661768585)
        ·
          refine ⟨4940040720932660746326439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6586720961243547661768585 4940040720932660746326439)
          ·
            refine ⟨7410061081398991119489659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940040720932660746326439 7410061081398991119489659)
            ·
              refine ⟨11115091622098486679234489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410061081398991119489659 11115091622098486679234489)
              ·
                refine ⟨8336318716573865009425867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11115091622098486679234489 8336318716573865009425867)
                ·
                  refine ⟨12504478074860797514138801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336318716573865009425867 12504478074860797514138801)
                  ·
                    refine ⟨9378358556145598135604101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12504478074860797514138801 9378358556145598135604101)
                    ·
                      refine ⟨1758442229277299650425769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9378358556145598135604101 1758442229277299650425769)
                      ·
                        rfl

theorem cell23_3424554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3424554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424554 prefixEnd_3424554 := by exact prefixLift 3424554
  have htrace : WordTrace (prefixWord ++ tailWord_3424554) baseStart_3424554 baseEnd_3424554 := by
    simpa [prefixWord, tailWord_3424554, baseEnd_3424554] using wordTrace_append hprefix tailTrace_3424554
  have hstable : (prefixWord ++ tailWord_3424554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424554).length < 2 ^ (prefixWord ++ tailWord_3424554).sum := by decide
  have hdescent : baseEnd_3424554 < baseStart_3424554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424558 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3424558 : Nat := 118140960795 + 3424558 * 2 ^ 59
def prefixEnd_3424558 : Nat := 4983230072969 + 3 ^ 40 * 3424558 * 2
def baseEnd_3424558 : Nat := 1758444283199917634775751

theorem tailTrace_3424558 : CollatzResearch.WordTrace tailWord_3424558 prefixEnd_3424558 1758444283199917634775751 := by
  unfold tailWord_3424558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15612986440927338598474291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83269261018279139191862885 15612986440927338598474291)
  ·
    refine ⟨23419479661391007897711437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15612986440927338598474291 23419479661391007897711437)
    ·
      refine ⟨8782304873021627961641789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23419479661391007897711437 8782304873021627961641789)
      ·
        refine ⟨3293364327383110485615671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8782304873021627961641789 3293364327383110485615671)
        ·
          refine ⟨4940046491074665728423507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293364327383110485615671 4940046491074665728423507)
          ·
            refine ⟨7410069736611998592635261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940046491074665728423507 7410069736611998592635261)
            ·
              refine ⟨2778776151229499472238223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410069736611998592635261 2778776151229499472238223)
              ·
                refine ⟨4168164226844249208357335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778776151229499472238223 4168164226844249208357335)
                ·
                  refine ⟨6252246340266373812536003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168164226844249208357335 6252246340266373812536003)
                  ·
                    refine ⟨9378369510399560718804005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6252246340266373812536003 9378369510399560718804005)
                    ·
                      refine ⟨1758444283199917634775751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9378369510399560718804005 1758444283199917634775751)
                      ·
                        rfl

theorem cell23_3424558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3424558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424558 prefixEnd_3424558 := by exact prefixLift 3424558
  have htrace : WordTrace (prefixWord ++ tailWord_3424558) baseStart_3424558 baseEnd_3424558 := by
    simpa [prefixWord, tailWord_3424558, baseEnd_3424558] using wordTrace_append hprefix tailTrace_3424558
  have hstable : (prefixWord ++ tailWord_3424558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424558).length < 2 ^ (prefixWord ++ tailWord_3424558).sum := by decide
  have hdescent : baseEnd_3424558 < baseStart_3424558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424561 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_3424561 : Nat := 118140960795 + 3424561 * 2 ^ 59
def prefixEnd_3424561 : Nat := 4983230072969 + 3 ^ 40 * 3424561 * 2
def baseEnd_3424561 : Nat := 1758445823641881123038237

theorem tailTrace_3424561 : CollatzResearch.WordTrace tailWord_3424561 prefixEnd_3424561 1758445823641881123038237 := by
  unfold tailWord_3424561
  simp only [CollatzResearch.WordTrace]
  refine ⟨124904000946407840300153537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83269333964271893533435691 124904000946407840300153537)
  ·
    refine ⟨93678000709805880225115153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124904000946407840300153537 93678000709805880225115153)
    ·
      refine ⟨70258500532354410168836365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93678000709805880225115153 70258500532354410168836365)
      ·
        refine ⟨26346937699632903813313637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70258500532354410168836365 26346937699632903813313637)
        ·
          refine ⟨4940050818681169464996307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26346937699632903813313637 4940050818681169464996307)
          ·
            refine ⟨7410076228021754197494461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940050818681169464996307 7410076228021754197494461)
            ·
              refine ⟨2778778585508157824060423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410076228021754197494461 2778778585508157824060423)
              ·
                refine ⟨4168167878262236736090635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778778585508157824060423 4168167878262236736090635)
                ·
                  refine ⟨6252251817393355104135953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168167878262236736090635 6252251817393355104135953)
                  ·
                    refine ⟨4689188863045016328101965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252251817393355104135953 4689188863045016328101965)
                    ·
                      refine ⟨1758445823641881123038237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689188863045016328101965 1758445823641881123038237)
                      ·
                        rfl

theorem cell23_3424561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_3424561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424561 prefixEnd_3424561 := by exact prefixLift 3424561
  have htrace : WordTrace (prefixWord ++ tailWord_3424561) baseStart_3424561 baseEnd_3424561 := by
    simpa [prefixWord, tailWord_3424561, baseEnd_3424561] using wordTrace_append hprefix tailTrace_3424561
  have hstable : (prefixWord ++ tailWord_3424561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424561).length < 2 ^ (prefixWord ++ tailWord_3424561).sum := by decide
  have hdescent : baseEnd_3424561 < baseStart_3424561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424600 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3424600 : Nat := 118140960795 + 3424600 * 2 ^ 59
def prefixEnd_3424600 : Nat := 4983230072969 + 3 ^ 40 * 3424600 * 2
def baseEnd_3424600 : Nat := 1758465849387406470450557

theorem tailTrace_3424600 : CollatzResearch.WordTrace tailWord_3424600 prefixEnd_3424600 1758465849387406470450557 := by
  unfold tailWord_3424600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62452711696633274980411627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83270282262177699973882169 62452711696633274980411627)
  ·
    refine ⟨93679067544949912470617441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62452711696633274980411627 93679067544949912470617441)
    ·
      refine ⟨70259300658712434352963081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93679067544949912470617441 70259300658712434352963081)
      ·
        refine ⟨52694475494034325764722311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70259300658712434352963081 52694475494034325764722311)
        ·
          refine ⟨79041713241051488647083467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52694475494034325764722311 79041713241051488647083467)
          ·
            refine ⟨118562569861577232970625201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79041713241051488647083467 118562569861577232970625201)
            ·
              refine ⟨88921927396182924727968901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118562569861577232970625201 88921927396182924727968901)
              ·
                refine ⟨16672861386784298386494169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88921927396182924727968901 16672861386784298386494169)
                ·
                  refine ⟨12504646040088223789870627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16672861386784298386494169 12504646040088223789870627)
                  ·
                    refine ⟨18756969060132335684805941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12504646040088223789870627 18756969060132335684805941)
                    ·
                      refine ⟨1758465849387406470450557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18756969060132335684805941 1758465849387406470450557)
                      ·
                        rfl

theorem cell23_3424600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3424600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424600 prefixEnd_3424600 := by exact prefixLift 3424600
  have htrace : WordTrace (prefixWord ++ tailWord_3424600) baseStart_3424600 baseEnd_3424600 := by
    simpa [prefixWord, tailWord_3424600, baseEnd_3424600] using wordTrace_append hprefix tailTrace_3424600
  have hstable : (prefixWord ++ tailWord_3424600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424600).length < 2 ^ (prefixWord ++ tailWord_3424600).sum := by decide
  have hdescent : baseEnd_3424600 < baseStart_3424600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424618 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3424618 : Nat := 118140960795 + 3424618 * 2 ^ 59
def prefixEnd_3424618 : Nat := 4983230072969 + 3 ^ 40 * 3424618 * 2
def baseEnd_3424618 : Nat := 1758475092039187400025475

theorem tailTrace_3424618 : CollatzResearch.WordTrace tailWord_3424618 prefixEnd_3424618 1758475092039187400025475 := by
  unfold tailWord_3424618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31226519976800334758744627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83270719938134226023319005 31226519976800334758744627)
  ·
    refine ⟨46839779965200502138116941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31226519976800334758744627 46839779965200502138116941)
    ·
      refine ⟨17564917486950188301793853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46839779965200502138116941 17564917486950188301793853)
      ·
        refine ⟨6586844057606320613172695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17564917486950188301793853 6586844057606320613172695)
        ·
          refine ⟨9880266086409480919759043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586844057606320613172695 9880266086409480919759043)
          ·
            refine ⟨14820399129614221379638565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880266086409480919759043 14820399129614221379638565)
            ·
              refine ⟨2778824836802666508682231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14820399129614221379638565 2778824836802666508682231)
              ·
                refine ⟨4168237255203999763023347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778824836802666508682231 4168237255203999763023347)
                ·
                  refine ⟨6252355882805999644535021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168237255203999763023347 6252355882805999644535021)
                  ·
                    refine ⟨2344633456052249866700633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6252355882805999644535021 2344633456052249866700633)
                    ·
                      refine ⟨1758475092039187400025475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344633456052249866700633 1758475092039187400025475)
                      ·
                        rfl

theorem cell23_3424618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3424618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424618 prefixEnd_3424618 := by exact prefixLift 3424618
  have htrace : WordTrace (prefixWord ++ tailWord_3424618) baseStart_3424618 baseEnd_3424618 := by
    simpa [prefixWord, tailWord_3424618, baseEnd_3424618] using wordTrace_append hprefix tailTrace_3424618
  have hstable : (prefixWord ++ tailWord_3424618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424618).length < 2 ^ (prefixWord ++ tailWord_3424618).sum := by decide
  have hdescent : baseEnd_3424618 < baseStart_3424618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424637 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 7]
def baseStart_3424637 : Nat := 118140960795 + 3424637 * 2 ^ 59
def prefixEnd_3424637 : Nat := 4983230072969 + 3 ^ 40 * 3424637 * 2
def baseEnd_3424637 : Nat := 195387205352402536187543

theorem tailTrace_3424637 : CollatzResearch.WordTrace tailWord_3424637 prefixEnd_3424637 195387205352402536187543 := by
  unfold tailWord_3424637
  simp only [CollatzResearch.WordTrace]
  refine ⟨124906772894132505279920165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83271181929421670186613443 124906772894132505279920165)
  ·
    refine ⟨23420019917649844739985031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124906772894132505279920165 23420019917649844739985031)
    ·
      refine ⟨35130029876474767109977547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23420019917649844739985031 35130029876474767109977547)
      ·
        refine ⟨52695044814712150664966321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35130029876474767109977547 52695044814712150664966321)
        ·
          refine ⟨39521283611034112998724741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52695044814712150664966321 39521283611034112998724741)
          ·
            refine ⟨7410240677068896187260889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39521283611034112998724741 7410240677068896187260889)
            ·
              refine ⟨5557680507801672140445667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7410240677068896187260889 5557680507801672140445667)
              ·
                refine ⟨8336520761702508210668501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557680507801672140445667 8336520761702508210668501)
                ·
                  refine ⟨195387205352402536187543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8336520761702508210668501 195387205352402536187543)
                  ·
                    rfl

theorem cell23_3424637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_3424637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424637 prefixEnd_3424637 := by exact prefixLift 3424637
  have htrace : WordTrace (prefixWord ++ tailWord_3424637) baseStart_3424637 baseEnd_3424637 := by
    simpa [prefixWord, tailWord_3424637, baseEnd_3424637] using wordTrace_append hprefix tailTrace_3424637
  have hstable : (prefixWord ++ tailWord_3424637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424637).length < 2 ^ (prefixWord ++ tailWord_3424637).sum := by decide
  have hdescent : baseEnd_3424637 < baseStart_3424637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424647 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_3424647 : Nat := 118140960795 + 3424647 * 2 ^ 59
def prefixEnd_3424647 : Nat := 4983230072969 + 3 ^ 40 * 3424647 * 2
def baseEnd_3424647 : Nat := 1758489982978167786562841

theorem tailTrace_3424647 : CollatzResearch.WordTrace tailWord_3424647 prefixEnd_3424647 1758489982978167786562841 := by
  unfold tailWord_3424647
  simp only [CollatzResearch.WordTrace]
  refine ⟨124907137624096276987784195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83271425082730851325189463 124907137624096276987784195)
  ·
    refine ⟨187360706436144415481676293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124907137624096276987784195 187360706436144415481676293)
    ·
      refine ⟨35130132456777077902814305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187360706436144415481676293 35130132456777077902814305)
      ·
        refine ⟨26347599342582808427110729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35130132456777077902814305 26347599342582808427110729)
        ·
          refine ⟨19760699506937106320333047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26347599342582808427110729 19760699506937106320333047)
          ·
            refine ⟨29641049260405659480499571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19760699506937106320333047 29641049260405659480499571)
            ·
              refine ⟨44461573890608489220749357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29641049260405659480499571 44461573890608489220749357)
              ·
                refine ⟨16673090208978183457781009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44461573890608489220749357 16673090208978183457781009)
                ·
                  refine ⟨12504817656733637593335757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16673090208978183457781009 12504817656733637593335757)
                  ·
                    refine ⟨4689306621275114097500909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12504817656733637593335757 4689306621275114097500909)
                    ·
                      refine ⟨1758489982978167786562841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689306621275114097500909 1758489982978167786562841)
                      ·
                        rfl

theorem cell23_3424647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_3424647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424647 prefixEnd_3424647 := by exact prefixLift 3424647
  have htrace : WordTrace (prefixWord ++ tailWord_3424647) baseStart_3424647 baseEnd_3424647 := by
    simpa [prefixWord, tailWord_3424647, baseEnd_3424647] using wordTrace_append hprefix tailTrace_3424647
  have hstable : (prefixWord ++ tailWord_3424647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424647).length < 2 ^ (prefixWord ++ tailWord_3424647).sum := by decide
  have hdescent : baseEnd_3424647 < baseStart_3424647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424648 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_3424648 : Nat := 118140960795 + 3424648 * 2 ^ 59
def prefixEnd_3424648 : Nat := 4983230072969 + 3 ^ 40 * 3424648 * 2
def baseEnd_3424648 : Nat := 1758490496458822282650337

theorem tailTrace_3424648 : CollatzResearch.WordTrace tailWord_3424648 prefixEnd_3424648 1758490496458822282650337 := by
  unfold tailWord_3424648
  simp only [CollatzResearch.WordTrace]
  refine ⟨62453587048546327079285299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83271449398061769439047065 62453587048546327079285299)
  ·
    refine ⟨93680380572819490618927949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62453587048546327079285299 93680380572819490618927949)
    ·
      refine ⟨35130142714807308982097981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93680380572819490618927949 35130142714807308982097981)
      ·
        refine ⟨13173803518052740868286743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35130142714807308982097981 13173803518052740868286743)
        ·
          refine ⟨19760705277079111302430115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13173803518052740868286743 19760705277079111302430115)
          ·
            refine ⟨29641057915618666953645173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19760705277079111302430115 29641057915618666953645173)
            ·
              refine ⟨2778849179589250026904235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29641057915618666953645173 2778849179589250026904235)
              ·
                refine ⟨4168273769383875040356353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778849179589250026904235 4168273769383875040356353)
                ·
                  refine ⟨3126205327037906280267265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168273769383875040356353 3126205327037906280267265)
                  ·
                    refine ⟨2344653995278429710200449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126205327037906280267265 2344653995278429710200449)
                    ·
                      refine ⟨1758490496458822282650337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344653995278429710200449 1758490496458822282650337)
                      ·
                        rfl

theorem cell23_3424648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_3424648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424648 prefixEnd_3424648 := by exact prefixLift 3424648
  have htrace : WordTrace (prefixWord ++ tailWord_3424648) baseStart_3424648 baseEnd_3424648 := by
    simpa [prefixWord, tailWord_3424648, baseEnd_3424648] using wordTrace_append hprefix tailTrace_3424648
  have hstable : (prefixWord ++ tailWord_3424648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424648).length < 2 ^ (prefixWord ++ tailWord_3424648).sum := by decide
  have hdescent : baseEnd_3424648 < baseStart_3424648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424707 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3]
def baseStart_3424707 : Nat := 118140960795 + 3424707 * 2 ^ 59
def prefixEnd_3424707 : Nat := 4983230072969 + 3 ^ 40 * 3424707 * 2
def baseEnd_3424707 : Nat := 1758520791817437551812565

theorem tailTrace_3424707 : CollatzResearch.WordTrace tailWord_3424707 prefixEnd_3424707 1758520791817437551812565 := by
  unfold tailWord_3424707
  simp only [CollatzResearch.WordTrace]
  refine ⟨124909326003878907234968375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83272884002585938156645583 124909326003878907234968375)
  ·
    refine ⟨187363989005818360852452563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124909326003878907234968375 187363989005818360852452563)
    ·
      refine ⟨281045983508727541278678845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187363989005818360852452563 281045983508727541278678845)
      ·
        refine ⟨105392243815772827979504567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281045983508727541278678845 105392243815772827979504567)
        ·
          refine ⟨158088365723659241969256851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105392243815772827979504567 158088365723659241969256851)
          ·
            refine ⟨237132548585488862953885277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158088365723659241969256851 237132548585488862953885277)
            ·
              refine ⟨88924705719558323607706979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237132548585488862953885277 88924705719558323607706979)
              ·
                refine ⟨133387058579337485411560469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88924705719558323607706979 133387058579337485411560469)
                ·
                  refine ⟨6252518370906444628666897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133387058579337485411560469 6252518370906444628666897)
                  ·
                    refine ⟨4689388778179833471500173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252518370906444628666897 4689388778179833471500173)
                    ·
                      refine ⟨1758520791817437551812565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689388778179833471500173 1758520791817437551812565)
                      ·
                        rfl

theorem cell23_3424707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_3424707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424707 prefixEnd_3424707 := by exact prefixLift 3424707
  have htrace : WordTrace (prefixWord ++ tailWord_3424707) baseStart_3424707 baseEnd_3424707 := by
    simpa [prefixWord, tailWord_3424707, baseEnd_3424707] using wordTrace_append hprefix tailTrace_3424707
  have hstable : (prefixWord ++ tailWord_3424707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424707).length < 2 ^ (prefixWord ++ tailWord_3424707).sum := by decide
  have hdescent : baseEnd_3424707 < baseStart_3424707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424720 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_3424720 : Nat := 118140960795 + 3424720 * 2 ^ 59
def prefixEnd_3424720 : Nat := 4983230072969 + 3 ^ 40 * 3424720 * 2
def baseEnd_3424720 : Nat := 1758527467065946000950005

theorem tailTrace_3424720 : CollatzResearch.WordTrace tailWord_3424720 prefixEnd_3424720 1758527467065946000950005 := by
  unfold tailWord_3424720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62454900076415905227595807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83273200101887873636794409 62454900076415905227595807)
  ·
    refine ⟨93682350114623857841393711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62454900076415905227595807 93682350114623857841393711)
    ·
      refine ⟨140523525171935786762090567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93682350114623857841393711 140523525171935786762090567)
      ·
        refine ⟨210785287757903680143135851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140523525171935786762090567 210785287757903680143135851)
        ·
          refine ⟨316177931636855520214703777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210785287757903680143135851 316177931636855520214703777)
          ·
            refine ⟨237133448727641640161027833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316177931636855520214703777 237133448727641640161027833)
            ·
              refine ⟨177850086545731230120770875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237133448727641640161027833 177850086545731230120770875)
              ·
                refine ⟨266775129818596845181156313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177850086545731230120770875 266775129818596845181156313)
                ·
                  refine ⟨200081347363947633885867235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266775129818596845181156313 200081347363947633885867235)
                  ·
                    refine ⟨300122021045921450828800853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 200081347363947633885867235 300122021045921450828800853)
                    ·
                      refine ⟨1758527467065946000950005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 300122021045921450828800853 1758527467065946000950005)
                      ·
                        rfl

theorem cell23_3424720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_3424720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424720 prefixEnd_3424720 := by exact prefixLift 3424720
  have htrace : WordTrace (prefixWord ++ tailWord_3424720) baseStart_3424720 baseEnd_3424720 := by
    simpa [prefixWord, tailWord_3424720, baseEnd_3424720] using wordTrace_append hprefix tailTrace_3424720
  have hstable : (prefixWord ++ tailWord_3424720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424720).length < 2 ^ (prefixWord ++ tailWord_3424720).sum := by decide
  have hdescent : baseEnd_3424720 < baseStart_3424720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424744 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 6]
def baseStart_3424744 : Nat := 118140960795 + 3424744 * 2 ^ 59
def prefixEnd_3424744 : Nat := 4983230072969 + 3 ^ 40 * 3424744 * 2
def baseEnd_3424744 : Nat := 195393310066850434116655

theorem tailTrace_3424744 : CollatzResearch.WordTrace tailWord_3424744 prefixEnd_3424744 195393310066850434116655 := by
  unfold tailWord_3424744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62455337752372431277032643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83273783669829908369376857 62455337752372431277032643)
  ·
    refine ⟨93683006628558646915548965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62455337752372431277032643 93683006628558646915548965)
    ·
      refine ⟨17565563742854746296665431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93683006628558646915548965 17565563742854746296665431)
      ·
        refine ⟨26348345614282119444998147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17565563742854746296665431 26348345614282119444998147)
        ·
          refine ⟨39522518421423179167497221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26348345614282119444998147 39522518421423179167497221)
          ·
            refine ⟨7410472204016846093905729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39522518421423179167497221 7410472204016846093905729)
            ·
              refine ⟨5557854153012634570429297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7410472204016846093905729 5557854153012634570429297)
              ·
                refine ⟨4168390614759475927821973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557854153012634570429297 4168390614759475927821973)
                ·
                  refine ⟨195393310066850434116655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4168390614759475927821973 195393310066850434116655)
                  ·
                    rfl

theorem cell23_3424744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_3424744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424744 prefixEnd_3424744 := by exact prefixLift 3424744
  have htrace : WordTrace (prefixWord ++ tailWord_3424744) baseStart_3424744 baseEnd_3424744 := by
    simpa [prefixWord, tailWord_3424744, baseEnd_3424744] using wordTrace_append hprefix tailTrace_3424744
  have hstable : (prefixWord ++ tailWord_3424744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424744).length < 2 ^ (prefixWord ++ tailWord_3424744).sum := by decide
  have hdescent : baseEnd_3424744 < baseStart_3424744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424764 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_3424764 : Nat := 118140960795 + 3424764 * 2 ^ 59
def prefixEnd_3424764 : Nat := 4983230072969 + 3 ^ 40 * 3424764 * 2
def baseEnd_3424764 : Nat := 1758550060214743828799803

theorem tailTrace_3424764 : CollatzResearch.WordTrace tailWord_3424764 prefixEnd_3424764 1758550060214743828799803 := by
  unfold tailWord_3424764
  simp only [CollatzResearch.WordTrace]
  refine ⟨62455702482336202984896673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83274269976448270646528897 62455702482336202984896673)
  ·
    refine ⟨46841776861752152238672505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62455702482336202984896673 46841776861752152238672505)
    ·
      refine ⟨35131332646314114179004379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46841776861752152238672505 35131332646314114179004379)
      ·
        refine ⟨52696998969471171268506569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35131332646314114179004379 52696998969471171268506569)
        ·
          refine ⟨39522749227103378451379927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52696998969471171268506569 39522749227103378451379927)
          ·
            refine ⟨59284123840655067677069891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39522749227103378451379927 59284123840655067677069891)
            ·
              refine ⟨88926185760982601515604837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59284123840655067677069891 88926185760982601515604837)
              ·
                refine ⟨16673659830184237784175907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88926185760982601515604837 16673659830184237784175907)
                ·
                  refine ⟨25010489745276356676263861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16673659830184237784175907 25010489745276356676263861)
                  ·
                    refine ⟨2344733413619658438399737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25010489745276356676263861 2344733413619658438399737)
                    ·
                      refine ⟨1758550060214743828799803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344733413619658438399737 1758550060214743828799803)
                      ·
                        rfl

theorem cell23_3424764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_3424764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424764 prefixEnd_3424764 := by exact prefixLift 3424764
  have htrace : WordTrace (prefixWord ++ tailWord_3424764) baseStart_3424764 baseEnd_3424764 := by
    simpa [prefixWord, tailWord_3424764, baseEnd_3424764] using wordTrace_append hprefix tailTrace_3424764
  have hstable : (prefixWord ++ tailWord_3424764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424764).length < 2 ^ (prefixWord ++ tailWord_3424764).sum := by decide
  have hdescent : baseEnd_3424764 < baseStart_3424764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424787 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 1, 6]
def baseStart_3424787 : Nat := 118140960795 + 3424787 * 2 ^ 59
def prefixEnd_3424787 : Nat := 4983230072969 + 3 ^ 40 * 3424787 * 2
def baseEnd_3424787 : Nat := 586187290089932412937399

theorem tailTrace_3424787 : CollatzResearch.WordTrace tailWord_3424787 prefixEnd_3424787 586187290089932412937399 := by
  unfold tailWord_3424787
  simp only [CollatzResearch.WordTrace]
  refine ⟨124912243843589080897880615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83274829229059387265253743 124912243843589080897880615)
  ·
    refine ⟨187368365765383621346820923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124912243843589080897880615 187368365765383621346820923)
    ·
      refine ⟨281052548648075432020231385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187368365765383621346820923 281052548648075432020231385)
      ·
        refine ⟨210789411486056574015173539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281052548648075432020231385 210789411486056574015173539)
        ·
          refine ⟨316184117229084861022760309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210789411486056574015173539 316184117229084861022760309)
          ·
            refine ⟨29642260990226705720883779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 316184117229084861022760309 29642260990226705720883779)
            ·
              refine ⟨44463391485340058581325669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29642260990226705720883779 44463391485340058581325669)
              ·
                refine ⟨8336885903501260983998563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44463391485340058581325669 8336885903501260983998563)
                ·
                  refine ⟨12505328855251891475997845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336885903501260983998563 12505328855251891475997845)
                  ·
                    refine ⟨586187290089932412937399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12505328855251891475997845 586187290089932412937399)
                    ·
                      rfl

theorem cell23_3424787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 6].length) (baseStart_3424787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424787 prefixEnd_3424787 := by exact prefixLift 3424787
  have htrace : WordTrace (prefixWord ++ tailWord_3424787) baseStart_3424787 baseEnd_3424787 := by
    simpa [prefixWord, tailWord_3424787, baseEnd_3424787] using wordTrace_append hprefix tailTrace_3424787
  have hstable : (prefixWord ++ tailWord_3424787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424787).length < 2 ^ (prefixWord ++ tailWord_3424787).sum := by decide
  have hdescent : baseEnd_3424787 < baseStart_3424787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424828 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_3424828 : Nat := 118140960795 + 3424828 * 2 ^ 59
def prefixEnd_3424828 : Nat := 4983230072969 + 3 ^ 40 * 3424828 * 2
def baseEnd_3424828 : Nat := 1758582922976631578399509

theorem tailTrace_3424828 : CollatzResearch.WordTrace tailWord_3424828 prefixEnd_3424828 1758582922976631578399509 := by
  unfold tailWord_3424828
  simp only [CollatzResearch.WordTrace]
  refine ⟨62456869618220272450061569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83275826157627029933415425 62456869618220272450061569)
  ·
    refine ⟨46842652213665204337546177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62456869618220272450061569 46842652213665204337546177)
    ·
      refine ⟨35131989160248903253159633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46842652213665204337546177 35131989160248903253159633)
      ·
        refine ⟨26348991870186677439869725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35131989160248903253159633 26348991870186677439869725)
        ·
          refine ⟨9880871951320004039951147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26348991870186677439869725 9880871951320004039951147)
          ·
            refine ⟨14821307926980006059926721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880871951320004039951147 14821307926980006059926721)
            ·
              refine ⟨11115980945235004544945041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14821307926980006059926721 11115980945235004544945041)
              ·
                refine ⟨8336985708926253408708781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11115980945235004544945041 8336985708926253408708781)
                ·
                  refine ⟨3126369640847345028265793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8336985708926253408708781 3126369640847345028265793)
                  ·
                    refine ⟨2344777230635508771199345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126369640847345028265793 2344777230635508771199345)
                    ·
                      refine ⟨1758582922976631578399509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344777230635508771199345 1758582922976631578399509)
                      ·
                        rfl

theorem cell23_3424828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_3424828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424828 prefixEnd_3424828 := by exact prefixLift 3424828
  have htrace : WordTrace (prefixWord ++ tailWord_3424828) baseStart_3424828 baseEnd_3424828 := by
    simpa [prefixWord, tailWord_3424828, baseEnd_3424828] using wordTrace_append hprefix tailTrace_3424828
  have hstable : (prefixWord ++ tailWord_3424828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424828).length < 2 ^ (prefixWord ++ tailWord_3424828).sum := by decide
  have hdescent : baseEnd_3424828 < baseStart_3424828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424831 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_3424831 : Nat := 118140960795 + 3424831 * 2 ^ 59
def prefixEnd_3424831 : Nat := 4983230072969 + 3 ^ 40 * 3424831 * 2
def baseEnd_3424831 : Nat := 1758584463418595066661995

theorem tailTrace_3424831 : CollatzResearch.WordTrace tailWord_3424831 prefixEnd_3424831 1758584463418595066661995 := by
  unfold tailWord_3424831
  simp only [CollatzResearch.WordTrace]
  refine ⟨124913848655429676412482347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83275899103619784274988231 124913848655429676412482347)
  ·
    refine ⟨187370772983144514618723521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124913848655429676412482347 187370772983144514618723521)
    ·
      refine ⟨140528079737358385964042641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187370772983144514618723521 140528079737358385964042641)
      ·
        refine ⟨105396059803018789473031981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140528079737358385964042641 105396059803018789473031981)
        ·
          refine ⟨39523522426132046052386993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105396059803018789473031981 39523522426132046052386993)
          ·
            refine ⟨29642641819599034539290245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39523522426132046052386993 29642641819599034539290245)
            ·
              refine ⟨5557995341174818976116921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29642641819599034539290245 5557995341174818976116921)
              ·
                refine ⟨4168496505881114232087691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5557995341174818976116921 4168496505881114232087691)
                ·
                  refine ⟨6252744758821671348131537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168496505881114232087691 6252744758821671348131537)
                  ·
                    refine ⟨4689558569116253511098653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252744758821671348131537 4689558569116253511098653)
                    ·
                      refine ⟨1758584463418595066661995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689558569116253511098653 1758584463418595066661995)
                      ·
                        rfl

theorem cell23_3424831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_3424831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424831 prefixEnd_3424831 := by exact prefixLift 3424831
  have htrace : WordTrace (prefixWord ++ tailWord_3424831) baseStart_3424831 baseEnd_3424831 := by
    simpa [prefixWord, tailWord_3424831, baseEnd_3424831] using wordTrace_append hprefix tailTrace_3424831
  have hstable : (prefixWord ++ tailWord_3424831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424831).length < 2 ^ (prefixWord ++ tailWord_3424831).sum := by decide
  have hdescent : baseEnd_3424831 < baseStart_3424831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424838 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_3424838 : Nat := 118140960795 + 3424838 * 2 ^ 59
def prefixEnd_3424838 : Nat := 4983230072969 + 3 ^ 40 * 3424838 * 2
def baseEnd_3424838 : Nat := 586196019261058846424821

theorem tailTrace_3424838 : CollatzResearch.WordTrace tailWord_3424838 prefixEnd_3424838 586196019261058846424821 := by
  unfold tailWord_3424838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903565748950134893999599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83276069310936211071991445 3903565748950134893999599)
  ·
    refine ⟨5855348623425202340999399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903565748950134893999599 5855348623425202340999399)
    ·
      refine ⟨8783022935137803511499099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855348623425202340999399 8783022935137803511499099)
      ·
        refine ⟨13174534402706705267248649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8783022935137803511499099 13174534402706705267248649)
        ·
          refine ⟨9880900802030028950436487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13174534402706705267248649 9880900802030028950436487)
          ·
            refine ⟨14821351203045043425654731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9880900802030028950436487 14821351203045043425654731)
            ·
              refine ⟨22232026804567565138482097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14821351203045043425654731 22232026804567565138482097)
              ·
                refine ⟨16674020103425673853861573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22232026804567565138482097 16674020103425673853861573)
                ·
                  refine ⟨3126378769392313847599045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16674020103425673853861573 3126378769392313847599045)
                  ·
                    refine ⟨586196019261058846424821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126378769392313847599045 586196019261058846424821)
                    ·
                      rfl

theorem cell23_3424838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_3424838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424838 prefixEnd_3424838 := by exact prefixLift 3424838
  have htrace : WordTrace (prefixWord ++ tailWord_3424838) baseStart_3424838 baseEnd_3424838 := by
    simpa [prefixWord, tailWord_3424838, baseEnd_3424838] using wordTrace_append hprefix tailTrace_3424838
  have hstable : (prefixWord ++ tailWord_3424838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424838).length < 2 ^ (prefixWord ++ tailWord_3424838).sum := by decide
  have hdescent : baseEnd_3424838 < baseStart_3424838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424844 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3424844 : Nat := 118140960795 + 3424844 * 2 ^ 59
def prefixEnd_3424844 : Nat := 4983230072969 + 3 ^ 40 * 3424844 * 2
def baseEnd_3424844 : Nat := 1758591138667103515799435

theorem tailTrace_3424844 : CollatzResearch.WordTrace tailWord_3424844 prefixEnd_3424844 1758591138667103515799435 := by
  unfold tailWord_3424844
  simp only [CollatzResearch.WordTrace]
  refine ⟨62457161402191289816352793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83276215202921719755137057 62457161402191289816352793)
  ·
    refine ⟨46842871051643467362264595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62457161402191289816352793 46842871051643467362264595)
    ·
      refine ⟨70264306577465201043396893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46842871051643467362264595 70264306577465201043396893)
      ·
        refine ⟨26349114966549450391273835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70264306577465201043396893 26349114966549450391273835)
        ·
          refine ⟨39523672449824175586910753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26349114966549450391273835 39523672449824175586910753)
          ·
            refine ⟨29642754337368131690183065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39523672449824175586910753 29642754337368131690183065)
            ·
              refine ⟨22232065753026098767637299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29642754337368131690183065 22232065753026098767637299)
              ·
                refine ⟨33348098629539148151455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22232065753026098767637299 33348098629539148151455949)
                ·
                  refine ⟨12505536986077180556795981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33348098629539148151455949 12505536986077180556795981)
                  ·
                    refine ⟨4689576369778942708798493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12505536986077180556795981 4689576369778942708798493)
                    ·
                      refine ⟨1758591138667103515799435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689576369778942708798493 1758591138667103515799435)
                      ·
                        rfl

theorem cell23_3424844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3424844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424844 prefixEnd_3424844 := by exact prefixLift 3424844
  have htrace : WordTrace (prefixWord ++ tailWord_3424844) baseStart_3424844 baseEnd_3424844 := by
    simpa [prefixWord, tailWord_3424844, baseEnd_3424844] using wordTrace_append hprefix tailTrace_3424844
  have hstable : (prefixWord ++ tailWord_3424844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424844).length < 2 ^ (prefixWord ++ tailWord_3424844).sum := by decide
  have hdescent : baseEnd_3424844 < baseStart_3424844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424871 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_3424871 : Nat := 118140960795 + 3424871 * 2 ^ 59
def prefixEnd_3424871 : Nat := 4983230072969 + 3 ^ 40 * 3424871 * 2
def baseEnd_3424871 : Nat := 1758605002644774910161811

theorem tailTrace_3424871 : CollatzResearch.WordTrace tailWord_3424871 prefixEnd_3424871 1758605002644774910161811 := by
  unfold tailWord_3424871
  simp only [CollatzResearch.WordTrace]
  refine ⟨124915307575284763243938467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83276871716856508829292311 124915307575284763243938467)
  ·
    refine ⟨187372961362927144865907701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124915307575284763243938467 187372961362927144865907701)
    ·
      refine ⟨17566215127774419831178847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187372961362927144865907701 17566215127774419831178847)
      ·
        refine ⟨26349322691661629746768271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17566215127774419831178847 26349322691661629746768271)
        ·
          refine ⟨39523984037492444620152407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26349322691661629746768271 39523984037492444620152407)
          ·
            refine ⟨59285976056238666930228611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39523984037492444620152407 59285976056238666930228611)
            ·
              refine ⟨88928964084358000395342917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59285976056238666930228611 88928964084358000395342917)
              ·
                refine ⟨16674180765817125074126797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88928964084358000395342917 16674180765817125074126797)
                ·
                  refine ⟨6252817787181421902797549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16674180765817125074126797 6252817787181421902797549)
                  ·
                    refine ⟨2344806670193033213549081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6252817787181421902797549 2344806670193033213549081)
                    ·
                      refine ⟨1758605002644774910161811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344806670193033213549081 1758605002644774910161811)
                      ·
                        rfl

theorem cell23_3424871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_3424871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424871 prefixEnd_3424871 := by exact prefixLift 3424871
  have htrace : WordTrace (prefixWord ++ tailWord_3424871) baseStart_3424871 baseEnd_3424871 := by
    simpa [prefixWord, tailWord_3424871, baseEnd_3424871] using wordTrace_append hprefix tailTrace_3424871
  have hstable : (prefixWord ++ tailWord_3424871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424871).length < 2 ^ (prefixWord ++ tailWord_3424871).sum := by decide
  have hdescent : baseEnd_3424871 < baseStart_3424871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424872 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 2, 4]
def baseStart_3424872 : Nat := 118140960795 + 3424872 * 2 ^ 59
def prefixEnd_3424872 : Nat := 4983230072969 + 3 ^ 40 * 3424872 * 2
def baseEnd_3424872 : Nat := 586201838708476468749769

theorem tailTrace_3424872 : CollatzResearch.WordTrace tailWord_3424872 prefixEnd_3424872 586201838708476468749769 := by
  unfold tailWord_3424872
  simp only [CollatzResearch.WordTrace]
  refine ⟨62457672024140570207362435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83276896032187426943149913 62457672024140570207362435)
  ·
    refine ⟨93686508036210855311043653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62457672024140570207362435 93686508036210855311043653)
    ·
      refine ⟨17566220256789535370820685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93686508036210855311043653 17566220256789535370820685)
      ·
        refine ⟨6587332596296075764057757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17566220256789535370820685 6587332596296075764057757)
        ·
          refine ⟨2470249723611028411521659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6587332596296075764057757 2470249723611028411521659)
          ·
            refine ⟨3705374585416542617282489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470249723611028411521659 3705374585416542617282489)
            ·
              refine ⟨2779030939062406962961867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3705374585416542617282489 2779030939062406962961867)
              ·
                refine ⟨4168546408593610444442801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779030939062406962961867 4168546408593610444442801)
                ·
                  refine ⟨3126409806445207833332101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168546408593610444442801 3126409806445207833332101)
                  ·
                    refine ⟨586201838708476468749769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126409806445207833332101 586201838708476468749769)
                    ·
                      rfl

theorem cell23_3424872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_3424872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424872 prefixEnd_3424872 := by exact prefixLift 3424872
  have htrace : WordTrace (prefixWord ++ tailWord_3424872) baseStart_3424872 baseEnd_3424872 := by
    simpa [prefixWord, tailWord_3424872, baseEnd_3424872] using wordTrace_append hprefix tailTrace_3424872
  have hstable : (prefixWord ++ tailWord_3424872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424872).length < 2 ^ (prefixWord ++ tailWord_3424872).sum := by decide
  have hdescent : baseEnd_3424872 < baseStart_3424872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424901 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_3424901 : Nat := 118140960795 + 3424901 * 2 ^ 59
def prefixEnd_3424901 : Nat := 4983230072969 + 3 ^ 40 * 3424901 * 2
def baseEnd_3424901 : Nat := 1758620407064409792786673

theorem tailTrace_3424901 : CollatzResearch.WordTrace tailWord_3424901 prefixEnd_3424901 1758620407064409792786673 := by
  unfold tailWord_3424901
  simp only [CollatzResearch.WordTrace]
  refine ⟨124916401765176078367530557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83277601176784052245020371 124916401765176078367530557)
  ·
    refine ⟨46843650661941029387823959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124916401765176078367530557 46843650661941029387823959)
    ·
      refine ⟨70265475992911544081735939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46843650661941029387823959 70265475992911544081735939)
      ·
        refine ⟨105398213989367316122603909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70265475992911544081735939 105398213989367316122603909)
        ·
          refine ⟨19762165123006371772988233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105398213989367316122603909 19762165123006371772988233)
          ·
            refine ⟨14821623842254778829741175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19762165123006371772988233 14821623842254778829741175)
            ·
              refine ⟨22232435763382168244611763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14821623842254778829741175 22232435763382168244611763)
              ·
                refine ⟨33348653645073252366917645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22232435763382168244611763 33348653645073252366917645)
                ·
                  refine ⟨12505745116902469637594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33348653645073252366917645 12505745116902469637594117)
                  ·
                    refine ⟨2344827209419213057048897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12505745116902469637594117 2344827209419213057048897)
                    ·
                      refine ⟨1758620407064409792786673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2344827209419213057048897 1758620407064409792786673)
                      ·
                        rfl

theorem cell23_3424901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_3424901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424901 prefixEnd_3424901 := by exact prefixLift 3424901
  have htrace : WordTrace (prefixWord ++ tailWord_3424901) baseStart_3424901 baseEnd_3424901 := by
    simpa [prefixWord, tailWord_3424901, baseEnd_3424901] using wordTrace_append hprefix tailTrace_3424901
  have hstable : (prefixWord ++ tailWord_3424901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424901).length < 2 ^ (prefixWord ++ tailWord_3424901).sum := by decide
  have hdescent : baseEnd_3424901 < baseStart_3424901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424907 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 11]
def baseStart_3424907 : Nat := 118140960795 + 3424907 * 2 ^ 59
def prefixEnd_3424907 : Nat := 4983230072969 + 3 ^ 40 * 3424907 * 2
def baseEnd_3424907 : Nat := 195402609772037418812405

theorem tailTrace_3424907 : CollatzResearch.WordTrace tailWord_3424907 prefixEnd_3424907 195402609772037418812405 := by
  unfold tailWord_3424907
  simp only [CollatzResearch.WordTrace]
  refine ⟨124916620603154341392248975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83277747068769560928165983 124916620603154341392248975)
  ·
    refine ⟨187374930904731512088373463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124916620603154341392248975 187374930904731512088373463)
    ·
      refine ⟨281062396357097268132560195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187374930904731512088373463 281062396357097268132560195)
      ·
        refine ⟨421593594535645902198840293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281062396357097268132560195 421593594535645902198840293)
        ·
          refine ⟨79048798975433606662282555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421593594535645902198840293 79048798975433606662282555)
          ·
            refine ⟨118573198463150409993423833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79048798975433606662282555 118573198463150409993423833)
            ·
              refine ⟨88929898847362807495067875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118573198463150409993423833 88929898847362807495067875)
              ·
                refine ⟨133394848271044211242601813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88929898847362807495067875 133394848271044211242601813)
                ·
                  refine ⟨195402609772037418812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 133394848271044211242601813 195402609772037418812405)
                  ·
                    rfl

theorem cell23_3424907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 11].length) (baseStart_3424907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424907 prefixEnd_3424907 := by exact prefixLift 3424907
  have htrace : WordTrace (prefixWord ++ tailWord_3424907) baseStart_3424907 baseEnd_3424907 := by
    simpa [prefixWord, tailWord_3424907, baseEnd_3424907] using wordTrace_append hprefix tailTrace_3424907
  have hstable : (prefixWord ++ tailWord_3424907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424907).length < 2 ^ (prefixWord ++ tailWord_3424907).sum := by decide
  have hdescent : baseEnd_3424907 < baseStart_3424907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424941 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3424941 : Nat := 118140960795 + 3424941 * 2 ^ 59
def prefixEnd_3424941 : Nat := 4983230072969 + 3 ^ 40 * 3424941 * 2
def baseEnd_3424941 : Nat := 195404549587843292920721

theorem tailTrace_3424941 : CollatzResearch.WordTrace tailWord_3424941 prefixEnd_3424941 195404549587843292920721 := by
  unfold tailWord_3424941
  simp only [CollatzResearch.WordTrace]
  refine ⟨124917860685031165198986677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83278573790020776799324451 124917860685031165198986677)
  ·
    refine ⟨11711049439221671737405001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124917860685031165198986677 11711049439221671737405001)
    ·
      refine ⟨8783287079416253803053751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11711049439221671737405001 8783287079416253803053751)
      ·
        refine ⟨13174930619124380704580627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8783287079416253803053751 13174930619124380704580627)
        ·
          refine ⟨19762395928686571056870941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174930619124380704580627 19762395928686571056870941)
          ·
            refine ⟨7410898473257464146326603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19762395928686571056870941 7410898473257464146326603)
            ·
              refine ⟨11116347709886196219489905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410898473257464146326603 11116347709886196219489905)
              ·
                refine ⟨8337260782414647164617429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116347709886196219489905 8337260782414647164617429)
                ·
                  refine ⟨195404549587843292920721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8337260782414647164617429 195404549587843292920721)
                  ·
                    rfl

theorem cell23_3424941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3424941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424941 prefixEnd_3424941 := by exact prefixLift 3424941
  have htrace : WordTrace (prefixWord ++ tailWord_3424941) baseStart_3424941 baseEnd_3424941 := by
    simpa [prefixWord, tailWord_3424941, baseEnd_3424941] using wordTrace_append hprefix tailTrace_3424941
  have hstable : (prefixWord ++ tailWord_3424941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424941).length < 2 ^ (prefixWord ++ tailWord_3424941).sum := by decide
  have hdescent : baseEnd_3424941 < baseStart_3424941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424954 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_3424954 : Nat := 118140960795 + 3424954 * 2 ^ 59
def prefixEnd_3424954 : Nat := 4983230072969 + 3 ^ 40 * 3424954 * 2
def baseEnd_3424954 : Nat := 586215873846366028474643

theorem tailTrace_3424954 : CollatzResearch.WordTrace tailWord_3424954 prefixEnd_3424954 586215873846366028474643 := by
  unfold tailWord_3424954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229583708496017104802479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83278889889322712279473277 31229583708496017104802479)
  ·
    refine ⟨46844375562744025657203719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31229583708496017104802479 46844375562744025657203719)
    ·
      refine ⟨70266563344116038485805579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46844375562744025657203719 70266563344116038485805579)
      ·
        refine ⟨105399845016174057728708369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70266563344116038485805579 105399845016174057728708369)
        ·
          refine ⟨79049883762130543296531277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105399845016174057728708369 79049883762130543296531277)
          ·
            refine ⟨29643706410798953736199229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79049883762130543296531277 29643706410798953736199229)
            ·
              refine ⟨11116389904049607651074711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29643706410798953736199229 11116389904049607651074711)
              ·
                refine ⟨16674584856074411476612067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116389904049607651074711 16674584856074411476612067)
                ·
                  refine ⟨25011877284111617214918101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16674584856074411476612067 25011877284111617214918101)
                  ·
                    refine ⟨586215873846366028474643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25011877284111617214918101 586215873846366028474643)
                    ·
                      rfl

theorem cell23_3424954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_3424954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424954 prefixEnd_3424954 := by exact prefixLift 3424954
  have htrace : WordTrace (prefixWord ++ tailWord_3424954) baseStart_3424954 baseEnd_3424954 := by
    simpa [prefixWord, tailWord_3424954, baseEnd_3424954] using wordTrace_append hprefix tailTrace_3424954
  have hstable : (prefixWord ++ tailWord_3424954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424954).length < 2 ^ (prefixWord ++ tailWord_3424954).sum := by decide
  have hdescent : baseEnd_3424954 < baseStart_3424954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3424958 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_3424958 : Nat := 118140960795 + 3424958 * 2 ^ 59
def prefixEnd_3424958 : Nat := 4983230072969 + 3 ^ 40 * 3424958 * 2
def baseEnd_3424958 : Nat := 195405519495746229974879

theorem tailTrace_3424958 : CollatzResearch.WordTrace tailWord_3424958 prefixEnd_3424958 195405519495746229974879 := by
  unfold tailWord_3424958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614810090746197137794441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83278987150646384734903685 15614810090746197137794441)
  ·
    refine ⟨11711107568059647853345831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15614810090746197137794441 11711107568059647853345831)
    ·
      refine ⟨17566661352089471780018747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711107568059647853345831 17566661352089471780018747)
      ·
        refine ⟨26349992028134207670028121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17566661352089471780018747 26349992028134207670028121)
        ·
          refine ⟨19762494021100655752521091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26349992028134207670028121 19762494021100655752521091)
          ·
            refine ⟨29643741031650983628781637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19762494021100655752521091 29643741031650983628781637)
            ·
              refine ⟨5558201443434559430396557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29643741031650983628781637 5558201443434559430396557)
              ·
                refine ⟨2084325541287959786398709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558201443434559430396557 2084325541287959786398709)
                ·
                  refine ⟨195405519495746229974879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2084325541287959786398709 195405519495746229974879)
                  ·
                    rfl

theorem cell23_3424958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_3424958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3424958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3424958 prefixEnd_3424958 := by exact prefixLift 3424958
  have htrace : WordTrace (prefixWord ++ tailWord_3424958) baseStart_3424958 baseEnd_3424958 := by
    simpa [prefixWord, tailWord_3424958, baseEnd_3424958] using wordTrace_append hprefix tailTrace_3424958
  have hstable : (prefixWord ++ tailWord_3424958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3424958).length < 2 ^ (prefixWord ++ tailWord_3424958).sum := by decide
  have hdescent : baseEnd_3424958 < baseStart_3424958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3424958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425001 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_3425001 : Nat := 118140960795 + 3425001 * 2 ^ 59
def prefixEnd_3425001 : Nat := 4983230072969 + 3 ^ 40 * 3425001 * 2
def baseEnd_3425001 : Nat := 586223918376619800512071

theorem tailTrace_3425001 : CollatzResearch.WordTrace tailWord_3425001 prefixEnd_3425001 586223918376619800512071 := by
  unfold tailWord_3425001
  simp only [CollatzResearch.WordTrace]
  refine ⟨124920049064813795446170857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83280032709875863630780571 124920049064813795446170857)
  ·
    refine ⟨93690036798610346584628143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124920049064813795446170857 93690036798610346584628143)
    ·
      refine ⟨140535055197915519876942215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93690036798610346584628143 140535055197915519876942215)
      ·
        refine ⟨210802582796873279815413323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140535055197915519876942215 210802582796873279815413323)
        ·
          refine ⟨316203874195309919723119985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210802582796873279815413323 316203874195309919723119985)
          ·
            refine ⟨237152905646482439792339989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316203874195309919723119985 237152905646482439792339989)
            ·
              refine ⟨11116542452178864365265937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237152905646482439792339989 11116542452178864365265937)
              ·
                refine ⟨8337406839134148273949453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116542452178864365265937 8337406839134148273949453)
                ·
                  refine ⟨3126527564675305602731045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8337406839134148273949453 3126527564675305602731045)
                  ·
                    refine ⟨586223918376619800512071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126527564675305602731045 586223918376619800512071)
                    ·
                      rfl

theorem cell23_3425001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_3425001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425001 prefixEnd_3425001 := by exact prefixLift 3425001
  have htrace : WordTrace (prefixWord ++ tailWord_3425001) baseStart_3425001 baseEnd_3425001 := by
    simpa [prefixWord, tailWord_3425001, baseEnd_3425001] using wordTrace_append hprefix tailTrace_3425001
  have hstable : (prefixWord ++ tailWord_3425001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425001).length < 2 ^ (prefixWord ++ tailWord_3425001).sum := by decide
  have hdescent : baseEnd_3425001 < baseStart_3425001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425004 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3425004 : Nat := 118140960795 + 3425004 * 2 ^ 59
def prefixEnd_3425004 : Nat := 4983230072969 + 3 ^ 40 * 3425004 * 2
def baseEnd_3425004 : Nat := 1758673295571822889798699

theorem tailTrace_3425004 : CollatzResearch.WordTrace tailWord_3425004 prefixEnd_3425004 1758673295571822889798699 := by
  unfold tailWord_3425004
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460079241901463479265033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83280105655868617972353377 62460079241901463479265033)
  ·
    refine ⟨46845059431426097609448775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62460079241901463479265033 46845059431426097609448775)
    ·
      refine ⟨70267589147139146414173163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46845059431426097609448775 70267589147139146414173163)
      ·
        refine ⟨105401383720708719621259745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70267589147139146414173163 105401383720708719621259745)
        ·
          refine ⟨79051037790531539715944809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105401383720708719621259745 79051037790531539715944809)
          ·
            refine ⟨59288278342898654786958607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79051037790531539715944809 59288278342898654786958607)
            ·
              refine ⟨88932417514347982180437911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59288278342898654786958607 88932417514347982180437911)
              ·
                refine ⟨133398626271521973270656867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88932417514347982180437911 133398626271521973270656867)
                ·
                  refine ⟨200097939407282959905985301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133398626271521973270656867 200097939407282959905985301)
                  ·
                    refine ⟨9379590909716388745593061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200097939407282959905985301 9379590909716388745593061)
                    ·
                      refine ⟨1758673295571822889798699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9379590909716388745593061 1758673295571822889798699)
                      ·
                        rfl

theorem cell23_3425004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3425004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425004 prefixEnd_3425004 := by exact prefixLift 3425004
  have htrace : WordTrace (prefixWord ++ tailWord_3425004) baseStart_3425004 baseEnd_3425004 := by
    simpa [prefixWord, tailWord_3425004, baseEnd_3425004] using wordTrace_append hprefix tailTrace_3425004
  have hstable : (prefixWord ++ tailWord_3425004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425004).length < 2 ^ (prefixWord ++ tailWord_3425004).sum := by decide
  have hdescent : baseEnd_3425004 < baseStart_3425004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425011 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3]
def baseStart_3425011 : Nat := 118140960795 + 3425011 * 2 ^ 59
def prefixEnd_3425011 : Nat := 4983230072969 + 3 ^ 40 * 3425011 * 2
def baseEnd_3425011 : Nat := 1758676889936404362411167

theorem tailTrace_3425011 : CollatzResearch.WordTrace tailWord_3425011 prefixEnd_3425011 1758676889936404362411167 := by
  unfold tailWord_3425011
  simp only [CollatzResearch.WordTrace]
  refine ⟨124920413794777567154034887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83280275863185044769356591 124920413794777567154034887)
  ·
    refine ⟨187380620692166350731052331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124920413794777567154034887 187380620692166350731052331)
    ·
      refine ⟨281070931038249526096578497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187380620692166350731052331 281070931038249526096578497)
      ·
        refine ⟨210803198278687144572433873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281070931038249526096578497 210803198278687144572433873)
        ·
          refine ⟨158102398709015358429325405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210803198278687144572433873 158102398709015358429325405)
          ·
            refine ⟨59288399515880759410997027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158102398709015358429325405 59288399515880759410997027)
            ·
              refine ⟨88932599273821139116495541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59288399515880759410997027 88932599273821139116495541)
              ·
                refine ⟨8337431181920731792171457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88932599273821139116495541 8337431181920731792171457)
                ·
                  refine ⟨6253073386440548844128593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337431181920731792171457 6253073386440548844128593)
                  ·
                    refine ⟨4689805039830411633096445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253073386440548844128593 4689805039830411633096445)
                    ·
                      refine ⟨1758676889936404362411167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689805039830411633096445 1758676889936404362411167)
                      ·
                        rfl

theorem cell23_3425011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_3425011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425011 prefixEnd_3425011 := by exact prefixLift 3425011
  have htrace : WordTrace (prefixWord ++ tailWord_3425011) baseStart_3425011 baseEnd_3425011 := by
    simpa [prefixWord, tailWord_3425011, baseEnd_3425011] using wordTrace_append hprefix tailTrace_3425011
  have hstable : (prefixWord ++ tailWord_3425011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425011).length < 2 ^ (prefixWord ++ tailWord_3425011).sum := by decide
  have hdescent : baseEnd_3425011 < baseStart_3425011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425028 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3425028 : Nat := 118140960795 + 3425028 * 2 ^ 59
def prefixEnd_3425028 : Nat := 4983230072969 + 3 ^ 40 * 3425028 * 2
def baseEnd_3425028 : Nat := 1758685619107530795898589

theorem tailTrace_3425028 : CollatzResearch.WordTrace tailWord_3425028 prefixEnd_3425028 1758685619107530795898589 := by
  unfold tailWord_3425028
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460516917857989528701869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83280689223810652704935825 62460516917857989528701869)
  ·
    refine ⟨23422693844196746073263201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62460516917857989528701869 23422693844196746073263201)
    ·
      refine ⟨17567020383147559554947401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23422693844196746073263201 17567020383147559554947401)
      ·
        refine ⟨13175265287360669666210551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17567020383147559554947401 13175265287360669666210551)
        ·
          refine ⟨19762897931041004499315827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13175265287360669666210551 19762897931041004499315827)
          ·
            refine ⟨29644346896561506748973741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19762897931041004499315827 29644346896561506748973741)
            ·
              refine ⟨11116630086210565030865153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29644346896561506748973741 11116630086210565030865153)
              ·
                refine ⟨8337472564657923773148865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116630086210565030865153 8337472564657923773148865)
                ·
                  refine ⟨6253104423493442829861649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337472564657923773148865 6253104423493442829861649)
                  ·
                    refine ⟨4689828317620082122396237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253104423493442829861649 4689828317620082122396237)
                    ·
                      refine ⟨1758685619107530795898589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4689828317620082122396237 1758685619107530795898589)
                      ·
                        rfl

theorem cell23_3425028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3425028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425028 prefixEnd_3425028 := by exact prefixLift 3425028
  have htrace : WordTrace (prefixWord ++ tailWord_3425028) baseStart_3425028 baseEnd_3425028 := by
    simpa [prefixWord, tailWord_3425028, baseEnd_3425028] using wordTrace_append hprefix tailTrace_3425028
  have hstable : (prefixWord ++ tailWord_3425028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425028).length < 2 ^ (prefixWord ++ tailWord_3425028).sum := by decide
  have hdescent : baseEnd_3425028 < baseStart_3425028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425031 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 8]
def baseStart_3425031 : Nat := 118140960795 + 3425031 * 2 ^ 59
def prefixEnd_3425031 : Nat := 4983230072969 + 3 ^ 40 * 3425031 * 2
def baseEnd_3425031 : Nat := 195409684394388253795675

theorem tailTrace_3425031 : CollatzResearch.WordTrace tailWord_3425031 prefixEnd_3425031 195409684394388253795675 := by
  unfold tailWord_3425031
  simp only [CollatzResearch.WordTrace]
  refine ⟨124921143254705110569762947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83280762169803407046508631 124921143254705110569762947)
  ·
    refine ⟨187381714882057665854644421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124921143254705110569762947 187381714882057665854644421)
    ·
      refine ⟨35134071540385812347745829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187381714882057665854644421 35134071540385812347745829)
      ·
        refine ⟨6587638413822339815202343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35134071540385812347745829 6587638413822339815202343)
        ·
          refine ⟨9881457620733509722803515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587638413822339815202343 9881457620733509722803515)
          ·
            refine ⟨14822186431100264584205273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881457620733509722803515 14822186431100264584205273)
            ·
              refine ⟨11116639823325198438153955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14822186431100264584205273 11116639823325198438153955)
              ·
                refine ⟨16674959734987797657230933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116639823325198438153955 16674959734987797657230933)
                ·
                  refine ⟨195409684394388253795675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16674959734987797657230933 195409684394388253795675)
                  ·
                    rfl

theorem cell23_3425031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 8].length) (baseStart_3425031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425031 prefixEnd_3425031 := by exact prefixLift 3425031
  have htrace : WordTrace (prefixWord ++ tailWord_3425031) baseStart_3425031 baseEnd_3425031 := by
    simpa [prefixWord, tailWord_3425031, baseEnd_3425031] using wordTrace_append hprefix tailTrace_3425031
  have hstable : (prefixWord ++ tailWord_3425031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425031).length < 2 ^ (prefixWord ++ tailWord_3425031).sum := by decide
  have hdescent : baseEnd_3425031 < baseStart_3425031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425061 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_3425061 : Nat := 118140960795 + 3425061 * 2 ^ 59
def prefixEnd_3425061 : Nat := 4983230072969 + 3 ^ 40 * 3425061 * 2
def baseEnd_3425061 : Nat := 586234187989709722261979

theorem tailTrace_3425061 : CollatzResearch.WordTrace tailWord_3425061 prefixEnd_3425061 586234187989709722261979 := by
  unfold tailWord_3425061
  simp only [CollatzResearch.WordTrace]
  refine ⟨124922237444596425693355037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83281491629730950462236691 124922237444596425693355037)
  ·
    refine ⟨46845839041723659635008139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124922237444596425693355037 46845839041723659635008139)
    ·
      refine ⟨70268758562585489452512209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46845839041723659635008139 70268758562585489452512209)
      ·
        refine ⟨52701568921939117089384157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70268758562585489452512209 52701568921939117089384157)
        ·
          refine ⟨19763088345727168908519059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52701568921939117089384157 19763088345727168908519059)
          ·
            refine ⟨29644632518590753362778589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19763088345727168908519059 29644632518590753362778589)
            ·
              refine ⟨11116737194471532511041971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29644632518590753362778589 11116737194471532511041971)
              ·
                refine ⟨16675105791707298766562957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116737194471532511041971 16675105791707298766562957)
                ·
                  refine ⟨6253164671890237037461109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16675105791707298766562957 6253164671890237037461109)
                  ·
                    refine ⟨586234187989709722261979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6253164671890237037461109 586234187989709722261979)
                    ·
                      rfl

theorem cell23_3425061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_3425061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425061 prefixEnd_3425061 := by exact prefixLift 3425061
  have htrace : WordTrace (prefixWord ++ tailWord_3425061) baseStart_3425061 baseEnd_3425061 := by
    simpa [prefixWord, tailWord_3425061, baseEnd_3425061] using wordTrace_append hprefix tailTrace_3425061
  have hstable : (prefixWord ++ tailWord_3425061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425061).length < 2 ^ (prefixWord ++ tailWord_3425061).sum := by decide
  have hdescent : baseEnd_3425061 < baseStart_3425061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425086 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3425086 : Nat := 118140960795 + 3425086 * 2 ^ 59
def prefixEnd_3425086 : Nat := 4983230072969 + 3 ^ 40 * 3425086 * 2
def baseEnd_3425086 : Nat := 586238466995163856324441

theorem tailTrace_3425086 : CollatzResearch.WordTrace tailWord_3425086 prefixEnd_3425086 586238466995163856324441 := by
  unfold tailWord_3425086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15615393658688231870376889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83282099513003903308676741 15615393658688231870376889)
  ·
    refine ⟨11711545244016173902782667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15615393658688231870376889 11711545244016173902782667)
    ·
      refine ⟨17567317866024260854174001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711545244016173902782667 17567317866024260854174001)
      ·
        refine ⟨13175488399518195640630501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17567317866024260854174001 13175488399518195640630501)
        ·
          refine ⟨2470404074909661682618219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13175488399518195640630501 2470404074909661682618219)
          ·
            refine ⟨3705606112364492523927329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470404074909661682618219 3705606112364492523927329)
            ·
              refine ⟨2779204584273369392945497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3705606112364492523927329 2779204584273369392945497)
              ·
                refine ⟨2084403438205027044709123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779204584273369392945497 2084403438205027044709123)
                ·
                  refine ⟨3126605157307540567063685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084403438205027044709123 3126605157307540567063685)
                  ·
                    refine ⟨586238466995163856324441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126605157307540567063685 586238466995163856324441)
                    ·
                      rfl

theorem cell23_3425086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3425086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425086 prefixEnd_3425086 := by exact prefixLift 3425086
  have htrace : WordTrace (prefixWord ++ tailWord_3425086) baseStart_3425086 baseEnd_3425086 := by
    simpa [prefixWord, tailWord_3425086, baseEnd_3425086] using wordTrace_append hprefix tailTrace_3425086
  have hstable : (prefixWord ++ tailWord_3425086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425086).length < 2 ^ (prefixWord ++ tailWord_3425086).sum := by decide
  have hdescent : baseEnd_3425086 < baseStart_3425086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425128 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3425128 : Nat := 118140960795 + 3425128 * 2 ^ 59
def prefixEnd_3425128 : Nat := 4983230072969 + 3 ^ 40 * 3425128 * 2
def baseEnd_3425128 : Nat := 1758736967172980404648129

theorem tailTrace_3425128 : CollatzResearch.WordTrace tailWord_3425128 prefixEnd_3425128 1758736967172980404648129 := by
  unfold tailWord_3425128
  simp only [CollatzResearch.WordTrace]
  refine ⟨62462340567676848068022019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83283120756902464090696025 62462340567676848068022019)
  ·
    refine ⟨93693510851515272102033029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62462340567676848068022019 93693510851515272102033029)
    ·
      refine ⟨17567533284659113519131193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93693510851515272102033029 17567533284659113519131193)
      ·
        refine ⟨13175649963494335139348395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17567533284659113519131193 13175649963494335139348395)
        ·
          refine ⟨19763474945241502709022593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13175649963494335139348395 19763474945241502709022593)
          ·
            refine ⟨14822606208931127031766945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19763474945241502709022593 14822606208931127031766945)
            ·
              refine ⟨11116954656698345273825209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14822606208931127031766945 11116954656698345273825209)
              ·
                refine ⟨8337715992523758955368907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116954656698345273825209 8337715992523758955368907)
                ·
                  refine ⟨12506573988785638433053361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8337715992523758955368907 12506573988785638433053361)
                  ·
                    refine ⟨9379930491589228824790021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12506573988785638433053361 9379930491589228824790021)
                    ·
                      refine ⟨1758736967172980404648129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9379930491589228824790021 1758736967172980404648129)
                      ·
                        rfl

theorem cell23_3425128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3425128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425128 prefixEnd_3425128 := by exact prefixLift 3425128
  have htrace : WordTrace (prefixWord ++ tailWord_3425128) baseStart_3425128 baseEnd_3425128 := by
    simpa [prefixWord, tailWord_3425128, baseEnd_3425128] using wordTrace_append hprefix tailTrace_3425128
  have hstable : (prefixWord ++ tailWord_3425128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425128).length < 2 ^ (prefixWord ++ tailWord_3425128).sum := by decide
  have hdescent : baseEnd_3425128 < baseStart_3425128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425142 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_3425142 : Nat := 118140960795 + 3425142 * 2 ^ 59
def prefixEnd_3425142 : Nat := 4983230072969 + 3 ^ 40 * 3425142 * 2
def baseEnd_3425142 : Nat := 586248051967381116624355

theorem tailTrace_3425142 : CollatzResearch.WordTrace tailWord_3425142 prefixEnd_3425142 586248051967381116624355 := by
  unfold tailWord_3425142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807824484831436032940855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83283461171535317684702453 7807824484831436032940855)
  ·
    refine ⟨11711736727247154049411283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7807824484831436032940855 11711736727247154049411283)
    ·
      refine ⟨17567605090870731074116925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711736727247154049411283 17567605090870731074116925)
      ·
        refine ⟨6587851909076524152793847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17567605090870731074116925 6587851909076524152793847)
        ·
          refine ⟨9881777863614786229190771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587851909076524152793847 9881777863614786229190771)
          ·
            refine ⟨14822666795422179343786157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881777863614786229190771 14822666795422179343786157)
            ·
              refine ⟨5558500048283317253919809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14822666795422179343786157 5558500048283317253919809)
              ·
                refine ⟨4168875036212487940439857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558500048283317253919809 4168875036212487940439857)
                ·
                  refine ⟨3126656277159365955329893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168875036212487940439857 3126656277159365955329893)
                  ·
                    refine ⟨586248051967381116624355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126656277159365955329893 586248051967381116624355)
                    ·
                      rfl

theorem cell23_3425142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_3425142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425142 prefixEnd_3425142 := by exact prefixLift 3425142
  have htrace : WordTrace (prefixWord ++ tailWord_3425142) baseStart_3425142 baseEnd_3425142 := by
    simpa [prefixWord, tailWord_3425142, baseEnd_3425142] using wordTrace_append hprefix tailTrace_3425142
  have hstable : (prefixWord ++ tailWord_3425142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425142).length < 2 ^ (prefixWord ++ tailWord_3425142).sum := by decide
  have hdescent : baseEnd_3425142 < baseStart_3425142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425262 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_3425262 : Nat := 118140960795 + 3425262 * 2 ^ 59
def prefixEnd_3425262 : Nat := 4983230072969 + 3 ^ 40 * 3425262 * 2
def baseEnd_3425262 : Nat := 195422863731186986708057

theorem tailTrace_3425262 : CollatzResearch.WordTrace tailWord_3425262 prefixEnd_3425262 195422863731186986708057 := by
  unfold tailWord_3425262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15616196064608529627677755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83286379011245491347614693 15616196064608529627677755)
  ·
    refine ⟨23424294096912794441516633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15616196064608529627677755 23424294096912794441516633)
    ·
      refine ⟨17568220572684595831137475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23424294096912794441516633 17568220572684595831137475)
      ·
        refine ⟨26352330859026893746706213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17568220572684595831137475 26352330859026893746706213)
        ·
          refine ⟨4941062036067542577507415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26352330859026893746706213 4941062036067542577507415)
          ·
            refine ⟨7411593054101313866261123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941062036067542577507415 7411593054101313866261123)
            ·
              refine ⟨11117389581151970799391685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411593054101313866261123 11117389581151970799391685)
              ·
                refine ⟨2084510546465994524885941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11117389581151970799391685 2084510546465994524885941)
                ·
                  refine ⟨195422863731186986708057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2084510546465994524885941 195422863731186986708057)
                  ·
                    rfl

theorem cell23_3425262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_3425262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425262 prefixEnd_3425262 := by exact prefixLift 3425262
  have htrace : WordTrace (prefixWord ++ tailWord_3425262) baseStart_3425262 baseEnd_3425262 := by
    simpa [prefixWord, tailWord_3425262, baseEnd_3425262] using wordTrace_append hprefix tailTrace_3425262
  have hstable : (prefixWord ++ tailWord_3425262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425262).length < 2 ^ (prefixWord ++ tailWord_3425262).sum := by decide
  have hdescent : baseEnd_3425262 < baseStart_3425262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425265 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_3425265 : Nat := 118140960795 + 3425265 * 2 ^ 59
def prefixEnd_3425265 : Nat := 4983230072969 + 3 ^ 40 * 3425265 * 2
def baseEnd_3425265 : Nat := 1758807314022646368634999

theorem tailTrace_3425265 : CollatzResearch.WordTrace tailWord_3425265 prefixEnd_3425265 1758807314022646368634999 := by
  unfold tailWord_3425265
  simp only [CollatzResearch.WordTrace]
  refine ⟨124929677935857368533781249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83286451957238245689187499 124929677935857368533781249)
  ·
    refine ⟨93697258451893026400335937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124929677935857368533781249 93697258451893026400335937)
    ·
      refine ⟨70272943838919769800251953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93697258451893026400335937 70272943838919769800251953)
      ·
        refine ⟨52704707879189827350188965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70272943838919769800251953 52704707879189827350188965)
        ·
          refine ⟨9882132727348092628160431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52704707879189827350188965 9882132727348092628160431)
          ·
            refine ⟨14823199091022138942240647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882132727348092628160431 14823199091022138942240647)
            ·
              refine ⟨22234798636533208413360971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14823199091022138942240647 22234798636533208413360971)
              ·
                refine ⟨33352197954799812620041457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22234798636533208413360971 33352197954799812620041457)
                ·
                  refine ⟨25014148466099859465031093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33352197954799812620041457 25014148466099859465031093)
                  ·
                    refine ⟨2345076418696861824846665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25014148466099859465031093 2345076418696861824846665)
                    ·
                      refine ⟨1758807314022646368634999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345076418696861824846665 1758807314022646368634999)
                      ·
                        rfl

theorem cell23_3425265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_3425265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425265 prefixEnd_3425265 := by exact prefixLift 3425265
  have htrace : WordTrace (prefixWord ++ tailWord_3425265) baseStart_3425265 baseEnd_3425265 := by
    simpa [prefixWord, tailWord_3425265, baseEnd_3425265] using wordTrace_append hprefix tailTrace_3425265
  have hstable : (prefixWord ++ tailWord_3425265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425265).length < 2 ^ (prefixWord ++ tailWord_3425265).sum := by decide
  have hdescent : baseEnd_3425265 < baseStart_3425265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425332 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3425332 : Nat := 118140960795 + 3425332 * 2 ^ 59
def prefixEnd_3425332 : Nat := 4983230072969 + 3 ^ 40 * 3425332 * 2
def baseEnd_3425332 : Nat := 1758841717226497606497191

theorem tailTrace_3425332 : CollatzResearch.WordTrace tailWord_3425332 prefixEnd_3425332 1758841717226497606497191 := by
  unfold tailWord_3425332
  simp only [CollatzResearch.WordTrace]
  refine ⟨62466060813307319488235125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83288081084409759317646833 62466060813307319488235125)
  ·
    refine ⟨5856193201247561202022043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62466060813307319488235125 5856193201247561202022043)
    ·
      refine ⟨8784289801871341803033065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856193201247561202022043 8784289801871341803033065)
      ·
        refine ⟨6588217351403506352274799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8784289801871341803033065 6588217351403506352274799)
        ·
          refine ⟨9882326027105259528412199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588217351403506352274799 9882326027105259528412199)
          ·
            refine ⟨14823489040657889292618299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882326027105259528412199 14823489040657889292618299)
            ·
              refine ⟨22235233560986833938927449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14823489040657889292618299 22235233560986833938927449)
              ·
                refine ⟨16676425170740125454195587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22235233560986833938927449 16676425170740125454195587)
                ·
                  refine ⟨25014637756110188181293381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16676425170740125454195587 25014637756110188181293381)
                  ·
                    refine ⟨4690244579270660283992509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25014637756110188181293381 4690244579270660283992509)
                    ·
                      refine ⟨1758841717226497606497191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4690244579270660283992509 1758841717226497606497191)
                      ·
                        rfl

theorem cell23_3425332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3425332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425332 prefixEnd_3425332 := by exact prefixLift 3425332
  have htrace : WordTrace (prefixWord ++ tailWord_3425332) baseStart_3425332 baseEnd_3425332 := by
    simpa [prefixWord, tailWord_3425332, baseEnd_3425332] using wordTrace_append hprefix tailTrace_3425332
  have hstable : (prefixWord ++ tailWord_3425332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425332).length < 2 ^ (prefixWord ++ tailWord_3425332).sum := by decide
  have hdescent : baseEnd_3425332 < baseStart_3425332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425365 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3425365 : Nat := 118140960795 + 3425365 * 2 ^ 59
def prefixEnd_3425365 : Nat := 4983230072969 + 3 ^ 40 * 3425365 * 2
def baseEnd_3425365 : Nat := 586286220696031992461513

theorem tailTrace_3425365 : CollatzResearch.WordTrace tailWord_3425365 prefixEnd_3425365 586286220696031992461513 := by
  unfold tailWord_3425365
  simp only [CollatzResearch.WordTrace]
  refine ⟨124933325235495085612421549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83288883490330057074947699 124933325235495085612421549)
  ·
    refine ⟨46849996963310657104658081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124933325235495085612421549 46849996963310657104658081)
    ·
      refine ⟨35137497722482992828493561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46849996963310657104658081 35137497722482992828493561)
      ·
        refine ⟨26353123291862244621370171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35137497722482992828493561 26353123291862244621370171)
        ·
          refine ⟨39529684937793366932055257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26353123291862244621370171 39529684937793366932055257)
          ·
            refine ⟨29647263703345025199041443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39529684937793366932055257 29647263703345025199041443)
            ·
              refine ⟨44470895555017537798562165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29647263703345025199041443 44470895555017537798562165)
              ·
                refine ⟨4169146458282894168615203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44470895555017537798562165 4169146458282894168615203)
                ·
                  refine ⟨6253719687424341252922805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169146458282894168615203 6253719687424341252922805)
                  ·
                    refine ⟨586286220696031992461513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6253719687424341252922805 586286220696031992461513)
                    ·
                      rfl

theorem cell23_3425365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3425365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425365 prefixEnd_3425365 := by exact prefixLift 3425365
  have htrace : WordTrace (prefixWord ++ tailWord_3425365) baseStart_3425365 baseEnd_3425365 := by
    simpa [prefixWord, tailWord_3425365, baseEnd_3425365] using wordTrace_append hprefix tailTrace_3425365
  have hstable : (prefixWord ++ tailWord_3425365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425365).length < 2 ^ (prefixWord ++ tailWord_3425365).sum := by decide
  have hdescent : baseEnd_3425365 < baseStart_3425365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425366 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3425366 : Nat := 118140960795 + 3425366 * 2 ^ 59
def prefixEnd_3425366 : Nat := 4983230072969 + 3 ^ 40 * 3425366 * 2
def baseEnd_3425366 : Nat := 1758859175568750473472035

theorem tailTrace_3425366 : CollatzResearch.WordTrace tailWord_3425366 prefixEnd_3425366 1758859175568750473472035 := by
  unfold tailWord_3425366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808335106780716423950497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83288907805660975188805301 7808335106780716423950497)
  ·
    refine ⟨5856251330085537317962873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7808335106780716423950497 5856251330085537317962873)
    ·
      refine ⟨4392188497564152988472155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5856251330085537317962873 4392188497564152988472155)
      ·
        refine ⟨6588282746346229482708233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392188497564152988472155 6588282746346229482708233)
        ·
          refine ⟨4941212059759672112031175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6588282746346229482708233 4941212059759672112031175)
          ·
            refine ⟨7411818089639508168046763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941212059759672112031175 7411818089639508168046763)
            ·
              refine ⟨11117727134459262252070145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411818089639508168046763 11117727134459262252070145)
              ·
                refine ⟨8338295350844446689052609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11117727134459262252070145 8338295350844446689052609)
                ·
                  refine ⟨6253721513133335016789457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8338295350844446689052609 6253721513133335016789457)
                  ·
                    refine ⟨4690291134850001262592093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253721513133335016789457 4690291134850001262592093)
                    ·
                      refine ⟨1758859175568750473472035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4690291134850001262592093 1758859175568750473472035)
                      ·
                        rfl

theorem cell23_3425366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3425366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425366 prefixEnd_3425366 := by exact prefixLift 3425366
  have htrace : WordTrace (prefixWord ++ tailWord_3425366) baseStart_3425366 baseEnd_3425366 := by
    simpa [prefixWord, tailWord_3425366, baseEnd_3425366] using wordTrace_append hprefix tailTrace_3425366
  have hstable : (prefixWord ++ tailWord_3425366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425366).length < 2 ^ (prefixWord ++ tailWord_3425366).sum := by decide
  have hdescent : baseEnd_3425366 < baseStart_3425366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425373 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3425373 : Nat := 118140960795 + 3425373 * 2 ^ 59
def prefixEnd_3425373 : Nat := 4983230072969 + 3 ^ 40 * 3425373 * 2
def baseEnd_3425373 : Nat := 586287589977777315361501

theorem tailTrace_3425373 : CollatzResearch.WordTrace tailWord_3425373 prefixEnd_3425373 586287589977777315361501 := by
  unfold tailWord_3425373
  simp only [CollatzResearch.WordTrace]
  refine ⟨124933617019466102978712773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83289078012977401985808515 124933617019466102978712773)
  ·
    refine ⟨23425053191149894308508645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124933617019466102978712773 23425053191149894308508645)
    ·
      refine ⟨4392197473340605182845371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23425053191149894308508645 4392197473340605182845371)
      ·
        refine ⟨6588296210010907774268057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392197473340605182845371 6588296210010907774268057)
        ·
          refine ⟨4941222157508180830701043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6588296210010907774268057 4941222157508180830701043)
          ·
            refine ⟨7411833236262271246051565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941222157508180830701043 7411833236262271246051565)
            ·
              refine ⟨2779437463598351717269337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7411833236262271246051565 2779437463598351717269337)
              ·
                refine ⟨2084578097698763787952003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779437463598351717269337 2084578097698763787952003)
                ·
                  refine ⟨3126867146548145681928005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084578097698763787952003 3126867146548145681928005)
                  ·
                    refine ⟨586287589977777315361501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126867146548145681928005 586287589977777315361501)
                    ·
                      rfl

theorem cell23_3425373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3425373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425373 prefixEnd_3425373 := by exact prefixLift 3425373
  have htrace : WordTrace (prefixWord ++ tailWord_3425373) baseStart_3425373 baseEnd_3425373 := by
    simpa [prefixWord, tailWord_3425373, baseEnd_3425373] using wordTrace_append hprefix tailTrace_3425373
  have hstable : (prefixWord ++ tailWord_3425373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425373).length < 2 ^ (prefixWord ++ tailWord_3425373).sum := by decide
  have hdescent : baseEnd_3425373 < baseStart_3425373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425408 : List Nat := [2, 1, 1, 2, 1, 3, 4, 9]
def baseStart_3425408 : Nat := 118140960795 + 3425408 * 2 ^ 59
def prefixEnd_3425408 : Nat := 4983230072969 + 3 ^ 40 * 3425408 * 2
def baseEnd_3425408 : Nat := 65143731176157011449883

theorem tailTrace_3425408 : CollatzResearch.WordTrace tailWord_3425408 prefixEnd_3425408 65143731176157011449883 := by
  unfold tailWord_3425408
  simp only [CollatzResearch.WordTrace]
  refine ⟨62467446787169651978118439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83289929049559535970824585 62467446787169651978118439)
  ·
    refine ⟨93701170180754477967177659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62467446787169651978118439 93701170180754477967177659)
    ·
      refine ⟨140551755271131716950766489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93701170180754477967177659 140551755271131716950766489)
      ·
        refine ⟨105413816453348787713074867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140551755271131716950766489 105413816453348787713074867)
        ·
          refine ⟨158120724680023181569612301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105413816453348787713074867 158120724680023181569612301)
          ·
            refine ⟨59295271755008693088604613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158120724680023181569612301 59295271755008693088604613)
            ·
              refine ⟨11117863454064129954113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59295271755008693088604613 11117863454064129954113365)
              ·
                refine ⟨65143731176157011449883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11117863454064129954113365 65143731176157011449883)
                ·
                  rfl

theorem cell23_3425408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 9].length) (baseStart_3425408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425408 prefixEnd_3425408 := by exact prefixLift 3425408
  have htrace : WordTrace (prefixWord ++ tailWord_3425408) baseStart_3425408 baseEnd_3425408 := by
    simpa [prefixWord, tailWord_3425408, baseEnd_3425408] using wordTrace_append hprefix tailTrace_3425408
  have hstable : (prefixWord ++ tailWord_3425408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425408).length < 2 ^ (prefixWord ++ tailWord_3425408).sum := by decide
  have hdescent : baseEnd_3425408 < baseStart_3425408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425422 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_3425422 : Nat := 118140960795 + 3425422 * 2 ^ 59
def prefixEnd_3425422 : Nat := 4983230072969 + 3 ^ 40 * 3425422 * 2
def baseEnd_3425422 : Nat := 1758887930485402254371777

theorem tailTrace_3425422 : CollatzResearch.WordTrace tailWord_3425422 prefixEnd_3425422 1758887930485402254371777 := by
  unfold tailWord_3425422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15616925524536073043405815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83290269464192389564831013 15616925524536073043405815)
  ·
    refine ⟨23425388286804109565108723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15616925524536073043405815 23425388286804109565108723)
    ·
      refine ⟨35138082430206164347663085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23425388286804109565108723 35138082430206164347663085)
      ·
        refine ⟨13176780911327311630373657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35138082430206164347663085 13176780911327311630373657)
        ·
          refine ⟨9882585683495483722780243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13176780911327311630373657 9882585683495483722780243)
          ·
            refine ⟨14823878525243225584170365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9882585683495483722780243 14823878525243225584170365)
            ·
              refine ⟨5558954446966209594063887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14823878525243225584170365 5558954446966209594063887)
              ·
                refine ⟨8338431670449314391095831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558954446966209594063887 8338431670449314391095831)
                ·
                  refine ⟨12507647505673971586643747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8338431670449314391095831 12507647505673971586643747)
                  ·
                    refine ⟨18761471258510957379965621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12507647505673971586643747 18761471258510957379965621)
                    ·
                      refine ⟨1758887930485402254371777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18761471258510957379965621 1758887930485402254371777)
                      ·
                        rfl

theorem cell23_3425422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_3425422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425422 prefixEnd_3425422 := by exact prefixLift 3425422
  have htrace : WordTrace (prefixWord ++ tailWord_3425422) baseStart_3425422 baseEnd_3425422 := by
    simpa [prefixWord, tailWord_3425422, baseEnd_3425422] using wordTrace_append hprefix tailTrace_3425422
  have hstable : (prefixWord ++ tailWord_3425422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425422).length < 2 ^ (prefixWord ++ tailWord_3425422).sum := by decide
  have hdescent : baseEnd_3425422 < baseStart_3425422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425473 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3425473 : Nat := 118140960795 + 3425473 * 2 ^ 59
def prefixEnd_3425473 : Nat := 4983230072969 + 3 ^ 40 * 3425473 * 2
def baseEnd_3425473 : Nat := 1758914117998781554834043

theorem tailTrace_3425473 : CollatzResearch.WordTrace tailWord_3425473 prefixEnd_3425473 1758914117998781554834043 := by
  unfold tailWord_3425473
  simp only [CollatzResearch.WordTrace]
  refine ⟨124937264319103820057353073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83291509546069213371568715 124937264319103820057353073)
  ·
    refine ⟨93702948239327865043014805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124937264319103820057353073 93702948239327865043014805)
    ·
      refine ⟨4392325698718493673891319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93702948239327865043014805 4392325698718493673891319)
      ·
        refine ⟨6588488548077740510836979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392325698718493673891319 6588488548077740510836979)
        ·
          refine ⟨9882732822116610766255469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588488548077740510836979 9882732822116610766255469)
          ·
            refine ⟨3706024808293729037345801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9882732822116610766255469 3706024808293729037345801)
            ·
              refine ⟨2779518606220296778009351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706024808293729037345801 2779518606220296778009351)
              ·
                refine ⟨4169277909330445167014027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779518606220296778009351 4169277909330445167014027)
                ·
                  refine ⟨6253916863995667750521041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169277909330445167014027 6253916863995667750521041)
                  ·
                    refine ⟨4690437647996750812890781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253916863995667750521041 4690437647996750812890781)
                    ·
                      refine ⟨1758914117998781554834043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4690437647996750812890781 1758914117998781554834043)
                      ·
                        rfl

theorem cell23_3425473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3425473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425473 prefixEnd_3425473 := by exact prefixLift 3425473
  have htrace : WordTrace (prefixWord ++ tailWord_3425473) baseStart_3425473 baseEnd_3425473 := by
    simpa [prefixWord, tailWord_3425473, baseEnd_3425473] using wordTrace_append hprefix tailTrace_3425473
  have hstable : (prefixWord ++ tailWord_3425473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425473).length < 2 ^ (prefixWord ++ tailWord_3425473).sum := by decide
  have hdescent : baseEnd_3425473 < baseStart_3425473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425495 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_3425495 : Nat := 118140960795 + 3425495 * 2 ^ 59
def prefixEnd_3425495 : Nat := 4983230072969 + 3 ^ 40 * 3425495 * 2
def baseEnd_3425495 : Nat := 1758925414573180468758941

theorem tailTrace_3425495 : CollatzResearch.WordTrace tailWord_3425495 prefixEnd_3425495 1758925414573180468758941 := by
  unfold tailWord_3425495
  simp only [CollatzResearch.WordTrace]
  refine ⟨124938066725024117814653939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83292044483349411876435959 124938066725024117814653939)
  ·
    refine ⟨187407100087536176721980909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124938066725024117814653939 187407100087536176721980909)
    ·
      refine ⟨70277662532826066270742841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187407100087536176721980909 70277662532826066270742841)
      ·
        refine ⟨52708246899619549703057131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70277662532826066270742841 52708246899619549703057131)
        ·
          refine ⟨79062370349429324554585697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52708246899619549703057131 79062370349429324554585697)
          ·
            refine ⟨59296777762071993415939273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79062370349429324554585697 59296777762071993415939273)
            ·
              refine ⟨44472583321553995061954455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59296777762071993415939273 44472583321553995061954455)
              ·
                refine ⟨66708874982330992592931683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44472583321553995061954455 66708874982330992592931683)
                ·
                  refine ⟨100063312473496488889397525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66708874982330992592931683 100063312473496488889397525)
                  ·
                    refine ⟨4690467772195147916690509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100063312473496488889397525 4690467772195147916690509)
                    ·
                      refine ⟨1758925414573180468758941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4690467772195147916690509 1758925414573180468758941)
                      ·
                        rfl

theorem cell23_3425495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3425495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425495 prefixEnd_3425495 := by exact prefixLift 3425495
  have htrace : WordTrace (prefixWord ++ tailWord_3425495) baseStart_3425495 baseEnd_3425495 := by
    simpa [prefixWord, tailWord_3425495, baseEnd_3425495] using wordTrace_append hprefix tailTrace_3425495
  have hstable : (prefixWord ++ tailWord_3425495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425495).length < 2 ^ (prefixWord ++ tailWord_3425495).sum := by decide
  have hdescent : baseEnd_3425495 < baseStart_3425495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425515 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 7]
def baseStart_3425515 : Nat := 118140960795 + 3425515 * 2 ^ 59
def prefixEnd_3425515 : Nat := 4983230072969 + 3 ^ 40 * 3425515 * 2
def baseEnd_3425515 : Nat := 195437298242918932278761

theorem tailTrace_3425515 : CollatzResearch.WordTrace tailWord_3425515 prefixEnd_3425515 195437298242918932278761 := by
  unfold tailWord_3425515
  simp only [CollatzResearch.WordTrace]
  refine ⟨124938796184951661230381999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83292530789967774153587999 124938796184951661230381999)
  ·
    refine ⟨187408194277427491845572999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124938796184951661230381999 187408194277427491845572999)
    ·
      refine ⟨281112291416141237768359499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187408194277427491845572999 281112291416141237768359499)
      ·
        refine ⟨421668437124211856652539249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281112291416141237768359499 421668437124211856652539249)
        ·
          refine ⟨316251327843158892489404437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421668437124211856652539249 316251327843158892489404437)
          ·
            refine ⟨14824280992648073085440833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316251327843158892489404437 14824280992648073085440833)
            ·
              refine ⟨11118210744486054814080625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14824280992648073085440833 11118210744486054814080625)
              ·
                refine ⟨8338658058364541110560469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11118210744486054814080625 8338658058364541110560469)
                ·
                  refine ⟨195437298242918932278761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8338658058364541110560469 195437298242918932278761)
                  ·
                    rfl

theorem cell23_3425515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 7].length) (baseStart_3425515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425515 prefixEnd_3425515 := by exact prefixLift 3425515
  have htrace : WordTrace (prefixWord ++ tailWord_3425515) baseStart_3425515 baseEnd_3425515 := by
    simpa [prefixWord, tailWord_3425515, baseEnd_3425515] using wordTrace_append hprefix tailTrace_3425515
  have hstable : (prefixWord ++ tailWord_3425515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425515).length < 2 ^ (prefixWord ++ tailWord_3425515).sum := by decide
  have hdescent : baseEnd_3425515 < baseStart_3425515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425595 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_3425595 : Nat := 118140960795 + 3425595 * 2 ^ 59
def prefixEnd_3425595 : Nat := 4983230072969 + 3 ^ 40 * 3425595 * 2
def baseEnd_3425595 : Nat := 1758976762638630077508481

theorem tailTrace_3425595 : CollatzResearch.WordTrace tailWord_3425595 prefixEnd_3425595 1758976762638630077508481 := by
  unfold tailWord_3425595
  simp only [CollatzResearch.WordTrace]
  refine ⟨124941714024661834893294239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83294476016441223262196159 124941714024661834893294239)
  ·
    refine ⟨187412571036992752339941359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124941714024661834893294239 187412571036992752339941359)
    ·
      refine ⟨281118856555489128509912039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187412571036992752339941359 281118856555489128509912039)
      ·
        refine ⟨421678284833233692764868059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281118856555489128509912039 421678284833233692764868059)
        ·
          refine ⟨632517427249850539147302089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421678284833233692764868059 632517427249850539147302089)
          ·
            refine ⟨474388070437387904360476567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632517427249850539147302089 474388070437387904360476567)
            ·
              refine ⟨711582105656081856540714851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474388070437387904360476567 711582105656081856540714851)
              ·
                refine ⟨1067373158484122784811072277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711582105656081856540714851 1067373158484122784811072277)
                ·
                  refine ⟨50033116803943255538019013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1067373158484122784811072277 50033116803943255538019013)
                  ·
                    refine ⟨9381209400739360413378565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50033116803943255538019013 9381209400739360413378565)
                    ·
                      refine ⟨1758976762638630077508481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9381209400739360413378565 1758976762638630077508481)
                      ·
                        rfl

theorem cell23_3425595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_3425595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425595 prefixEnd_3425595 := by exact prefixLift 3425595
  have htrace : WordTrace (prefixWord ++ tailWord_3425595) baseStart_3425595 baseEnd_3425595 := by
    simpa [prefixWord, tailWord_3425595, baseEnd_3425595] using wordTrace_append hprefix tailTrace_3425595
  have hstable : (prefixWord ++ tailWord_3425595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425595).length < 2 ^ (prefixWord ++ tailWord_3425595).sum := by decide
  have hdescent : baseEnd_3425595 < baseStart_3425595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425605 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 8]
def baseStart_3425605 : Nat := 118140960795 + 3425605 * 2 ^ 59
def prefixEnd_3425605 : Nat := 4983230072969 + 3 ^ 40 * 3425605 * 2
def baseEnd_3425605 : Nat := 195442433049463893153715

theorem tailTrace_3425605 : CollatzResearch.WordTrace tailWord_3425605 prefixEnd_3425605 195442433049463893153715 := by
  unfold tailWord_3425605
  simp only [CollatzResearch.WordTrace]
  refine ⟨124942078754625606601158269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83294719169750404400772179 124942078754625606601158269)
  ·
    refine ⟨46853279532984602475434351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124942078754625606601158269 46853279532984602475434351)
    ·
      refine ⟨70279919299476903713151527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46853279532984602475434351 70279919299476903713151527)
      ·
        refine ⟨105419878949215355569727291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70279919299476903713151527 105419878949215355569727291)
        ·
          refine ⟨158129818423823033354590937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105419878949215355569727291 158129818423823033354590937)
          ·
            refine ⟨118597363817867275015943203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158129818423823033354590937 118597363817867275015943203)
            ·
              refine ⟨177896045726800912523914805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118597363817867275015943203 177896045726800912523914805)
              ·
                refine ⟨16677754286887585549117013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177896045726800912523914805 16677754286887585549117013)
                ·
                  refine ⟨195442433049463893153715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16677754286887585549117013 195442433049463893153715)
                  ·
                    rfl

theorem cell23_3425605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_3425605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425605 prefixEnd_3425605 := by exact prefixLift 3425605
  have htrace : WordTrace (prefixWord ++ tailWord_3425605) baseStart_3425605 baseEnd_3425605 := by
    simpa [prefixWord, tailWord_3425605, baseEnd_3425605] using wordTrace_append hprefix tailTrace_3425605
  have hstable : (prefixWord ++ tailWord_3425605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425605).length < 2 ^ (prefixWord ++ tailWord_3425605).sum := by decide
  have hdescent : baseEnd_3425605 < baseStart_3425605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425636 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 2, 2, 3]
def baseStart_3425636 : Nat := 118140960795 + 3425636 * 2 ^ 59
def prefixEnd_3425636 : Nat := 4983230072969 + 3 ^ 40 * 3425636 * 2
def baseEnd_3425636 : Nat := 1758997815345464417095793

theorem tailTrace_3425636 : CollatzResearch.WordTrace tailWord_3425636 prefixEnd_3425636 1758997815345464417095793 := by
  unfold tailWord_3425636
  simp only [CollatzResearch.WordTrace]
  refine ⟨62471604708756649447768381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83295472945008865930357841 62471604708756649447768381)
  ·
    refine ⟨23426851765783743542913143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62471604708756649447768381 23426851765783743542913143)
    ·
      refine ⟨35140277648675615314369715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23426851765783743542913143 35140277648675615314369715)
      ·
        refine ⟨52710416473013422971554573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35140277648675615314369715 52710416473013422971554573)
        ·
          refine ⟨19766406177380033614332965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52710416473013422971554573 19766406177380033614332965)
          ·
            refine ⟨3706201158258756302687431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19766406177380033614332965 3706201158258756302687431)
            ·
              refine ⟨5559301737388134454031147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706201158258756302687431 5559301737388134454031147)
              ·
                refine ⟨8338952606082201681046721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559301737388134454031147 8338952606082201681046721)
                ·
                  refine ⟨6254214454561651260785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8338952606082201681046721 6254214454561651260785041)
                  ·
                    refine ⟨4690660840921238445588781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254214454561651260785041 4690660840921238445588781)
                    ·
                      refine ⟨1758997815345464417095793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4690660840921238445588781 1758997815345464417095793)
                      ·
                        rfl

theorem cell23_3425636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_3425636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425636 prefixEnd_3425636 := by exact prefixLift 3425636
  have htrace : WordTrace (prefixWord ++ tailWord_3425636) baseStart_3425636 baseEnd_3425636 := by
    simpa [prefixWord, tailWord_3425636, baseEnd_3425636] using wordTrace_append hprefix tailTrace_3425636
  have hstable : (prefixWord ++ tailWord_3425636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425636).length < 2 ^ (prefixWord ++ tailWord_3425636).sum := by decide
  have hdescent : baseEnd_3425636 < baseStart_3425636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425659 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 4, 3, 2]
def baseStart_3425659 : Nat := 118140960795 + 3425659 * 2 ^ 59
def prefixEnd_3425659 : Nat := 4983230072969 + 3 ^ 40 * 3425659 * 2
def baseEnd_3425659 : Nat := 1759009625400517827108187

theorem tailTrace_3425659 : CollatzResearch.WordTrace tailWord_3425659 prefixEnd_3425659 1759009625400517827108187 := by
  unfold tailWord_3425659
  simp only [CollatzResearch.WordTrace]
  refine ⟨124944048296429973823624031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83296032197619982549082687 124944048296429973823624031)
  ·
    refine ⟨187416072444644960735436047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124944048296429973823624031 187416072444644960735436047)
    ·
      refine ⟨281124108666967441103154071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187416072444644960735436047 281124108666967441103154071)
      ·
        refine ⟨421686163000451161654731107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281124108666967441103154071 421686163000451161654731107)
        ·
          refine ⟨632529244500676742482096661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421686163000451161654731107 632529244500676742482096661)
          ·
            refine ⟨29649808335969222303848281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 632529244500676742482096661 29649808335969222303848281)
            ·
              refine ⟨22237356251976916727886211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29649808335969222303848281 22237356251976916727886211)
              ·
                refine ⟨33356034377965375091829317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22237356251976916727886211 33356034377965375091829317)
                ·
                  refine ⟨6254256445868507829717997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33356034377965375091829317 6254256445868507829717997)
                  ·
                    refine ⟨2345346167200690436144249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6254256445868507829717997 2345346167200690436144249)
                    ·
                      refine ⟨1759009625400517827108187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345346167200690436144249 1759009625400517827108187)
                      ·
                        rfl

theorem cell23_3425659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3, 2].length) (baseStart_3425659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425659 prefixEnd_3425659 := by exact prefixLift 3425659
  have htrace : WordTrace (prefixWord ++ tailWord_3425659) baseStart_3425659 baseEnd_3425659 := by
    simpa [prefixWord, tailWord_3425659, baseEnd_3425659] using wordTrace_append hprefix tailTrace_3425659
  have hstable : (prefixWord ++ tailWord_3425659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425659).length < 2 ^ (prefixWord ++ tailWord_3425659).sum := by decide
  have hdescent : baseEnd_3425659 < baseStart_3425659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425689 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_3425689 : Nat := 118140960795 + 3425689 * 2 ^ 59
def prefixEnd_3425689 : Nat := 4983230072969 + 3 ^ 40 * 3425689 * 2
def baseEnd_3425689 : Nat := 1759025029820152709733049

theorem tailTrace_3425689 : CollatzResearch.WordTrace tailWord_3425689 prefixEnd_3425689 1759025029820152709733049 := by
  unfold tailWord_3425689
  simp only [CollatzResearch.WordTrace]
  refine ⟨124945142486321288947216121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83296761657547525964810747 124945142486321288947216121)
  ·
    refine ⟨93708856864740966710412091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124945142486321288947216121 93708856864740966710412091)
    ·
      refine ⟨140563285297111450065618137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93708856864740966710412091 140563285297111450065618137)
      ·
        refine ⟨105422463972833587549213603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140563285297111450065618137 105422463972833587549213603)
        ·
          refine ⟨158133695959250381323820405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105422463972833587549213603 158133695959250381323820405)
          ·
            refine ⟨14825033996179723249108163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158133695959250381323820405 14825033996179723249108163)
            ·
              refine ⟨22237550994269584873662245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14825033996179723249108163 22237550994269584873662245)
              ·
                refine ⟨4169540811425547163811671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22237550994269584873662245 4169540811425547163811671)
                ·
                  refine ⟨6254311217138320745717507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169540811425547163811671 6254311217138320745717507)
                  ·
                    refine ⟨9381466825707481118576261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6254311217138320745717507 9381466825707481118576261)
                    ·
                      refine ⟨1759025029820152709733049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9381466825707481118576261 1759025029820152709733049)
                      ·
                        rfl

theorem cell23_3425689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_3425689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425689 prefixEnd_3425689 := by exact prefixLift 3425689
  have htrace : WordTrace (prefixWord ++ tailWord_3425689) baseStart_3425689 baseEnd_3425689 := by
    simpa [prefixWord, tailWord_3425689, baseEnd_3425689] using wordTrace_append hprefix tailTrace_3425689
  have hstable : (prefixWord ++ tailWord_3425689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425689).length < 2 ^ (prefixWord ++ tailWord_3425689).sum := by decide
  have hdescent : baseEnd_3425689 < baseStart_3425689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425752 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3425752 : Nat := 118140960795 + 3425752 * 2 ^ 59
def prefixEnd_3425752 : Nat := 4983230072969 + 3 ^ 40 * 3425752 * 2
def baseEnd_3425752 : Nat := 1759057379101385963245259

theorem tailTrace_3425752 : CollatzResearch.WordTrace tailWord_3425752 prefixEnd_3425752 1759057379101385963245259 := by
  unfold tailWord_3425752
  simp only [CollatzResearch.WordTrace]
  refine ⟨62473720142546525353379755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83298293523395367137839673 62473720142546525353379755)
  ·
    refine ⟨93710580213819788030069633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62473720142546525353379755 93710580213819788030069633)
    ·
      refine ⟨70282935160364841022552225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93710580213819788030069633 70282935160364841022552225)
      ·
        refine ⟨52712201370273630766914169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70282935160364841022552225 52712201370273630766914169)
        ·
          refine ⟨39534151027705223075185627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52712201370273630766914169 39534151027705223075185627)
          ·
            refine ⟨59301226541557834612778441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39534151027705223075185627 59301226541557834612778441)
            ·
              refine ⟨44475919906168375959583831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59301226541557834612778441 44475919906168375959583831)
              ·
                refine ⟨66713879859252563939375747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44475919906168375959583831 66713879859252563939375747)
                ·
                  refine ⟨100070819788878845909063621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66713879859252563939375747 100070819788878845909063621)
                  ·
                    refine ⟨18763278710414783607949429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100070819788878845909063621 18763278710414783607949429)
                    ·
                      refine ⟨1759057379101385963245259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18763278710414783607949429 1759057379101385963245259)
                      ·
                        rfl

theorem cell23_3425752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3425752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425752 prefixEnd_3425752 := by exact prefixLift 3425752
  have htrace : WordTrace (prefixWord ++ tailWord_3425752) baseStart_3425752 baseEnd_3425752 := by
    simpa [prefixWord, tailWord_3425752, baseEnd_3425752] using wordTrace_append hprefix tailTrace_3425752
  have hstable : (prefixWord ++ tailWord_3425752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425752).length < 2 ^ (prefixWord ++ tailWord_3425752).sum := by decide
  have hdescent : baseEnd_3425752 < baseStart_3425752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425789 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_3425789 : Nat := 118140960795 + 3425789 * 2 ^ 59
def prefixEnd_3425789 : Nat := 4983230072969 + 3 ^ 40 * 3425789 * 2
def baseEnd_3425789 : Nat := 586358792628534106160863

theorem tailTrace_3425789 : CollatzResearch.WordTrace tailWord_3425789 prefixEnd_3425789 586358792628534106160863 := by
  unfold tailWord_3425789
  simp only [CollatzResearch.WordTrace]
  refine ⟨124948789785959006025856421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83299193190639337350570947 124948789785959006025856421)
  ·
    refine ⟨23427898084867313629848079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124948789785959006025856421 23427898084867313629848079)
    ·
      refine ⟨35141847127300970444772119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23427898084867313629848079 35141847127300970444772119)
      ·
        refine ⟨52712770690951455667158179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35141847127300970444772119 52712770690951455667158179)
        ·
          refine ⟨79069156036427183500737269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52712770690951455667158179 79069156036427183500737269)
          ·
            refine ⟨7412733378415048453194119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79069156036427183500737269 7412733378415048453194119)
            ·
              refine ⟨11119100067622572679791179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7412733378415048453194119 11119100067622572679791179)
              ·
                refine ⟨16678650101433859019686769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11119100067622572679791179 16678650101433859019686769)
                ·
                  refine ⟨12508987576075394264765077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16678650101433859019686769 12508987576075394264765077)
                  ·
                    refine ⟨586358792628534106160863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12508987576075394264765077 586358792628534106160863)
                    ·
                      rfl

theorem cell23_3425789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_3425789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425789 prefixEnd_3425789 := by exact prefixLift 3425789
  have htrace : WordTrace (prefixWord ++ tailWord_3425789) baseStart_3425789 baseEnd_3425789 := by
    simpa [prefixWord, tailWord_3425789, baseEnd_3425789] using wordTrace_append hprefix tailTrace_3425789
  have hstable : (prefixWord ++ tailWord_3425789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425789).length < 2 ^ (prefixWord ++ tailWord_3425789).sum := by decide
  have hdescent : baseEnd_3425789 < baseStart_3425789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425790 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3425790 : Nat := 118140960795 + 3425790 * 2 ^ 59
def prefixEnd_3425790 : Nat := 4983230072969 + 3 ^ 40 * 3425790 * 2
def baseEnd_3425790 : Nat := 1759076891366256814570085

theorem tailTrace_3425790 : CollatzResearch.WordTrace tailWord_3425790 prefixEnd_3425790 1759076891366256814570085 := by
  unfold tailWord_3425790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15618603282369422899580353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83299217505970255464428549 15618603282369422899580353)
  ·
    refine ⟨11713952461777067174685265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15618603282369422899580353 11713952461777067174685265)
    ·
      refine ⟨8785464346332800381013949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11713952461777067174685265 8785464346332800381013949)
      ·
        refine ⟨3294549129874800142880231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8785464346332800381013949 3294549129874800142880231)
        ·
          refine ⟨4941823694812200214320347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294549129874800142880231 4941823694812200214320347)
          ·
            refine ⟨7412735542218300321480521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941823694812200214320347 7412735542218300321480521)
            ·
              refine ⟨5559551656663725241110391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7412735542218300321480521 5559551656663725241110391)
              ·
                refine ⟨8339327484995587861665587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559551656663725241110391 8339327484995587861665587)
                ·
                  refine ⟨12508991227493381792498381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8339327484995587861665587 12508991227493381792498381)
                  ·
                    refine ⟨4690871710310018172186893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12508991227493381792498381 4690871710310018172186893)
                    ·
                      refine ⟨1759076891366256814570085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4690871710310018172186893 1759076891366256814570085)
                      ·
                        rfl

theorem cell23_3425790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3425790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425790 prefixEnd_3425790 := by exact prefixLift 3425790
  have htrace : WordTrace (prefixWord ++ tailWord_3425790) baseStart_3425790 baseEnd_3425790 := by
    simpa [prefixWord, tailWord_3425790, baseEnd_3425790] using wordTrace_append hprefix tailTrace_3425790
  have hstable : (prefixWord ++ tailWord_3425790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425790).length < 2 ^ (prefixWord ++ tailWord_3425790).sum := by decide
  have hdescent : baseEnd_3425790 < baseStart_3425790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425849 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_3425849 : Nat := 118140960795 + 3425849 * 2 ^ 59
def prefixEnd_3425849 : Nat := 4983230072969 + 3 ^ 40 * 3425849 * 2
def baseEnd_3425849 : Nat := 586369062241624027910771

theorem tailTrace_3425849 : CollatzResearch.WordTrace tailWord_3425849 prefixEnd_3425849 586369062241624027910771 := by
  unfold tailWord_3425849
  simp only [CollatzResearch.WordTrace]
  refine ⟨124950978165741636273040601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83300652110494424182027067 124950978165741636273040601)
  ·
    refine ⟨93713233624306227204780451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124950978165741636273040601 93713233624306227204780451)
    ·
      refine ⟨140569850436459340807170677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93713233624306227204780451 140569850436459340807170677)
      ·
        refine ⟨13178423478418063200672251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140569850436459340807170677 13178423478418063200672251)
        ·
          refine ⟨19767635217627094801008377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13178423478418063200672251 19767635217627094801008377)
          ·
            refine ⟨14825726413220321100756283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19767635217627094801008377 14825726413220321100756283)
            ·
              refine ⟨22238589619830481651134425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14825726413220321100756283 22238589619830481651134425)
              ·
                refine ⟨16678942214872861238350819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22238589619830481651134425 16678942214872861238350819)
                ·
                  refine ⟨25018413322309291857526229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16678942214872861238350819 25018413322309291857526229)
                  ·
                    refine ⟨586369062241624027910771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25018413322309291857526229 586369062241624027910771)
                    ·
                      rfl

theorem cell23_3425849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_3425849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425849 prefixEnd_3425849 := by exact prefixLift 3425849
  have htrace : WordTrace (prefixWord ++ tailWord_3425849) baseStart_3425849 baseEnd_3425849 := by
    simpa [prefixWord, tailWord_3425849, baseEnd_3425849] using wordTrace_append hprefix tailTrace_3425849
  have hstable : (prefixWord ++ tailWord_3425849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425849).length < 2 ^ (prefixWord ++ tailWord_3425849).sum := by decide
  have hdescent : baseEnd_3425849 < baseStart_3425849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425939 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 7, 5]
def baseStart_3425939 : Nat := 118140960795 + 3425939 * 2 ^ 59
def prefixEnd_3425939 : Nat := 4983230072969 + 3 ^ 40 * 3425939 * 2
def baseEnd_3425939 : Nat := 586384466661258910535633

theorem tailTrace_3425939 : CollatzResearch.WordTrace tailWord_3425939 prefixEnd_3425939 586384466661258910535633 := by
  unfold tailWord_3425939
  simp only [CollatzResearch.WordTrace]
  refine ⟨124954260735415581643816871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83302840490277054429211247 124954260735415581643816871)
  ·
    refine ⟨187431391103123372465725307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124954260735415581643816871 187431391103123372465725307)
    ·
      refine ⟨281147086654685058698587961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187431391103123372465725307 281147086654685058698587961)
      ·
        refine ⟨210860314991013794023940971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281147086654685058698587961 210860314991013794023940971)
        ·
          refine ⟨316290472486520691035911457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210860314991013794023940971 316290472486520691035911457)
          ·
            refine ⟨237217854364890518276933593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316290472486520691035911457 237217854364890518276933593)
            ·
              refine ⟨177913390773667888707700195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237217854364890518276933593 177913390773667888707700195)
              ·
                refine ⟨266870086160501833061550293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177913390773667888707700195 266870086160501833061550293)
                ·
                  refine ⟨6254767644386761712380085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266870086160501833061550293 6254767644386761712380085)
                  ·
                    refine ⟨586384466661258910535633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6254767644386761712380085 586384466661258910535633)
                    ·
                      rfl

theorem cell23_3425939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 5].length) (baseStart_3425939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425939 prefixEnd_3425939 := by exact prefixLift 3425939
  have htrace : WordTrace (prefixWord ++ tailWord_3425939) baseStart_3425939 baseEnd_3425939 := by
    simpa [prefixWord, tailWord_3425939, baseEnd_3425939] using wordTrace_append hprefix tailTrace_3425939
  have hstable : (prefixWord ++ tailWord_3425939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425939).length < 2 ^ (prefixWord ++ tailWord_3425939).sum := by decide
  have hdescent : baseEnd_3425939 < baseStart_3425939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425956 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_3425956 : Nat := 118140960795 + 3425956 * 2 ^ 59
def prefixEnd_3425956 : Nat := 4983230072969 + 3 ^ 40 * 3425956 * 2
def baseEnd_3425956 : Nat := 586387376384967721698107

theorem tailTrace_3425956 : CollatzResearch.WordTrace tailWord_3425956 prefixEnd_3425956 586387376384967721698107 := by
  unfold tailWord_3425956
  simp only [CollatzResearch.WordTrace]
  refine ⟨62477440388176996773592861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83303253850902662364790481 62477440388176996773592861)
  ·
    refine ⟨23429040145566373790097323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62477440388176996773592861 23429040145566373790097323)
    ·
      refine ⟨35143560218349560685145985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429040145566373790097323 35143560218349560685145985)
      ·
        refine ⟨26357670163762170513859489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35143560218349560685145985 26357670163762170513859489)
        ·
          refine ⟨19768252622821627885394617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26357670163762170513859489 19768252622821627885394617)
          ·
            refine ⟨14826189467116220914045963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19768252622821627885394617 14826189467116220914045963)
            ·
              refine ⟨22239284200674331371068945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14826189467116220914045963 22239284200674331371068945)
              ·
                refine ⟨16679463150505748528301709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22239284200674331371068945 16679463150505748528301709)
                ·
                  refine ⟨6254798681439655698113141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16679463150505748528301709 6254798681439655698113141)
                  ·
                    refine ⟨586387376384967721698107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6254798681439655698113141 586387376384967721698107)
                    ·
                      rfl

theorem cell23_3425956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_3425956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425956 prefixEnd_3425956 := by exact prefixLift 3425956
  have htrace : WordTrace (prefixWord ++ tailWord_3425956) baseStart_3425956 baseEnd_3425956 := by
    simpa [prefixWord, tailWord_3425956, baseEnd_3425956] using wordTrace_append hprefix tailTrace_3425956
  have hstable : (prefixWord ++ tailWord_3425956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425956).length < 2 ^ (prefixWord ++ tailWord_3425956).sum := by decide
  have hdescent : baseEnd_3425956 < baseStart_3425956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3425980 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_3425980 : Nat := 118140960795 + 3425980 * 2 ^ 59
def prefixEnd_3425980 : Nat := 4983230072969 + 3 ^ 40 * 3425980 * 2
def baseEnd_3425980 : Nat := 1759174452690611071194211

theorem tailTrace_3425980 : CollatzResearch.WordTrace tailWord_3425980 prefixEnd_3425980 1759174452690611071194211 := by
  unfold tailWord_3425980
  simp only [CollatzResearch.WordTrace]
  refine ⟨62477878064133522823029697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83303837418844697097372929 62477878064133522823029697)
  ·
    refine ⟨46858408548100142117272273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62477878064133522823029697 46858408548100142117272273)
    ·
      refine ⟨35143806411075106587954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46858408548100142117272273 35143806411075106587954205)
      ·
        refine ⟨13178927404153164970482827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35143806411075106587954205 13178927404153164970482827)
        ·
          refine ⟨19768391106229747455724241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13178927404153164970482827 19768391106229747455724241)
          ·
            refine ⟨14826293329672310591793181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19768391106229747455724241 14826293329672310591793181)
            ·
              refine ⟨5559859998627116471922443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14826293329672310591793181 5559859998627116471922443)
              ·
                refine ⟨8339789997940674707883665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559859998627116471922443 8339789997940674707883665)
                ·
                  refine ⟨6254842498455506030912749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8339789997940674707883665 6254842498455506030912749)
                  ·
                    refine ⟨2345565936920814761592281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6254842498455506030912749 2345565936920814761592281)
                    ·
                      refine ⟨1759174452690611071194211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345565936920814761592281 1759174452690611071194211)
                      ·
                        rfl

theorem cell23_3425980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_3425980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3425980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3425980 prefixEnd_3425980 := by exact prefixLift 3425980
  have htrace : WordTrace (prefixWord ++ tailWord_3425980) baseStart_3425980 baseEnd_3425980 := by
    simpa [prefixWord, tailWord_3425980, baseEnd_3425980] using wordTrace_append hprefix tailTrace_3425980
  have hstable : (prefixWord ++ tailWord_3425980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3425980).length < 2 ^ (prefixWord ++ tailWord_3425980).sum := by decide
  have hdescent : baseEnd_3425980 < baseStart_3425980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3425980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426010 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2]
def baseStart_3426010 : Nat := 118140960795 + 3426010 * 2 ^ 59
def prefixEnd_3426010 : Nat := 4983230072969 + 3 ^ 40 * 3426010 * 2
def baseEnd_3426010 : Nat := 1759189857110245953819073

theorem tailTrace_3426010 : CollatzResearch.WordTrace tailWord_3426010 prefixEnd_3426010 1759189857110245953819073 := by
  unfold tailWord_3426010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31239212579539590192412871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83304566878772240513100989 31239212579539590192412871)
  ·
    refine ⟨46858818869309385288619307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31239212579539590192412871 46858818869309385288619307)
    ·
      refine ⟨70288228303964077932928961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46858818869309385288619307 70288228303964077932928961)
      ·
        refine ⟨52716171227973058449696721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70288228303964077932928961 52716171227973058449696721)
        ·
          refine ⟨39537128420979793837272541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52716171227973058449696721 39537128420979793837272541)
          ·
            refine ⟨14826423157867422688977203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39537128420979793837272541 14826423157867422688977203)
            ·
              refine ⟨22239634736801134033465805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14826423157867422688977203 22239634736801134033465805)
              ·
                refine ⟨8339863026300425262549677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22239634736801134033465805 8339863026300425262549677)
                ·
                  refine ⟨3127448634862659473456129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8339863026300425262549677 3127448634862659473456129)
                  ·
                    refine ⟨2345586476146994605092097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3127448634862659473456129 2345586476146994605092097)
                    ·
                      refine ⟨1759189857110245953819073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345586476146994605092097 1759189857110245953819073)
                      ·
                        rfl

theorem cell23_3426010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_3426010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426010 prefixEnd_3426010 := by exact prefixLift 3426010
  have htrace : WordTrace (prefixWord ++ tailWord_3426010) baseStart_3426010 baseEnd_3426010 := by
    simpa [prefixWord, tailWord_3426010, baseEnd_3426010] using wordTrace_append hprefix tailTrace_3426010
  have hstable : (prefixWord ++ tailWord_3426010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426010).length < 2 ^ (prefixWord ++ tailWord_3426010).sum := by decide
  have hdescent : baseEnd_3426010 < baseStart_3426010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426020 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_3426020 : Nat := 118140960795 + 3426020 * 2 ^ 59
def prefixEnd_3426020 : Nat := 4983230072969 + 3 ^ 40 * 3426020 * 2
def baseEnd_3426020 : Nat := 586398330638930304898009

theorem tailTrace_3426020 : CollatzResearch.WordTrace tailWord_3426020 prefixEnd_3426020 586398330638930304898009 := by
  unfold tailWord_3426020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62478607524061066238757757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83304810032081421651677009 62478607524061066238757757)
  ·
    refine ⟨23429477821522899839534159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62478607524061066238757757 23429477821522899839534159)
    ·
      refine ⟨35144216732284349759301239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429477821522899839534159 35144216732284349759301239)
      ·
        refine ⟨52716325098426524638951859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35144216732284349759301239 52716325098426524638951859)
        ·
          refine ⟨79074487647639786958427789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52716325098426524638951859 79074487647639786958427789)
          ·
            refine ⟨29652932867864920109410421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79074487647639786958427789 29652932867864920109410421)
            ·
              refine ⟨2779962456362336260257227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29652932867864920109410421 2779962456362336260257227)
              ·
                refine ⟨4169943684543504390385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779962456362336260257227 4169943684543504390385841)
                ·
                  refine ⟨3127457763407628292789381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169943684543504390385841 3127457763407628292789381)
                  ·
                    refine ⟨586398330638930304898009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127457763407628292789381 586398330638930304898009)
                    ·
                      rfl

theorem cell23_3426020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_3426020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426020 prefixEnd_3426020 := by exact prefixLift 3426020
  have htrace : WordTrace (prefixWord ++ tailWord_3426020) baseStart_3426020 baseEnd_3426020 := by
    simpa [prefixWord, tailWord_3426020, baseEnd_3426020] using wordTrace_append hprefix tailTrace_3426020
  have hstable : (prefixWord ++ tailWord_3426020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426020).length < 2 ^ (prefixWord ++ tailWord_3426020).sum := by decide
  have hdescent : baseEnd_3426020 < baseStart_3426020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426030 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3426030 : Nat := 118140960795 + 3426030 * 2 ^ 59
def prefixEnd_3426030 : Nat := 4983230072969 + 3 ^ 40 * 3426030 * 2
def baseEnd_3426030 : Nat := 1759200126723335875568981

theorem tailTrace_3426030 : CollatzResearch.WordTrace tailWord_3426030 prefixEnd_3426030 1759200126723335875568981 := by
  unfold tailWord_3426030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15619697472260738023172443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83305053185390602790253029 15619697472260738023172443)
  ·
    refine ⟨23429546208391107034758665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15619697472260738023172443 23429546208391107034758665)
    ·
      refine ⟨17572159656293330276068999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23429546208391107034758665 17572159656293330276068999)
      ·
        refine ⟨26358239484439995414103499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17572159656293330276068999 26358239484439995414103499)
        ·
          refine ⟨39537359226659993121155249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26358239484439995414103499 39537359226659993121155249)
          ·
            refine ⟨29653019419994994840866437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39537359226659993121155249 29653019419994994840866437)
            ·
              refine ⟨5559941141249061532662457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29653019419994994840866437 5559941141249061532662457)
              ·
                refine ⟨4169955855936796149496843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5559941141249061532662457 4169955855936796149496843)
                ·
                  refine ⟨6254933783905194224245265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169955855936796149496843 6254933783905194224245265)
                  ·
                    refine ⟨4691200337928895668183949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254933783905194224245265 4691200337928895668183949)
                    ·
                      refine ⟨1759200126723335875568981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4691200337928895668183949 1759200126723335875568981)
                      ·
                        rfl

theorem cell23_3426030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3426030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426030 prefixEnd_3426030 := by exact prefixLift 3426030
  have htrace : WordTrace (prefixWord ++ tailWord_3426030) baseStart_3426030 baseEnd_3426030 := by
    simpa [prefixWord, tailWord_3426030, baseEnd_3426030] using wordTrace_append hprefix tailTrace_3426030
  have hstable : (prefixWord ++ tailWord_3426030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426030).length < 2 ^ (prefixWord ++ tailWord_3426030).sum := by decide
  have hdescent : baseEnd_3426030 < baseStart_3426030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426033 : List Nat := [1, 2, 2, 2, 2, 5, 2, 7]
def baseStart_3426033 : Nat := 118140960795 + 3426033 * 2 ^ 59
def prefixEnd_3426033 : Nat := 4983230072969 + 3 ^ 40 * 3426033 * 2
def baseEnd_3426033 : Nat := 65155617302418494956721

theorem tailTrace_3426033 : CollatzResearch.WordTrace tailWord_3426033 prefixEnd_3426033 65155617302418494956721 := by
  unfold tailWord_3426033
  simp only [CollatzResearch.WordTrace]
  refine ⟨124957689197075035697738753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83305126131383357131825835 124957689197075035697738753)
  ·
    refine ⟨93718266897806276773304065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124957689197075035697738753 93718266897806276773304065)
    ·
      refine ⟨70288700173354707579978049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93718266897806276773304065 70288700173354707579978049)
      ·
        refine ⟨52716525130016030684983537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70288700173354707579978049 52716525130016030684983537)
        ·
          refine ⟨39537393847512023013737653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52716525130016030684983537 39537393847512023013737653)
          ·
            refine ⟨3706630673204252157537905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39537393847512023013737653 3706630673204252157537905)
            ·
              refine ⟨2779973004903189118153429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706630673204252157537905 2779973004903189118153429)
              ·
                refine ⟨65155617302418494956721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2779973004903189118153429 65155617302418494956721)
                ·
                  rfl

theorem cell23_3426033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 7].length) (baseStart_3426033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426033 prefixEnd_3426033 := by exact prefixLift 3426033
  have htrace : WordTrace (prefixWord ++ tailWord_3426033) baseStart_3426033 baseEnd_3426033 := by
    simpa [prefixWord, tailWord_3426033, baseEnd_3426033] using wordTrace_append hprefix tailTrace_3426033
  have hstable : (prefixWord ++ tailWord_3426033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426033).length < 2 ^ (prefixWord ++ tailWord_3426033).sum := by decide
  have hdescent : baseEnd_3426033 < baseStart_3426033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426053 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_3426053 : Nat := 118140960795 + 3426053 * 2 ^ 59
def prefixEnd_3426053 : Nat := 4983230072969 + 3 ^ 40 * 3426053 * 2
def baseEnd_3426053 : Nat := 1759211936778389285581375

theorem tailTrace_3426053 : CollatzResearch.WordTrace tailWord_3426053 prefixEnd_3426053 1759211936778389285581375 := by
  unfold tailWord_3426053
  simp only [CollatzResearch.WordTrace]
  refine ⟨124958418657002579113466813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83305612438001719408977875 124958418657002579113466813)
  ·
    refine ⟨46859406996375967167550055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124958418657002579113466813 46859406996375967167550055)
    ·
      refine ⟨70289110494563950751325083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46859406996375967167550055 70289110494563950751325083)
      ·
        refine ⟨105433665741845926126987625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70289110494563950751325083 105433665741845926126987625)
        ·
          refine ⟨79075249306384444595240719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105433665741845926126987625 79075249306384444595240719)
          ·
            refine ⟨118612873959576666892861079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79075249306384444595240719 118612873959576666892861079)
            ·
              refine ⟨177919310939365000339291619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118612873959576666892861079 177919310939365000339291619)
              ·
                refine ⟨266878966409047500508937429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177919310939365000339291619 266878966409047500508937429)
                ·
                  refine ⟨6254975775212050793178221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266878966409047500508937429 6254975775212050793178221)
                  ·
                    refine ⟨2345615915704519047441833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6254975775212050793178221 2345615915704519047441833)
                    ·
                      refine ⟨1759211936778389285581375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345615915704519047441833 1759211936778389285581375)
                      ·
                        rfl

theorem cell23_3426053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_3426053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426053 prefixEnd_3426053 := by exact prefixLift 3426053
  have htrace : WordTrace (prefixWord ++ tailWord_3426053) baseStart_3426053 baseEnd_3426053 := by
    simpa [prefixWord, tailWord_3426053, baseEnd_3426053] using wordTrace_append hprefix tailTrace_3426053
  have hstable : (prefixWord ++ tailWord_3426053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426053).length < 2 ^ (prefixWord ++ tailWord_3426053).sum := by decide
  have hdescent : baseEnd_3426053 < baseStart_3426053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426056 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3426056 : Nat := 118140960795 + 3426056 * 2 ^ 59
def prefixEnd_3426056 : Nat := 4983230072969 + 3 ^ 40 * 3426056 * 2
def baseEnd_3426056 : Nat := 1759213477220352773843861

theorem tailTrace_3426056 : CollatzResearch.WordTrace tailWord_3426056 prefixEnd_3426056 1759213477220352773843861 := by
  unfold tailWord_3426056
  simp only [CollatzResearch.WordTrace]
  refine ⟨62479264037995855312913011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83305685383994473750550681 62479264037995855312913011)
  ·
    refine ⟨93718896056993782969369517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62479264037995855312913011 93718896056993782969369517)
    ·
      refine ⟨35144586021372668613513569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93718896056993782969369517 35144586021372668613513569)
      ·
        refine ⟨26358439516029501460135177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35144586021372668613513569 26358439516029501460135177)
        ·
          refine ⟨19768829637022126095101383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26358439516029501460135177 19768829637022126095101383)
          ·
            refine ⟨29653244455533189142652075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19768829637022126095101383 29653244455533189142652075)
            ·
              refine ⟨44479866683299783713978113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653244455533189142652075 44479866683299783713978113)
              ·
                refine ⟨33359900012474837785483585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44479866683299783713978113 33359900012474837785483585)
                ·
                  refine ⟨25019925009356128339112689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33359900012474837785483585 25019925009356128339112689)
                  ·
                    refine ⟨18764943757017096254334517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25019925009356128339112689 18764943757017096254334517)
                    ·
                      refine ⟨1759213477220352773843861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18764943757017096254334517 1759213477220352773843861)
                      ·
                        rfl

theorem cell23_3426056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3426056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426056 prefixEnd_3426056 := by exact prefixLift 3426056
  have htrace : WordTrace (prefixWord ++ tailWord_3426056) baseStart_3426056 baseEnd_3426056 := by
    simpa [prefixWord, tailWord_3426056, baseEnd_3426056] using wordTrace_append hprefix tailTrace_3426056
  have hstable : (prefixWord ++ tailWord_3426056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426056).length < 2 ^ (prefixWord ++ tailWord_3426056).sum := by decide
  have hdescent : baseEnd_3426056 < baseStart_3426056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426076 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3426076 : Nat := 118140960795 + 3426076 * 2 ^ 59
def prefixEnd_3426076 : Nat := 4983230072969 + 3 ^ 40 * 3426076 * 2
def baseEnd_3426076 : Nat := 586407915611147565197923

theorem tailTrace_3426076 : CollatzResearch.WordTrace tailWord_3426076 prefixEnd_3426076 586407915611147565197923 := by
  unfold tailWord_3426076
  simp only [CollatzResearch.WordTrace]
  refine ⟨62479628767959627020777041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83306171690612836027702721 62479628767959627020777041)
  ·
    refine ⟨46859721575969720265582781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62479628767959627020777041 46859721575969720265582781)
    ·
      refine ⟨17572395590988645099593543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46859721575969720265582781 17572395590988645099593543)
      ·
        refine ⟨26358593386482967649390315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17572395590988645099593543 26358593386482967649390315)
        ·
          refine ⟨39537890079724451474085473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26358593386482967649390315 39537890079724451474085473)
          ·
            refine ⟨29653417559793338605564105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39537890079724451474085473 29653417559793338605564105)
            ·
              refine ⟨22240063169845003954173079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29653417559793338605564105 22240063169845003954173079)
              ·
                refine ⟨33360094754767505931259619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22240063169845003954173079 33360094754767505931259619)
                ·
                  refine ⟨50040142132151258896889429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33360094754767505931259619 50040142132151258896889429)
                  ·
                    refine ⟨586407915611147565197923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50040142132151258896889429 586407915611147565197923)
                    ·
                      rfl

theorem cell23_3426076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3426076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426076 prefixEnd_3426076 := by exact prefixLift 3426076
  have htrace : WordTrace (prefixWord ++ tailWord_3426076) baseStart_3426076 baseEnd_3426076 := by
    simpa [prefixWord, tailWord_3426076, baseEnd_3426076] using wordTrace_append hprefix tailTrace_3426076
  have hstable : (prefixWord ++ tailWord_3426076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426076).length < 2 ^ (prefixWord ++ tailWord_3426076).sum := by decide
  have hdescent : baseEnd_3426076 < baseStart_3426076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426096 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_3426096 : Nat := 118140960795 + 3426096 * 2 ^ 59
def prefixEnd_3426096 : Nat := 4983230072969 + 3 ^ 40 * 3426096 * 2
def baseEnd_3426096 : Nat := 1759234016446532617343677

theorem tailTrace_3426096 : CollatzResearch.WordTrace tailWord_3426096 prefixEnd_3426096 1759234016446532617343677 := by
  unfold tailWord_3426096
  simp only [CollatzResearch.WordTrace]
  refine ⟨62479993497923398728641071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83306657997231198304854761 62479993497923398728641071)
  ·
    refine ⟨93719990246885098092961607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62479993497923398728641071 93719990246885098092961607)
    ·
      refine ⟨140579985370327647139442411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93719990246885098092961607 140579985370327647139442411)
      ·
        refine ⟨210869978055491470709163617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140579985370327647139442411 210869978055491470709163617)
        ·
          refine ⟨158152483541618603031872713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210869978055491470709163617 158152483541618603031872713)
          ·
            refine ⟨118614362656213952273904535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158152483541618603031872713 118614362656213952273904535)
            ·
              refine ⟨177921543984320928410856803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118614362656213952273904535 177921543984320928410856803)
              ·
                refine ⟨266882315976481392616285205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177921543984320928410856803 266882315976481392616285205)
                ·
                  refine ⟨12510108561397565278888369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266882315976481392616285205 12510108561397565278888369)
                  ·
                    refine ⟨9382581421048173959166277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12510108561397565278888369 9382581421048173959166277)
                    ·
                      refine ⟨1759234016446532617343677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9382581421048173959166277 1759234016446532617343677)
                      ·
                        rfl

theorem cell23_3426096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_3426096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426096 prefixEnd_3426096 := by exact prefixLift 3426096
  have htrace : WordTrace (prefixWord ++ tailWord_3426096) baseStart_3426096 baseEnd_3426096 := by
    simpa [prefixWord, tailWord_3426096, baseEnd_3426096] using wordTrace_append hprefix tailTrace_3426096
  have hstable : (prefixWord ++ tailWord_3426096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426096).length < 2 ^ (prefixWord ++ tailWord_3426096).sum := by decide
  have hdescent : baseEnd_3426096 < baseStart_3426096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426117 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_3426117 : Nat := 118140960795 + 3426117 * 2 ^ 59
def prefixEnd_3426117 : Nat := 4983230072969 + 3 ^ 40 * 3426117 * 2
def baseEnd_3426117 : Nat := 1759244799540277035181081

theorem tailTrace_3426117 : CollatzResearch.WordTrace tailWord_3426117 prefixEnd_3426117 1759244799540277035181081 := by
  unfold tailWord_3426117
  simp only [CollatzResearch.WordTrace]
  refine ⟨124960752928770718043796605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83307168619180478695864403 124960752928770718043796605)
  ·
    refine ⟨46860282348289019266423727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124960752928770718043796605 46860282348289019266423727)
    ·
      refine ⟨70290423522433528899635591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46860282348289019266423727 70290423522433528899635591)
      ·
        refine ⟨105435635283650293349453387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70290423522433528899635591 105435635283650293349453387)
        ·
          refine ⟨158153452925475440024180081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105435635283650293349453387 158153452925475440024180081)
          ·
            refine ⟨118615089694106580018135061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158153452925475440024180081 118615089694106580018135061)
            ·
              refine ⟨5560082329411245938350081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118615089694106580018135061 5560082329411245938350081)
              ·
                refine ⟨4170061747058434453762561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5560082329411245938350081 4170061747058434453762561)
                ·
                  refine ⟨3127546310293825840321921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170061747058434453762561 3127546310293825840321921)
                  ·
                    refine ⟨2345659732720369380241441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3127546310293825840321921 2345659732720369380241441)
                    ·
                      refine ⟨1759244799540277035181081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345659732720369380241441 1759244799540277035181081)
                      ·
                        rfl

theorem cell23_3426117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_3426117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426117 prefixEnd_3426117 := by exact prefixLift 3426117
  have htrace : WordTrace (prefixWord ++ tailWord_3426117) baseStart_3426117 baseEnd_3426117 := by
    simpa [prefixWord, tailWord_3426117, baseEnd_3426117] using wordTrace_append hprefix tailTrace_3426117
  have hstable : (prefixWord ++ tailWord_3426117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426117).length < 2 ^ (prefixWord ++ tailWord_3426117).sum := by decide
  have hdescent : baseEnd_3426117 < baseStart_3426117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426126 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3426126 : Nat := 118140960795 + 3426126 * 2 ^ 59
def prefixEnd_3426126 : Nat := 4983230072969 + 3 ^ 40 * 3426126 * 2
def baseEnd_3426126 : Nat := 1759249420866167499968539

theorem tailTrace_3426126 : CollatzResearch.WordTrace tailWord_3426126 prefixEnd_3426126 1759249420866167499968539 := by
  unfold tailWord_3426126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620135148217264072609279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83307387457158741720582821 15620135148217264072609279)
  ·
    refine ⟨23430202722325896108913919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620135148217264072609279 23430202722325896108913919)
    ·
      refine ⟨35145304083488844163370879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430202722325896108913919 35145304083488844163370879)
      ·
        refine ⟨52717956125233266245056319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35145304083488844163370879 52717956125233266245056319)
        ·
          refine ⟨79076934187849899367584479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52717956125233266245056319 79076934187849899367584479)
          ·
            refine ⟨118615401281774849051376719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79076934187849899367584479 118615401281774849051376719)
            ·
              refine ⟨177923101922662273577065079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118615401281774849051376719 177923101922662273577065079)
              ·
                refine ⟨266884652883993410365597619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177923101922662273577065079 266884652883993410365597619)
                ·
                  refine ⟨400326979325990115548396429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266884652883993410365597619 400326979325990115548396429)
                  ·
                    refine ⟨150122617247246293330648661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400326979325990115548396429 150122617247246293330648661)
                    ·
                      refine ⟨1759249420866167499968539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 150122617247246293330648661 1759249420866167499968539)
                      ·
                        rfl

theorem cell23_3426126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3426126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426126 prefixEnd_3426126 := by exact prefixLift 3426126
  have htrace : WordTrace (prefixWord ++ tailWord_3426126) baseStart_3426126 baseEnd_3426126 := by
    simpa [prefixWord, tailWord_3426126, baseEnd_3426126] using wordTrace_append hprefix tailTrace_3426126
  have hstable : (prefixWord ++ tailWord_3426126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426126).length < 2 ^ (prefixWord ++ tailWord_3426126).sum := by decide
  have hdescent : baseEnd_3426126 < baseStart_3426126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426133 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3426133 : Nat := 118140960795 + 3426133 * 2 ^ 59
def prefixEnd_3426133 : Nat := 4983230072969 + 3 ^ 40 * 3426133 * 2
def baseEnd_3426133 : Nat := 1759253015230748972581007

theorem tailTrace_3426133 : CollatzResearch.WordTrace tailWord_3426133 prefixEnd_3426133 1759253015230748972581007 := by
  unfold tailWord_3426133
  simp only [CollatzResearch.WordTrace]
  refine ⟨124961336496712752776379053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83307557664475168517586035 124961336496712752776379053)
  ·
    refine ⟨46860501186267282291142145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124961336496712752776379053 46860501186267282291142145)
    ·
      refine ⟨35145375889700461718356609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46860501186267282291142145 35145375889700461718356609)
      ·
        refine ⟨26359031917275346288767457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35145375889700461718356609 26359031917275346288767457)
        ·
          refine ⟨19769273937956509716575593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26359031917275346288767457 19769273937956509716575593)
          ·
            refine ⟨14826955453467382287431695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19769273937956509716575593 14826955453467382287431695)
            ·
              refine ⟨22240433180201073431147543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14826955453467382287431695 22240433180201073431147543)
              ·
                refine ⟨33360649770301610146721315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22240433180201073431147543 33360649770301610146721315)
                ·
                  refine ⟨50040974655452415220081973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33360649770301610146721315 50040974655452415220081973)
                  ·
                    refine ⟨4691341373948663926882685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50040974655452415220081973 4691341373948663926882685)
                    ·
                      refine ⟨1759253015230748972581007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4691341373948663926882685 1759253015230748972581007)
                      ·
                        rfl

theorem cell23_3426133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3426133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426133 prefixEnd_3426133 := by exact prefixLift 3426133
  have htrace : WordTrace (prefixWord ++ tailWord_3426133) baseStart_3426133 baseEnd_3426133 := by
    simpa [prefixWord, tailWord_3426133, baseEnd_3426133] using wordTrace_append hprefix tailTrace_3426133
  have hstable : (prefixWord ++ tailWord_3426133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426133).length < 2 ^ (prefixWord ++ tailWord_3426133).sum := by decide
  have hdescent : baseEnd_3426133 < baseStart_3426133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426140 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 7]
def baseStart_3426140 : Nat := 118140960795 + 3426140 * 2 ^ 59
def prefixEnd_3426140 : Nat := 4983230072969 + 3 ^ 40 * 3426140 * 2
def baseEnd_3426140 : Nat := 195472956621703382799275

theorem tailTrace_3426140 : CollatzResearch.WordTrace tailWord_3426140 prefixEnd_3426140 195472956621703382799275 := by
  unfold tailWord_3426140
  simp only [CollatzResearch.WordTrace]
  refine ⟨62480795903843696485941937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83307727871791595314589249 62480795903843696485941937)
  ·
    refine ⟨46860596927882772364456453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62480795903843696485941937 46860596927882772364456453)
    ·
      refine ⟨8786361923978019818335585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46860596927882772364456453 8786361923978019818335585)
      ·
        refine ⟨6589771442983514863751689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8786361923978019818335585 6589771442983514863751689)
        ·
          refine ⟨4942328582237636147813767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6589771442983514863751689 4942328582237636147813767)
          ·
            refine ⟨7413492873356454221720651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942328582237636147813767 7413492873356454221720651)
            ·
              refine ⟨11120239310034681332580977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413492873356454221720651 11120239310034681332580977)
              ·
                refine ⟨8340179482526010999435733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11120239310034681332580977 8340179482526010999435733)
                ·
                  refine ⟨195472956621703382799275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8340179482526010999435733 195472956621703382799275)
                  ·
                    rfl

theorem cell23_3426140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_3426140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426140 prefixEnd_3426140 := by exact prefixLift 3426140
  have htrace : WordTrace (prefixWord ++ tailWord_3426140) baseStart_3426140 baseEnd_3426140 := by
    simpa [prefixWord, tailWord_3426140, baseEnd_3426140] using wordTrace_append hprefix tailTrace_3426140
  have hstable : (prefixWord ++ tailWord_3426140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426140).length < 2 ^ (prefixWord ++ tailWord_3426140).sum := by decide
  have hdescent : baseEnd_3426140 < baseStart_3426140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426173 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_3426173 : Nat := 118140960795 + 3426173 * 2 ^ 59
def prefixEnd_3426173 : Nat := 4983230072969 + 3 ^ 40 * 3426173 * 2
def baseEnd_3426173 : Nat := 1759273554456928816080823

theorem tailTrace_3426173 : CollatzResearch.WordTrace tailWord_3426173 prefixEnd_3426173 1759273554456928816080823 := by
  unfold tailWord_3426173
  simp only [CollatzResearch.WordTrace]
  refine ⟨124962795416567839607835173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83308530277711893071890115 124962795416567839607835173)
  ·
    refine ⟨23430524140606469926469095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124962795416567839607835173 23430524140606469926469095)
    ·
      refine ⟨35145786210909704889703643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430524140606469926469095 35145786210909704889703643)
      ·
        refine ⟨52718679316364557334555465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35145786210909704889703643 52718679316364557334555465)
        ·
          refine ⟨39539009487273418000916599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52718679316364557334555465 39539009487273418000916599)
          ·
            refine ⟨59308514230910127001374899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39539009487273418000916599 59308514230910127001374899)
            ·
              refine ⟨88962771346365190502062349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59308514230910127001374899 88962771346365190502062349)
              ·
                refine ⟨33361039254886946438273381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88962771346365190502062349 33361039254886946438273381)
                ·
                  refine ⟨6255194860291302457176259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33361039254886946438273381 6255194860291302457176259)
                  ·
                    refine ⟨9382792290436953685764389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6255194860291302457176259 9382792290436953685764389)
                    ·
                      refine ⟨1759273554456928816080823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9382792290436953685764389 1759273554456928816080823)
                      ·
                        rfl

theorem cell23_3426173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_3426173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426173 prefixEnd_3426173 := by exact prefixLift 3426173
  have htrace : WordTrace (prefixWord ++ tailWord_3426173) baseStart_3426173 baseEnd_3426173 := by
    simpa [prefixWord, tailWord_3426173, baseEnd_3426173] using wordTrace_append hprefix tailTrace_3426173
  have hstable : (prefixWord ++ tailWord_3426173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426173).length < 2 ^ (prefixWord ++ tailWord_3426173).sum := by decide
  have hdescent : baseEnd_3426173 < baseStart_3426173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426193 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_3426193 : Nat := 118140960795 + 3426193 * 2 ^ 59
def prefixEnd_3426193 : Nat := 4983230072969 + 3 ^ 40 * 3426193 * 2
def baseEnd_3426193 : Nat := 1759283824070018737830731

theorem tailTrace_3426193 : CollatzResearch.WordTrace tailWord_3426193 prefixEnd_3426193 1759283824070018737830731 := by
  unfold tailWord_3426193
  simp only [CollatzResearch.WordTrace]
  refine ⟨124963524876495383023563233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83309016584330255349042155 124963524876495383023563233)
  ·
    refine ⟨93722643657371537267672425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124963524876495383023563233 93722643657371537267672425)
    ·
      refine ⟨70291982743028652950754319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93722643657371537267672425 70291982743028652950754319)
      ·
        refine ⟨105437974114542979426131479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70291982743028652950754319 105437974114542979426131479)
        ·
          refine ⟨158156961171814469139197219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105437974114542979426131479 158156961171814469139197219)
          ·
            refine ⟨237235441757721703708795829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158156961171814469139197219 237235441757721703708795829)
            ·
              refine ⟨22240822664786409722699609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237235441757721703708795829 22240822664786409722699609)
              ·
                refine ⟨16680616998589807292024707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22240822664786409722699609 16680616998589807292024707)
                ·
                  refine ⟨25020925497884710938037061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16680616998589807292024707 25020925497884710938037061)
                  ·
                    refine ⟨4691423530853383300881949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25020925497884710938037061 4691423530853383300881949)
                    ·
                      refine ⟨1759283824070018737830731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4691423530853383300881949 1759283824070018737830731)
                      ·
                        rfl

theorem cell23_3426193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_3426193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426193 prefixEnd_3426193 := by exact prefixLift 3426193
  have htrace : WordTrace (prefixWord ++ tailWord_3426193) baseStart_3426193 baseEnd_3426193 := by
    simpa [prefixWord, tailWord_3426193, baseEnd_3426193] using wordTrace_append hprefix tailTrace_3426193
  have hstable : (prefixWord ++ tailWord_3426193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426193).length < 2 ^ (prefixWord ++ tailWord_3426193).sum := by decide
  have hdescent : baseEnd_3426193 < baseStart_3426193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426250 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2]
def baseStart_3426250 : Nat := 118140960795 + 3426250 * 2 ^ 59
def prefixEnd_3426250 : Nat := 4983230072969 + 3 ^ 40 * 3426250 * 2
def baseEnd_3426250 : Nat := 1759313092467325014817969

theorem tailTrace_3426250 : CollatzResearch.WordTrace tailWord_3426250 prefixEnd_3426250 1759313092467325014817969 := by
  unfold tailWord_3426250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31241400959322220439597051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83310402558192587838925469 31241400959322220439597051)
  ·
    refine ⟨46862101438983330659395577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31241400959322220439597051 46862101438983330659395577)
    ·
      refine ⟨35146576079237497994546683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46862101438983330659395577 35146576079237497994546683)
      ·
        refine ⟨52719864118856246991820025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35146576079237497994546683 52719864118856246991820025)
        ·
          refine ⟨39539898089142185243865019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52719864118856246991820025 39539898089142185243865019)
          ·
            refine ⟨59309847133713277865797529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39539898089142185243865019 59309847133713277865797529)
            ·
              refine ⟨44482385350284958399348147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59309847133713277865797529 44482385350284958399348147)
              ·
                refine ⟨66723578025427437599022221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44482385350284958399348147 66723578025427437599022221)
                ·
                  refine ⟨25021341759535289099633333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66723578025427437599022221 25021341759535289099633333)
                  ·
                    refine ⟨2345750789956433353090625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25021341759535289099633333 2345750789956433353090625)
                    ·
                      refine ⟨1759313092467325014817969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345750789956433353090625 1759313092467325014817969)
                      ·
                        rfl

theorem cell23_3426250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_3426250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426250 prefixEnd_3426250 := by exact prefixLift 3426250
  have htrace : WordTrace (prefixWord ++ tailWord_3426250) baseStart_3426250 baseEnd_3426250 := by
    simpa [prefixWord, tailWord_3426250, baseEnd_3426250] using wordTrace_append hprefix tailTrace_3426250
  have hstable : (prefixWord ++ tailWord_3426250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426250).length < 2 ^ (prefixWord ++ tailWord_3426250).sum := by decide
  have hdescent : baseEnd_3426250 < baseStart_3426250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426260 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3426260 : Nat := 118140960795 + 3426260 * 2 ^ 59
def prefixEnd_3426260 : Nat := 4983230072969 + 3 ^ 40 * 3426260 * 2
def baseEnd_3426260 : Nat := 586439409091289991897641

theorem tailTrace_3426260 : CollatzResearch.WordTrace tailWord_3426260 prefixEnd_3426260 586439409091289991897641 := by
  unfold tailWord_3426260
  simp only [CollatzResearch.WordTrace]
  refine ⟨62482984283626326733126117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83310645711501768977501489 62482984283626326733126117)
  ·
    refine ⟨11715559553179936262461147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62482984283626326733126117 11715559553179936262461147)
    ·
      refine ⟨17573339329769904393691721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11715559553179936262461147 17573339329769904393691721)
      ·
        refine ⟨13180004497327428295268791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17573339329769904393691721 13180004497327428295268791)
        ·
          refine ⟨19770006745991142442903187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13180004497327428295268791 19770006745991142442903187)
          ·
            refine ⟨29655010118986713664354781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19770006745991142442903187 29655010118986713664354781)
            ·
              refine ⟨11120628794620017624133043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29655010118986713664354781 11120628794620017624133043)
              ·
                refine ⟨16680943191930026436199565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11120628794620017624133043 16680943191930026436199565)
                ·
                  refine ⟨6255353696973759913574837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16680943191930026436199565 6255353696973759913574837)
                  ·
                    refine ⟨586439409091289991897641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6255353696973759913574837 586439409091289991897641)
                    ·
                      rfl

theorem cell23_3426260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3426260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426260 prefixEnd_3426260 := by exact prefixLift 3426260
  have htrace : WordTrace (prefixWord ++ tailWord_3426260) baseStart_3426260 baseEnd_3426260 := by
    simpa [prefixWord, tailWord_3426260, baseEnd_3426260] using wordTrace_append hprefix tailTrace_3426260
  have hstable : (prefixWord ++ tailWord_3426260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426260).length < 2 ^ (prefixWord ++ tailWord_3426260).sum := by decide
  have hdescent : baseEnd_3426260 < baseStart_3426260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426273 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3426273 : Nat := 118140960795 + 3426273 * 2 ^ 59
def prefixEnd_3426273 : Nat := 4983230072969 + 3 ^ 40 * 3426273 * 2
def baseEnd_3426273 : Nat := 586441634174126141610121

theorem tailTrace_3426273 : CollatzResearch.WordTrace tailWord_3426273 prefixEnd_3426273 586441634174126141610121 := by
  unfold tailWord_3426273
  simp only [CollatzResearch.WordTrace]
  refine ⟨124966442716205556686475473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83310961810803704457650315 124966442716205556686475473)
  ·
    refine ⟨93724832037154167514856605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124966442716205556686475473 93724832037154167514856605)
    ·
      refine ⟨35146812013932812818071227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93724832037154167514856605 35146812013932812818071227)
      ·
        refine ⟨52720218020899219227106841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35146812013932812818071227 52720218020899219227106841)
        ·
          refine ⟨39540163515674414420330131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52720218020899219227106841 39540163515674414420330131)
          ·
            refine ⟨59310245273511621630495197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39540163515674414420330131 59310245273511621630495197)
            ·
              refine ⟨22241341977566858111435699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59310245273511621630495197 22241341977566858111435699)
              ·
                refine ⟨33362012966350287167153549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22241341977566858111435699 33362012966350287167153549)
                ·
                  refine ⟨12510754862381357687682581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33362012966350287167153549 12510754862381357687682581)
                  ·
                    refine ⟨586441634174126141610121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12510754862381357687682581 586441634174126141610121)
                    ·
                      rfl

theorem cell23_3426273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3426273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426273 prefixEnd_3426273 := by exact prefixLift 3426273
  have htrace : WordTrace (prefixWord ++ tailWord_3426273) baseStart_3426273 baseEnd_3426273 := by
    simpa [prefixWord, tailWord_3426273, baseEnd_3426273] using wordTrace_append hprefix tailTrace_3426273
  have hstable : (prefixWord ++ tailWord_3426273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426273).length < 2 ^ (prefixWord ++ tailWord_3426273).sum := by decide
  have hdescent : baseEnd_3426273 < baseStart_3426273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426285 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3426285 : Nat := 118140960795 + 3426285 * 2 ^ 59
def prefixEnd_3426285 : Nat := 4983230072969 + 3 ^ 40 * 3426285 * 2
def baseEnd_3426285 : Nat := 586443688096744125960103

theorem tailTrace_3426285 : CollatzResearch.WordTrace tailWord_3426285 prefixEnd_3426285 586443688096744125960103 := by
  unfold tailWord_3426285
  simp only [CollatzResearch.WordTrace]
  refine ⟨124966880392162082735912309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83311253594774721823941539 124966880392162082735912309)
  ·
    refine ⟨11715645036765195256491779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124966880392162082735912309 11715645036765195256491779)
    ·
      refine ⟨17573467555147792884737669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11715645036765195256491779 17573467555147792884737669)
      ·
        refine ⟨3295025166590211165888313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17573467555147792884737669 3295025166590211165888313)
        ·
          refine ⟨2471268874942658374416235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3295025166590211165888313 2471268874942658374416235)
          ·
            refine ⟨3706903312413987561624353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471268874942658374416235 3706903312413987561624353)
            ·
              refine ⟨2780177484310490671218265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706903312413987561624353 2780177484310490671218265)
              ·
                refine ⟨2085133113232868003413699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780177484310490671218265 2085133113232868003413699)
                ·
                  refine ⟨3127699669849302005120549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085133113232868003413699 3127699669849302005120549)
                  ·
                    refine ⟨586443688096744125960103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127699669849302005120549 586443688096744125960103)
                    ·
                      rfl

theorem cell23_3426285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3426285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426285 prefixEnd_3426285 := by exact prefixLift 3426285
  have htrace : WordTrace (prefixWord ++ tailWord_3426285) baseStart_3426285 baseEnd_3426285 := by
    simpa [prefixWord, tailWord_3426285, baseEnd_3426285] using wordTrace_append hprefix tailTrace_3426285
  have hstable : (prefixWord ++ tailWord_3426285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426285).length < 2 ^ (prefixWord ++ tailWord_3426285).sum := by decide
  have hdescent : baseEnd_3426285 < baseStart_3426285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426300 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3426300 : Nat := 118140960795 + 3426300 * 2 ^ 59
def prefixEnd_3426300 : Nat := 4983230072969 + 3 ^ 40 * 3426300 * 2
def baseEnd_3426300 : Nat := 1759338766500049819192739

theorem tailTrace_3426300 : CollatzResearch.WordTrace tailWord_3426300 prefixEnd_3426300 1759338766500049819192739 := by
  unfold tailWord_3426300
  simp only [CollatzResearch.WordTrace]
  refine ⟨62483713743553870148854177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83311618324738493531805569 62483713743553870148854177)
  ·
    refine ⟨46862785307665402611640633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62483713743553870148854177 46862785307665402611640633)
    ·
      refine ⟨35147088980749051958730475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46862785307665402611640633 35147088980749051958730475)
      ·
        refine ⟨52720633471123577938095713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35147088980749051958730475 52720633471123577938095713)
        ·
          refine ⟨39540475103342683453571785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52720633471123577938095713 39540475103342683453571785)
          ·
            refine ⟨29655356327507012590178839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39540475103342683453571785 29655356327507012590178839)
            ·
              refine ⟨44483034491260518885268259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29655356327507012590178839 44483034491260518885268259)
              ·
                refine ⟨66724551736890778327902389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44483034491260518885268259 66724551736890778327902389)
                ·
                  refine ⟨6255426725333510468240849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66724551736890778327902389 6255426725333510468240849)
                  ·
                    refine ⟨4691570044000132851180637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6255426725333510468240849 4691570044000132851180637)
                    ·
                      refine ⟨1759338766500049819192739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4691570044000132851180637 1759338766500049819192739)
                      ·
                        rfl

theorem cell23_3426300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3426300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426300 prefixEnd_3426300 := by exact prefixLift 3426300
  have htrace : WordTrace (prefixWord ++ tailWord_3426300) baseStart_3426300 baseEnd_3426300 := by
    simpa [prefixWord, tailWord_3426300, baseEnd_3426300] using wordTrace_append hprefix tailTrace_3426300
  have hstable : (prefixWord ++ tailWord_3426300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426300).length < 2 ^ (prefixWord ++ tailWord_3426300).sum := by decide
  have hdescent : baseEnd_3426300 < baseStart_3426300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426347 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 3]
def baseStart_3426347 : Nat := 118140960795 + 3426347 * 2 ^ 59
def prefixEnd_3426347 : Nat := 4983230072969 + 3 ^ 40 * 3426347 * 2
def baseEnd_3426347 : Nat := 1759362900090811135305023

theorem tailTrace_3426347 : CollatzResearch.WordTrace tailWord_3426347 prefixEnd_3426347 1759362900090811135305023 := by
  unfold tailWord_3426347
  simp only [CollatzResearch.WordTrace]
  refine ⟨124969141717937467324669295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83312761145291644883112863 124969141717937467324669295)
  ·
    refine ⟨187453712576906200987003943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124969141717937467324669295 187453712576906200987003943)
    ·
      refine ⟨281180568865359301480505915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187453712576906200987003943 281180568865359301480505915)
      ·
        refine ⟨421770853298038952220758873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281180568865359301480505915 421770853298038952220758873)
        ·
          refine ⟨316328139973529214165569155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421770853298038952220758873 316328139973529214165569155)
          ·
            refine ⟨474492209960293821248353733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316328139973529214165569155 474492209960293821248353733)
            ·
              refine ⟨88967289367555091484066325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 474492209960293821248353733 88967289367555091484066325)
              ·
                refine ⟨4170341689104144913315609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88967289367555091484066325 4170341689104144913315609)
                ·
                  refine ⟨3127756266828108684986707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170341689104144913315609 3127756266828108684986707)
                  ·
                    refine ⟨4691634400242163027480061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3127756266828108684986707 4691634400242163027480061)
                    ·
                      refine ⟨1759362900090811135305023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4691634400242163027480061 1759362900090811135305023)
                      ·
                        rfl

theorem cell23_3426347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 3].length) (baseStart_3426347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426347 prefixEnd_3426347 := by exact prefixLift 3426347
  have htrace : WordTrace (prefixWord ++ tailWord_3426347) baseStart_3426347 baseEnd_3426347 := by
    simpa [prefixWord, tailWord_3426347, baseEnd_3426347] using wordTrace_append hprefix tailTrace_3426347
  have hstable : (prefixWord ++ tailWord_3426347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426347).length < 2 ^ (prefixWord ++ tailWord_3426347).sum := by decide
  have hdescent : baseEnd_3426347 < baseStart_3426347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426357 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_3426357 : Nat := 118140960795 + 3426357 * 2 ^ 59
def prefixEnd_3426357 : Nat := 4983230072969 + 3 ^ 40 * 3426357 * 2
def baseEnd_3426357 : Nat := 1759368034897356096179977

theorem tailTrace_3426357 : CollatzResearch.WordTrace tailWord_3426357 prefixEnd_3426357 1759368034897356096179977 := by
  unfold tailWord_3426357
  simp only [CollatzResearch.WordTrace]
  refine ⟨124969506447901239032533325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83313004298600826021688883 124969506447901239032533325)
  ·
    refine ⟨46863564917962964637199997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124969506447901239032533325 46863564917962964637199997)
    ·
      refine ⟨17573836844236111738949999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46863564917962964637199997 17573836844236111738949999)
      ·
        refine ⟨26360755266354167608424999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17573836844236111738949999 26360755266354167608424999)
        ·
          refine ⟨39541132899531251412637499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26360755266354167608424999 39541132899531251412637499)
          ·
            refine ⟨59311699349296877118956249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39541132899531251412637499 59311699349296877118956249)
            ·
              refine ⟨44483774511972657839217187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59311699349296877118956249 44483774511972657839217187)
              ·
                refine ⟨66725661767958986758825781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44483774511972657839217187 66725661767958986758825781)
                ·
                  refine ⟨6255530790746155008639917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66725661767958986758825781 6255530790746155008639917)
                  ·
                    refine ⟨2345824046529808128239969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6255530790746155008639917 2345824046529808128239969)
                    ·
                      refine ⟨1759368034897356096179977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345824046529808128239969 1759368034897356096179977)
                      ·
                        rfl

theorem cell23_3426357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_3426357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426357 prefixEnd_3426357 := by exact prefixLift 3426357
  have htrace : WordTrace (prefixWord ++ tailWord_3426357) baseStart_3426357 baseEnd_3426357 := by
    simpa [prefixWord, tailWord_3426357, baseEnd_3426357] using wordTrace_append hprefix tailTrace_3426357
  have hstable : (prefixWord ++ tailWord_3426357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426357).length < 2 ^ (prefixWord ++ tailWord_3426357).sum := by decide
  have hdescent : baseEnd_3426357 < baseStart_3426357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426404 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_3426404 : Nat := 118140960795 + 3426404 * 2 ^ 59
def prefixEnd_3426404 : Nat := 4983230072969 + 3 ^ 40 * 3426404 * 2
def baseEnd_3426404 : Nat := 1759392168488117412292261

theorem tailTrace_3426404 : CollatzResearch.WordTrace tailWord_3426404 prefixEnd_3426404 1759392168488117412292261 := by
  unfold tailWord_3426404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62485610339365483029747133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83314147119153977372996177 62485610339365483029747133)
  ·
    refine ⟨23432103877262056136155175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62485610339365483029747133 23432103877262056136155175)
    ·
      refine ⟨35148155815893084204232763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23432103877262056136155175 35148155815893084204232763)
      ·
        refine ⟨52722233723839626306349145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35148155815893084204232763 52722233723839626306349145)
        ·
          refine ⟨39541675292879719729761859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52722233723839626306349145 39541675292879719729761859)
          ·
            refine ⟨59312512939319579594642789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39541675292879719729761859 59312512939319579594642789)
            ·
              refine ⟨11121096176122421173995523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59312512939319579594642789 11121096176122421173995523)
              ·
                refine ⟨16681644264183631760993285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121096176122421173995523 16681644264183631760993285)
                ·
                  refine ⟨3127808299534430955186241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16681644264183631760993285 3127808299534430955186241)
                  ·
                    refine ⟨2345856224650823216389681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3127808299534430955186241 2345856224650823216389681)
                    ·
                      refine ⟨1759392168488117412292261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345856224650823216389681 1759392168488117412292261)
                      ·
                        rfl

theorem cell23_3426404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_3426404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426404 prefixEnd_3426404 := by exact prefixLift 3426404
  have htrace : WordTrace (prefixWord ++ tailWord_3426404) baseStart_3426404 baseEnd_3426404 := by
    simpa [prefixWord, tailWord_3426404, baseEnd_3426404] using wordTrace_append hprefix tailTrace_3426404
  have hstable : (prefixWord ++ tailWord_3426404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426404).length < 2 ^ (prefixWord ++ tailWord_3426404).sum := by decide
  have hdescent : baseEnd_3426404 < baseStart_3426404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426461 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 5]
def baseStart_3426461 : Nat := 118140960795 + 3426461 * 2 ^ 59
def prefixEnd_3426461 : Nat := 4983230072969 + 3 ^ 40 * 3426461 * 2
def baseEnd_3426461 : Nat := 195491270765047076586611

theorem tailTrace_3426461 : CollatzResearch.WordTrace tailWord_3426461 prefixEnd_3426461 195491270765047076586611 := by
  unfold tailWord_3426461
  simp only [CollatzResearch.WordTrace]
  refine ⟨124973299639524464794319237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83315533093016309862879491 124973299639524464794319237)
  ·
    refine ⟨23432493682410837148934857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124973299639524464794319237 23432493682410837148934857)
    ·
      refine ⟨17574370261808127861701143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23432493682410837148934857 17574370261808127861701143)
      ·
        refine ⟨26361555392712191792551715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17574370261808127861701143 26361555392712191792551715)
        ·
          refine ⟨39542333089068287688827573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26361555392712191792551715 39542333089068287688827573)
          ·
            refine ⟨3707093727100151970827585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39542333089068287688827573 3707093727100151970827585)
            ·
              refine ⟨2780320295325113978120689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707093727100151970827585 2780320295325113978120689)
              ·
                refine ⟨2085240221493835483590517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780320295325113978120689 2085240221493835483590517)
                ·
                  refine ⟨195491270765047076586611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2085240221493835483590517 195491270765047076586611)
                  ·
                    rfl

theorem cell23_3426461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_3426461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426461 prefixEnd_3426461 := by exact prefixLift 3426461
  have htrace : WordTrace (prefixWord ++ tailWord_3426461) baseStart_3426461 baseEnd_3426461 := by
    simpa [prefixWord, tailWord_3426461, baseEnd_3426461] using wordTrace_append hprefix tailTrace_3426461
  have hstable : (prefixWord ++ tailWord_3426461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426461).length < 2 ^ (prefixWord ++ tailWord_3426461).sum := by decide
  have hdescent : baseEnd_3426461 < baseStart_3426461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426487 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 5, 4]
def baseStart_3426487 : Nat := 118140960795 + 3426487 * 2 ^ 59
def prefixEnd_3426487 : Nat := 4983230072969 + 3 ^ 40 * 3426487 * 2
def baseEnd_3426487 : Nat := 586478262460813529184793

theorem tailTrace_3426487 : CollatzResearch.WordTrace tailWord_3426487 prefixEnd_3426487 586478262460813529184793 := by
  unfold tailWord_3426487
  simp only [CollatzResearch.WordTrace]
  refine ⟨124974247937430271234765715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83316165291620180823177143 124974247937430271234765715)
  ·
    refine ⟨187461371906145406852148573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124974247937430271234765715 187461371906145406852148573)
    ·
      refine ⟨70298014464804527569555715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187461371906145406852148573 70298014464804527569555715)
      ·
        refine ⟨105447021697206791354333573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70298014464804527569555715 105447021697206791354333573)
        ·
          refine ⟨19771316568226273378937545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105447021697206791354333573 19771316568226273378937545)
          ·
            refine ⟨14828487426169705034203159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19771316568226273378937545 14828487426169705034203159)
            ·
              refine ⟨22242731139254557551304739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14828487426169705034203159 22242731139254557551304739)
              ·
                refine ⟨33364096708881836326957109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22242731139254557551304739 33364096708881836326957109)
                ·
                  refine ⟨3127884066457672155652229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33364096708881836326957109 3127884066457672155652229)
                  ·
                    refine ⟨586478262460813529184793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127884066457672155652229 586478262460813529184793)
                    ·
                      rfl

theorem cell23_3426487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_3426487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426487 prefixEnd_3426487 := by exact prefixLift 3426487
  have htrace : WordTrace (prefixWord ++ tailWord_3426487) baseStart_3426487 baseEnd_3426487 := by
    simpa [prefixWord, tailWord_3426487, baseEnd_3426487] using wordTrace_append hprefix tailTrace_3426487
  have hstable : (prefixWord ++ tailWord_3426487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426487).length < 2 ^ (prefixWord ++ tailWord_3426487).sum := by decide
  have hdescent : baseEnd_3426487 < baseStart_3426487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426494 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3426494 : Nat := 118140960795 + 3426494 * 2 ^ 59
def prefixEnd_3426494 : Nat := 4983230072969 + 3 ^ 40 * 3426494 * 2
def baseEnd_3426494 : Nat := 1759438381747022060166847

theorem tailTrace_3426494 : CollatzResearch.WordTrace tailWord_3426494 prefixEnd_3426494 1759438381747022060166847 := by
  unfold tailWord_3426494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15621812906050613928783817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83316335498936607620180357 15621812906050613928783817)
  ·
    refine ⟨11716359679537960446587863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15621812906050613928783817 11716359679537960446587863)
    ·
      refine ⟨17574539519306940669881795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11716359679537960446587863 17574539519306940669881795)
      ·
        refine ⟨26361809278960411004822693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17574539519306940669881795 26361809278960411004822693)
        ·
          refine ⟨4942839239805077063404255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26361809278960411004822693 4942839239805077063404255)
          ·
            refine ⟨7414258859707615595106383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942839239805077063404255 7414258859707615595106383)
            ·
              refine ⟨11121388289561423392659575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7414258859707615595106383 11121388289561423392659575)
              ·
                refine ⟨16682082434342135088989363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121388289561423392659575 16682082434342135088989363)
                ·
                  refine ⟨25023123651513202633484045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16682082434342135088989363 25023123651513202633484045)
                  ·
                    refine ⟨9383671369317450987556517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25023123651513202633484045 9383671369317450987556517)
                    ·
                      refine ⟨1759438381747022060166847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9383671369317450987556517 1759438381747022060166847)
                      ·
                        rfl

theorem cell23_3426494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3426494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426494 prefixEnd_3426494 := by exact prefixLift 3426494
  have htrace : WordTrace (prefixWord ++ tailWord_3426494) baseStart_3426494 baseEnd_3426494 := by
    simpa [prefixWord, tailWord_3426494, baseEnd_3426494] using wordTrace_append hprefix tailTrace_3426494
  have hstable : (prefixWord ++ tailWord_3426494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426494).length < 2 ^ (prefixWord ++ tailWord_3426494).sum := by decide
  have hdescent : baseEnd_3426494 < baseStart_3426494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426554 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2]
def baseStart_3426554 : Nat := 118140960795 + 3426554 * 2 ^ 59
def prefixEnd_3426554 : Nat := 4983230072969 + 3 ^ 40 * 3426554 * 2
def baseEnd_3426554 : Nat := 1759469190586291825416571

theorem tailTrace_3426554 : CollatzResearch.WordTrace tailWord_3426554 prefixEnd_3426554 1759469190586291825416571 := by
  unfold tailWord_3426554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31244172907046885419363679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83317794418791694451636477 31244172907046885419363679)
  ·
    refine ⟨46866259360570328129045519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31244172907046885419363679 46866259360570328129045519)
    ·
      refine ⟨70299389040855492193568279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46866259360570328129045519 70299389040855492193568279)
      ·
        refine ⟨105449083561283238290352419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70299389040855492193568279 105449083561283238290352419)
        ·
          refine ⟨158173625341924857435528629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105449083561283238290352419 158173625341924857435528629)
          ·
            refine ⟨14828777375805455384580809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158173625341924857435528629 14828777375805455384580809)
            ·
              refine ⟨11121583031854091538435607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14828777375805455384580809 11121583031854091538435607)
              ·
                refine ⟨16682374547781137307653411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121583031854091538435607 16682374547781137307653411)
                ·
                  refine ⟨25023561821671705961480117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16682374547781137307653411 25023561821671705961480117)
                  ·
                    refine ⟨2345958920781722433888761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25023561821671705961480117 2345958920781722433888761)
                    ·
                      refine ⟨1759469190586291825416571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345958920781722433888761 1759469190586291825416571)
                      ·
                        rfl

theorem cell23_3426554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_3426554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426554 prefixEnd_3426554 := by exact prefixLift 3426554
  have htrace : WordTrace (prefixWord ++ tailWord_3426554) baseStart_3426554 baseEnd_3426554 := by
    simpa [prefixWord, tailWord_3426554, baseEnd_3426554] using wordTrace_append hprefix tailTrace_3426554
  have hstable : (prefixWord ++ tailWord_3426554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426554).length < 2 ^ (prefixWord ++ tailWord_3426554).sum := by decide
  have hdescent : baseEnd_3426554 < baseStart_3426554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426587 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5]
def baseStart_3426587 : Nat := 118140960795 + 3426587 * 2 ^ 59
def prefixEnd_3426587 : Nat := 4983230072969 + 3 ^ 40 * 3426587 * 2
def baseEnd_3426587 : Nat := 1759486135447890196303919

theorem tailTrace_3426587 : CollatzResearch.WordTrace tailWord_3426587 prefixEnd_3426587 1759486135447890196303919 := by
  unfold tailWord_3426587
  simp only [CollatzResearch.WordTrace]
  refine ⟨124977895237067988313406015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83318596824711992208937343 124977895237067988313406015)
  ·
    refine ⟨187466842855601982470109023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124977895237067988313406015 187466842855601982470109023)
    ·
      refine ⟨281200264283402973705163535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187466842855601982470109023 281200264283402973705163535)
      ·
        refine ⟨421800396425104460557745303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281200264283402973705163535 421800396425104460557745303)
        ·
          refine ⟨632700594637656690836617955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421800396425104460557745303 632700594637656690836617955)
          ·
            refine ⟨949050891956485036254926933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632700594637656690836617955 949050891956485036254926933)
            ·
              refine ⟨11121690140115059018612425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 949050891956485036254926933 11121690140115059018612425)
              ·
                refine ⟨8341267605086294263959319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11121690140115059018612425 8341267605086294263959319)
                ·
                  refine ⟨12511901407629441395938979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341267605086294263959319 12511901407629441395938979)
                  ·
                    refine ⟨18767852111444162093908469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12511901407629441395938979 18767852111444162093908469)
                    ·
                      refine ⟨1759486135447890196303919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18767852111444162093908469 1759486135447890196303919)
                      ·
                        rfl

theorem cell23_3426587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_3426587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426587 prefixEnd_3426587 := by exact prefixLift 3426587
  have htrace : WordTrace (prefixWord ++ tailWord_3426587) baseStart_3426587 baseEnd_3426587 := by
    simpa [prefixWord, tailWord_3426587, baseEnd_3426587] using wordTrace_append hprefix tailTrace_3426587
  have hstable : (prefixWord ++ tailWord_3426587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426587).length < 2 ^ (prefixWord ++ tailWord_3426587).sum := by decide
  have hdescent : baseEnd_3426587 < baseStart_3426587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426605 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3426605 : Nat := 118140960795 + 3426605 * 2 ^ 59
def prefixEnd_3426605 : Nat := 4983230072969 + 3 ^ 40 * 3426605 * 2
def baseEnd_3426605 : Nat := 1759495378099671125878837

theorem tailTrace_3426605 : CollatzResearch.WordTrace tailWord_3426605 prefixEnd_3426605 1759495378099671125878837 := by
  unfold tailWord_3426605
  simp only [CollatzResearch.WordTrace]
  refine ⟨124978551751002777387561269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83319034500668518258374179 124978551751002777387561269)
  ·
    refine ⟨11716739226656510380083869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124978551751002777387561269 11716739226656510380083869)
    ·
      refine ⟨4393777209996191392531451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11716739226656510380083869 4393777209996191392531451)
      ·
        refine ⟨6590665814994287088797177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393777209996191392531451 6590665814994287088797177)
        ·
          refine ⟨4942999361245715316597883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6590665814994287088797177 4942999361245715316597883)
          ·
            refine ⟨7414499041868572974896825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942999361245715316597883 7414499041868572974896825)
            ·
              refine ⟨5560874281401429731172619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414499041868572974896825 5560874281401429731172619)
              ·
                refine ⟨8341311422102144596758929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560874281401429731172619 8341311422102144596758929)
                ·
                  refine ⟨6255983566576608447569197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8341311422102144596758929 6255983566576608447569197)
                  ·
                    refine ⟨2345993837466228167838449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6255983566576608447569197 2345993837466228167838449)
                    ·
                      refine ⟨1759495378099671125878837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2345993837466228167838449 1759495378099671125878837)
                      ·
                        rfl

theorem cell23_3426605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3426605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426605 prefixEnd_3426605 := by exact prefixLift 3426605
  have htrace : WordTrace (prefixWord ++ tailWord_3426605) baseStart_3426605 baseEnd_3426605 := by
    simpa [prefixWord, tailWord_3426605, baseEnd_3426605] using wordTrace_append hprefix tailTrace_3426605
  have hstable : (prefixWord ++ tailWord_3426605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426605).length < 2 ^ (prefixWord ++ tailWord_3426605).sum := by decide
  have hdescent : baseEnd_3426605 < baseStart_3426605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426661 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_3426661 : Nat := 118140960795 + 3426661 * 2 ^ 59
def prefixEnd_3426661 : Nat := 4983230072969 + 3 ^ 40 * 3426661 * 2
def baseEnd_3426661 : Nat := 1759524133016322906778579

theorem tailTrace_3426661 : CollatzResearch.WordTrace tailWord_3426661 prefixEnd_3426661 1759524133016322906778579 := by
  unfold tailWord_3426661
  simp only [CollatzResearch.WordTrace]
  refine ⟨124980594238799898951599837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83320396159199932634399891 124980594238799898951599837)
  ·
    refine ⟨46867722839549962106849939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124980594238799898951599837 46867722839549962106849939)
    ·
      refine ⟨70301584259324943160274909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46867722839549962106849939 70301584259324943160274909)
      ·
        refine ⟨26363094097246853685103091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70301584259324943160274909 26363094097246853685103091)
        ·
          refine ⟨39544641145870280527654637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26363094097246853685103091 39544641145870280527654637)
          ·
            refine ⟨14829240429701355197870489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39544641145870280527654637 14829240429701355197870489)
            ·
              refine ⟨11121930322276016398402867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14829240429701355197870489 11121930322276016398402867)
              ·
                refine ⟨16682895483414024597604301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11121930322276016398402867 16682895483414024597604301)
                ·
                  refine ⟨6256085806280259224101613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16682895483414024597604301 6256085806280259224101613)
                  ·
                    refine ⟨2346032177355097209038105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6256085806280259224101613 2346032177355097209038105)
                    ·
                      refine ⟨1759524133016322906778579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346032177355097209038105 1759524133016322906778579)
                      ·
                        rfl

theorem cell23_3426661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_3426661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426661 prefixEnd_3426661 := by exact prefixLift 3426661
  have htrace : WordTrace (prefixWord ++ tailWord_3426661) baseStart_3426661 baseEnd_3426661 := by
    simpa [prefixWord, tailWord_3426661, baseEnd_3426661] using wordTrace_append hprefix tailTrace_3426661
  have hstable : (prefixWord ++ tailWord_3426661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426661).length < 2 ^ (prefixWord ++ tailWord_3426661).sum := by decide
  have hdescent : baseEnd_3426661 < baseStart_3426661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426687 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_3426687 : Nat := 118140960795 + 3426687 * 2 ^ 59
def prefixEnd_3426687 : Nat := 4983230072969 + 3 ^ 40 * 3426687 * 2
def baseEnd_3426687 : Nat := 1759537483513339805053459

theorem tailTrace_3426687 : CollatzResearch.WordTrace tailWord_3426687 prefixEnd_3426687 1759537483513339805053459 := by
  unfold tailWord_3426687
  simp only [CollatzResearch.WordTrace]
  refine ⟨124981542536705705392046315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83321028357803803594697543 124981542536705705392046315)
  ·
    refine ⟨187472313805058558088069473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124981542536705705392046315 187472313805058558088069473)
    ·
      refine ⟨140604235353793918566052105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187472313805058558088069473 140604235353793918566052105)
      ·
        refine ⟨105453176515345438924539079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140604235353793918566052105 105453176515345438924539079)
        ·
          refine ⟨158179764773018158386808619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105453176515345438924539079 158179764773018158386808619)
          ·
            refine ⟨237269647159527237580212929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158179764773018158386808619 237269647159527237580212929)
            ·
              refine ⟨177952235369645428185159697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237269647159527237580212929 177952235369645428185159697)
              ·
                refine ⟨133464176527234071138869773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177952235369645428185159697 133464176527234071138869773)
                ·
                  refine ⟨50049066197712776677076165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133464176527234071138869773 50049066197712776677076165)
                  ·
                    refine ⟨9384199912071145626951781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50049066197712776677076165 9384199912071145626951781)
                    ·
                      refine ⟨1759537483513339805053459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9384199912071145626951781 1759537483513339805053459)
                      ·
                        rfl

theorem cell23_3426687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_3426687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426687 prefixEnd_3426687 := by exact prefixLift 3426687
  have htrace : WordTrace (prefixWord ++ tailWord_3426687) baseStart_3426687 baseEnd_3426687 := by
    simpa [prefixWord, tailWord_3426687, baseEnd_3426687] using wordTrace_append hprefix tailTrace_3426687
  have hstable : (prefixWord ++ tailWord_3426687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426687).length < 2 ^ (prefixWord ++ tailWord_3426687).sum := by decide
  have hdescent : baseEnd_3426687 < baseStart_3426687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426714 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_3426714 : Nat := 118140960795 + 3426714 * 2 ^ 59
def prefixEnd_3426714 : Nat := 4983230072969 + 3 ^ 40 * 3426714 * 2
def baseEnd_3426714 : Nat := 195505705276779022157315

theorem tailTrace_3426714 : CollatzResearch.WordTrace tailWord_3426714 prefixEnd_3426714 195505705276779022157315 := by
  unfold tailWord_3426714
  simp only [CollatzResearch.WordTrace]
  refine ⟨31245631826901972250819799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83321684871738592668852797 31245631826901972250819799)
  ·
    refine ⟨46868447740352958376229699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31245631826901972250819799 46868447740352958376229699)
    ·
      refine ⟨70302671610529437564344549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46868447740352958376229699 70302671610529437564344549)
      ·
        refine ⟨13181750926974269543314603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70302671610529437564344549 13181750926974269543314603)
        ·
          refine ⟨19772626390461404314971905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13181750926974269543314603 19772626390461404314971905)
          ·
            refine ⟨14829469792846053236228929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19772626390461404314971905 14829469792846053236228929)
            ·
              refine ⟨11122102344634539927171697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14829469792846053236228929 11122102344634539927171697)
              ·
                refine ⟨8341576758475904945378773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11122102344634539927171697 8341576758475904945378773)
                ·
                  refine ⟨195505705276779022157315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8341576758475904945378773 195505705276779022157315)
                  ·
                    rfl

theorem cell23_3426714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_3426714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426714 prefixEnd_3426714 := by exact prefixLift 3426714
  have htrace : WordTrace (prefixWord ++ tailWord_3426714) baseStart_3426714 baseEnd_3426714 := by
    simpa [prefixWord, tailWord_3426714, baseEnd_3426714] using wordTrace_append hprefix tailTrace_3426714
  have hstable : (prefixWord ++ tailWord_3426714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426714).length < 2 ^ (prefixWord ++ tailWord_3426714).sum := by decide
  have hdescent : baseEnd_3426714 < baseStart_3426714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426724 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_3426724 : Nat := 118140960795 + 3426724 * 2 ^ 59
def prefixEnd_3426724 : Nat := 4983230072969 + 3 ^ 40 * 3426724 * 2
def baseEnd_3426724 : Nat := 1759556482297556160290789

theorem tailTrace_3426724 : CollatzResearch.WordTrace tailWord_3426724 prefixEnd_3426724 1759556482297556160290789 := by
  unfold tailWord_3426724
  simp only [CollatzResearch.WordTrace]
  refine ⟨62491446018785830355571613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83321928025047773807428817 62491446018785830355571613)
  ·
    refine ⟨23434292257044686383339355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62491446018785830355571613 23434292257044686383339355)
    ·
      refine ⟨35151438385567029575009033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23434292257044686383339355 35151438385567029575009033)
      ·
        refine ⟨26363578789175272181256775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35151438385567029575009033 26363578789175272181256775)
        ·
          refine ⟨39545368183762908271885163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26363578789175272181256775 39545368183762908271885163)
          ·
            refine ⟨59318052275644362407827745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39545368183762908271885163 59318052275644362407827745)
            ·
              refine ⟨44488539206733271805870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59318052275644362407827745 44488539206733271805870809)
              ·
                refine ⟨33366404405049953854403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44488539206733271805870809 33366404405049953854403107)
                ·
                  refine ⟨50049606607574930781604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33366404405049953854403107 50049606607574930781604661)
                  ·
                    refine ⟨4692150619460149760775437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50049606607574930781604661 4692150619460149760775437)
                    ·
                      refine ⟨1759556482297556160290789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4692150619460149760775437 1759556482297556160290789)
                      ·
                        rfl

theorem cell23_3426724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_3426724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426724 prefixEnd_3426724 := by exact prefixLift 3426724
  have htrace : WordTrace (prefixWord ++ tailWord_3426724) baseStart_3426724 baseEnd_3426724 := by
    simpa [prefixWord, tailWord_3426724, baseEnd_3426724] using wordTrace_append hprefix tailTrace_3426724
  have hstable : (prefixWord ++ tailWord_3426724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426724).length < 2 ^ (prefixWord ++ tailWord_3426724).sum := by decide
  have hdescent : baseEnd_3426724 < baseStart_3426724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426801 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_3426801 : Nat := 118140960795 + 3426801 * 2 ^ 59
def prefixEnd_3426801 : Nat := 4983230072969 + 3 ^ 40 * 3426801 * 2
def baseEnd_3426801 : Nat := 1759596020307952359027935

theorem tailTrace_3426801 : CollatzResearch.WordTrace tailWord_3426801 prefixEnd_3426801 1759596020307952359027935 := by
  unfold tailWord_3426801
  simp only [CollatzResearch.WordTrace]
  refine ⟨124985700458292702861696257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83323800305528468574464171 124985700458292702861696257)
  ·
    refine ⟨93739275343719527146272193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124985700458292702861696257 93739275343719527146272193)
    ·
      refine ⟨70304456507789645359704145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93739275343719527146272193 70304456507789645359704145)
      ·
        refine ⟨52728342380842234019778109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70304456507789645359704145 52728342380842234019778109)
        ·
          refine ⟨19773128392815837757416791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52728342380842234019778109 19773128392815837757416791)
          ·
            refine ⟨29659692589223756636125187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19773128392815837757416791 29659692589223756636125187)
            ·
              refine ⟨44489538883835634954187781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29659692589223756636125187 44489538883835634954187781)
              ·
                refine ⟨8341788540719181553910209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44489538883835634954187781 8341788540719181553910209)
                ·
                  refine ⟨6256341405539386165432657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8341788540719181553910209 6256341405539386165432657)
                  ·
                    refine ⟨4692256054154539624074493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6256341405539386165432657 4692256054154539624074493)
                    ·
                      refine ⟨1759596020307952359027935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4692256054154539624074493 1759596020307952359027935)
                      ·
                        rfl

theorem cell23_3426801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_3426801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426801 prefixEnd_3426801 := by exact prefixLift 3426801
  have htrace : WordTrace (prefixWord ++ tailWord_3426801) baseStart_3426801 baseEnd_3426801 := by
    simpa [prefixWord, tailWord_3426801, baseEnd_3426801] using wordTrace_append hprefix tailTrace_3426801
  have hstable : (prefixWord ++ tailWord_3426801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426801).length < 2 ^ (prefixWord ++ tailWord_3426801).sum := by decide
  have hdescent : baseEnd_3426801 < baseStart_3426801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426808 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 1, 4]
def baseStart_3426808 : Nat := 118140960795 + 3426808 * 2 ^ 59
def prefixEnd_3426808 : Nat := 4983230072969 + 3 ^ 40 * 3426808 * 2
def baseEnd_3426808 : Nat := 586533204890844610546801

theorem tailTrace_3426808 : CollatzResearch.WordTrace tailWord_3426808 prefixEnd_3426808 586533204890844610546801 := by
  unfold tailWord_3426808
  simp only [CollatzResearch.WordTrace]
  refine ⟨62492977884633671528600539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83323970512844895371467385 62492977884633671528600539)
  ·
    refine ⟨93739466826950507292900809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62492977884633671528600539 93739466826950507292900809)
    ·
      refine ⟨70304600120212880469675607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93739466826950507292900809 70304600120212880469675607)
      ·
        refine ⟨105456900180319320704513411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70304600120212880469675607 105456900180319320704513411)
        ·
          refine ⟨158185350270478981056770117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105456900180319320704513411 158185350270478981056770117)
          ·
            refine ⟨29659753175714808948144397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158185350270478981056770117 29659753175714808948144397)
            ·
              refine ⟨11122407440893053355554149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29659753175714808948144397 11122407440893053355554149)
              ·
                refine ⟨2085451395167447504166403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11122407440893053355554149 2085451395167447504166403)
                ·
                  refine ⟨3128177092751171256249605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085451395167447504166403 3128177092751171256249605)
                  ·
                    refine ⟨586533204890844610546801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128177092751171256249605 586533204890844610546801)
                    ·
                      rfl

theorem cell23_3426808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_3426808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426808 prefixEnd_3426808 := by exact prefixLift 3426808
  have htrace : WordTrace (prefixWord ++ tailWord_3426808) baseStart_3426808 baseEnd_3426808 := by
    simpa [prefixWord, tailWord_3426808, baseEnd_3426808] using wordTrace_append hprefix tailTrace_3426808
  have hstable : (prefixWord ++ tailWord_3426808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426808).length < 2 ^ (prefixWord ++ tailWord_3426808).sum := by decide
  have hdescent : baseEnd_3426808 < baseStart_3426808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426831 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 3]
def baseStart_3426831 : Nat := 118140960795 + 3426831 * 2 ^ 59
def prefixEnd_3426831 : Nat := 4983230072969 + 3 ^ 40 * 3426831 * 2
def baseEnd_3426831 : Nat := 1759611424727587241652797

theorem tailTrace_3426831 : CollatzResearch.WordTrace tailWord_3426831 prefixEnd_3426831 1759611424727587241652797 := by
  unfold tailWord_3426831
  simp only [CollatzResearch.WordTrace]
  refine ⟨124986794648184017985288347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83324529765456011990192231 124986794648184017985288347)
  ·
    refine ⟨187480191972276026977932521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124986794648184017985288347 187480191972276026977932521)
    ·
      refine ⟨140610143979207020233449391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187480191972276026977932521 140610143979207020233449391)
      ·
        refine ⟨210915215968810530350174087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140610143979207020233449391 210915215968810530350174087)
        ·
          refine ⟨316372823953215795525261131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210915215968810530350174087 316372823953215795525261131)
          ·
            refine ⟨474559235929823693287891697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316372823953215795525261131 474559235929823693287891697)
            ·
              refine ⟨355919426947367769965918773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474559235929823693287891697 355919426947367769965918773)
              ·
                refine ⟨33367446276315728434304885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355919426947367769965918773 33367446276315728434304885)
                ·
                  refine ⟨3128198088404599540716083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33367446276315728434304885 3128198088404599540716083)
                  ·
                    refine ⟨4692297132606899311074125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128198088404599540716083 4692297132606899311074125)
                    ·
                      refine ⟨1759611424727587241652797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4692297132606899311074125 1759611424727587241652797)
                      ·
                        rfl

theorem cell23_3426831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_3426831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426831 prefixEnd_3426831 := by exact prefixLift 3426831
  have htrace : WordTrace (prefixWord ++ tailWord_3426831) baseStart_3426831 baseEnd_3426831 := by
    simpa [prefixWord, tailWord_3426831, baseEnd_3426831] using wordTrace_append hprefix tailTrace_3426831
  have hstable : (prefixWord ++ tailWord_3426831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426831).length < 2 ^ (prefixWord ++ tailWord_3426831).sum := by decide
  have hdescent : baseEnd_3426831 < baseStart_3426831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426841 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 5, 2]
def baseStart_3426841 : Nat := 118140960795 + 3426841 * 2 ^ 59
def prefixEnd_3426841 : Nat := 4983230072969 + 3 ^ 40 * 3426841 * 2
def baseEnd_3426841 : Nat := 1759616559534132202527751

theorem tailTrace_3426841 : CollatzResearch.WordTrace tailWord_3426841 prefixEnd_3426841 1759616559534132202527751 := by
  unfold tailWord_3426841
  simp only [CollatzResearch.WordTrace]
  refine ⟨124987159378147789693152377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83324772918765193128768251 124987159378147789693152377)
  ·
    refine ⟨93740369533610842269864283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124987159378147789693152377 93740369533610842269864283)
    ·
      refine ⟨140610554300416263404796425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93740369533610842269864283 140610554300416263404796425)
      ·
        refine ⟨105457915725312197553597319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140610554300416263404796425 105457915725312197553597319)
        ·
          refine ⟨158186873587968296330395979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105457915725312197553597319 158186873587968296330395979)
          ·
            refine ⟨237280310381952444495593969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158186873587968296330395979 237280310381952444495593969)
            ·
              refine ⟨177960232786464333371695477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237280310381952444495593969 177960232786464333371695477)
              ·
                refine ⟨16683771823731031253596451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177960232786464333371695477 16683771823731031253596451)
                ·
                  refine ⟨25025657735596546880394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16683771823731031253596451 25025657735596546880394677)
                  ·
                    refine ⟨2346155412712176270037001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25025657735596546880394677 2346155412712176270037001)
                    ·
                      refine ⟨1759616559534132202527751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346155412712176270037001 1759616559534132202527751)
                      ·
                        rfl

theorem cell23_3426841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_3426841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426841 prefixEnd_3426841 := by exact prefixLift 3426841
  have htrace : WordTrace (prefixWord ++ tailWord_3426841) baseStart_3426841 baseEnd_3426841 := by
    simpa [prefixWord, tailWord_3426841, baseEnd_3426841] using wordTrace_append hprefix tailTrace_3426841
  have hstable : (prefixWord ++ tailWord_3426841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426841).length < 2 ^ (prefixWord ++ tailWord_3426841).sum := by decide
  have hdescent : baseEnd_3426841 < baseStart_3426841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426864 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_3426864 : Nat := 118140960795 + 3426864 * 2 ^ 59
def prefixEnd_3426864 : Nat := 4983230072969 + 3 ^ 40 * 3426864 * 2
def baseEnd_3426864 : Nat := 586542789863061870846715

theorem tailTrace_3426864 : CollatzResearch.WordTrace tailWord_3426864 prefixEnd_3426864 586542789863061870846715 := by
  unfold tailWord_3426864
  simp only [CollatzResearch.WordTrace]
  refine ⟨62493999128532232310619823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83325332171376309747493097 62493999128532232310619823)
  ·
    refine ⟨93740998692798348465929735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62493999128532232310619823 93740998692798348465929735)
    ·
      refine ⟨140611498039197522698894603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93740998692798348465929735 140611498039197522698894603)
      ·
        refine ⟨210917247058796284048341905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140611498039197522698894603 210917247058796284048341905)
        ·
          refine ⟨158187935294097213036256429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210917247058796284048341905 158187935294097213036256429)
          ·
            refine ⟨59320475735286454888596161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158187935294097213036256429 59320475735286454888596161)
            ·
              refine ⟨44490356801464841166447121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59320475735286454888596161 44490356801464841166447121)
              ·
                refine ⟨33367767601098630874835341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44490356801464841166447121 33367767601098630874835341)
                ·
                  refine ⟨12512912850411986578063253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33367767601098630874835341 12512912850411986578063253)
                  ·
                    refine ⟨586542789863061870846715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12512912850411986578063253 586542789863061870846715)
                    ·
                      rfl

theorem cell23_3426864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_3426864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426864 prefixEnd_3426864 := by exact prefixLift 3426864
  have htrace : WordTrace (prefixWord ++ tailWord_3426864) baseStart_3426864 baseEnd_3426864 := by
    simpa [prefixWord, tailWord_3426864, baseEnd_3426864] using wordTrace_append hprefix tailTrace_3426864
  have hstable : (prefixWord ++ tailWord_3426864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426864).length < 2 ^ (prefixWord ++ tailWord_3426864).sum := by decide
  have hdescent : baseEnd_3426864 < baseStart_3426864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426865 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 1, 1, 3]
def baseStart_3426865 : Nat := 118140960795 + 3426865 * 2 ^ 59
def prefixEnd_3426865 : Nat := 4983230072969 + 3 ^ 40 * 3426865 * 2
def baseEnd_3426865 : Nat := 1759628883069840108627641

theorem tailTrace_3426865 : CollatzResearch.WordTrace tailWord_3426865 prefixEnd_3426865 1759628883069840108627641 := by
  unfold tailWord_3426865
  simp only [CollatzResearch.WordTrace]
  refine ⟨124988034730060841792026049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83325356486707227861350699 124988034730060841792026049)
  ·
    refine ⟨93741026047545631344019537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124988034730060841792026049 93741026047545631344019537)
    ·
      refine ⟨70305769535659223508014653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93741026047545631344019537 70305769535659223508014653)
      ·
        refine ⟨26364663575872208815505495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70305769535659223508014653 26364663575872208815505495)
        ·
          refine ⟨39546995363808313223258243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26364663575872208815505495 39546995363808313223258243)
          ·
            refine ⟨59320493045712469834887365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39546995363808313223258243 59320493045712469834887365)
            ·
              refine ⟨11122592446071088094041381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59320493045712469834887365 11122592446071088094041381)
              ·
                refine ⟨2085486083638329017632759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11122592446071088094041381 2085486083638329017632759)
                ·
                  refine ⟨3128229125457493526449139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085486083638329017632759 3128229125457493526449139)
                  ·
                    refine ⟨4692343688186240289673709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128229125457493526449139 4692343688186240289673709)
                    ·
                      refine ⟨1759628883069840108627641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4692343688186240289673709 1759628883069840108627641)
                      ·
                        rfl

theorem cell23_3426865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_3426865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426865 prefixEnd_3426865 := by exact prefixLift 3426865
  have htrace : WordTrace (prefixWord ++ tailWord_3426865) baseStart_3426865 baseEnd_3426865 := by
    simpa [prefixWord, tailWord_3426865, baseEnd_3426865] using wordTrace_append hprefix tailTrace_3426865
  have hstable : (prefixWord ++ tailWord_3426865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426865).length < 2 ^ (prefixWord ++ tailWord_3426865).sum := by decide
  have hdescent : baseEnd_3426865 < baseStart_3426865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426891 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3]
def baseStart_3426891 : Nat := 118140960795 + 3426891 * 2 ^ 59
def prefixEnd_3426891 : Nat := 4983230072969 + 3 ^ 40 * 3426891 * 2
def baseEnd_3426891 : Nat := 1759642233566857006902521

theorem tailTrace_3426891 : CollatzResearch.WordTrace tailWord_3426891 prefixEnd_3426891 1759642233566857006902521 := by
  unfold tailWord_3426891
  simp only [CollatzResearch.WordTrace]
  refine ⟨124988983027966648232472527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83325988685311098821648351 124988983027966648232472527)
  ·
    refine ⟨187483474541949972348708791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124988983027966648232472527 187483474541949972348708791)
    ·
      refine ⟨281225211812924958523063187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187483474541949972348708791 281225211812924958523063187)
      ·
        refine ⟨421837817719387437784594781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281225211812924958523063187 421837817719387437784594781)
        ·
          refine ⟨158189181644770289169223043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421837817719387437784594781 158189181644770289169223043)
          ·
            refine ⟨237283772467155433753834565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158189181644770289169223043 237283772467155433753834565)
            ·
              refine ⟨44490707337591643828843981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 237283772467155433753834565 44490707337591643828843981)
              ·
                refine ⟨16684015251596866435816493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44490707337591643828843981 16684015251596866435816493)
                ·
                  refine ⟨6256505719348824913431185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16684015251596866435816493 6256505719348824913431185)
                  ·
                    refine ⟨4692379289511618685073389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6256505719348824913431185 4692379289511618685073389)
                    ·
                      refine ⟨1759642233566857006902521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4692379289511618685073389 1759642233566857006902521)
                      ·
                        rfl

theorem cell23_3426891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3].length) (baseStart_3426891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426891 prefixEnd_3426891 := by exact prefixLift 3426891
  have htrace : WordTrace (prefixWord ++ tailWord_3426891) baseStart_3426891 baseEnd_3426891 := by
    simpa [prefixWord, tailWord_3426891, baseEnd_3426891] using wordTrace_append hprefix tailTrace_3426891
  have hstable : (prefixWord ++ tailWord_3426891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426891).length < 2 ^ (prefixWord ++ tailWord_3426891).sum := by decide
  have hdescent : baseEnd_3426891 < baseStart_3426891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426901 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3426901 : Nat := 118140960795 + 3426901 * 2 ^ 59
def prefixEnd_3426901 : Nat := 4983230072969 + 3 ^ 40 * 3426901 * 2
def baseEnd_3426901 : Nat := 1759647368373401967777475

theorem tailTrace_3426901 : CollatzResearch.WordTrace tailWord_3426901 prefixEnd_3426901 1759647368373401967777475 := by
  unfold tailWord_3426901
  simp only [CollatzResearch.WordTrace]
  refine ⟨124989347757930419940336557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83326231838620279960224371 124989347757930419940336557)
  ·
    refine ⟨46871005409223907477626209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124989347757930419940336557 46871005409223907477626209)
    ·
      refine ⟨35153254056917930608219657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46871005409223907477626209 35153254056917930608219657)
      ·
        refine ⟨26364940542688447956164743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35153254056917930608219657 26364940542688447956164743)
        ·
          refine ⟨39547410814032671934247115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26364940542688447956164743 39547410814032671934247115)
          ·
            refine ⟨59321116221049007901370673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39547410814032671934247115 59321116221049007901370673)
            ·
              refine ⟨44490837165786755926028005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59321116221049007901370673 44490837165786755926028005)
              ·
                refine ⟨8342031968585016736130251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44490837165786755926028005 8342031968585016736130251)
                ·
                  refine ⟨12513047952877525104195377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342031968585016736130251 12513047952877525104195377)
                  ·
                    refine ⟨9384785964658143828146533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12513047952877525104195377 9384785964658143828146533)
                    ·
                      refine ⟨1759647368373401967777475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9384785964658143828146533 1759647368373401967777475)
                      ·
                        rfl

theorem cell23_3426901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3426901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426901 prefixEnd_3426901 := by exact prefixLift 3426901
  have htrace : WordTrace (prefixWord ++ tailWord_3426901) baseStart_3426901 baseEnd_3426901 := by
    simpa [prefixWord, tailWord_3426901, baseEnd_3426901] using wordTrace_append hprefix tailTrace_3426901
  have hstable : (prefixWord ++ tailWord_3426901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426901).length < 2 ^ (prefixWord ++ tailWord_3426901).sum := by decide
  have hdescent : baseEnd_3426901 < baseStart_3426901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426972 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3426972 : Nat := 118140960795 + 3426972 * 2 ^ 59
def prefixEnd_3426972 : Nat := 4983230072969 + 3 ^ 40 * 3426972 * 2
def baseEnd_3426972 : Nat := 1759683825499871189989649

theorem tailTrace_3426972 : CollatzResearch.WordTrace tailWord_3426972 prefixEnd_3426972 1759683825499871189989649 := by
  unfold tailWord_3426972
  simp only [CollatzResearch.WordTrace]
  refine ⟨62495968670336599533085585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83327958227115466044114113 62495968670336599533085585)
  ·
    refine ⟨46871976502752449649814189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62495968670336599533085585 46871976502752449649814189)
    ·
      refine ⟨17576991188532168618680321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46871976502752449649814189 17576991188532168618680321)
      ·
        refine ⟨13182743391399126464010241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17576991188532168618680321 13182743391399126464010241)
        ·
          refine ⟨9887057543549344848007681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13182743391399126464010241 9887057543549344848007681)
          ·
            refine ⟨7415293157662008636005761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887057543549344848007681 7415293157662008636005761)
            ·
              refine ⟨5561469868246506477004321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415293157662008636005761 5561469868246506477004321)
              ·
                refine ⟨4171102401184879857753241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561469868246506477004321 4171102401184879857753241)
                ·
                  refine ⟨3128326800888659893314931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171102401184879857753241 3128326800888659893314931)
                  ·
                    refine ⟨4692490201332989839972397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128326800888659893314931 4692490201332989839972397)
                    ·
                      refine ⟨1759683825499871189989649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4692490201332989839972397 1759683825499871189989649)
                      ·
                        rfl

theorem cell23_3426972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3426972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426972 prefixEnd_3426972 := by exact prefixLift 3426972
  have htrace : WordTrace (prefixWord ++ tailWord_3426972) baseStart_3426972 baseEnd_3426972 := by
    simpa [prefixWord, tailWord_3426972, baseEnd_3426972] using wordTrace_append hprefix tailTrace_3426972
  have hstable : (prefixWord ++ tailWord_3426972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426972).length < 2 ^ (prefixWord ++ tailWord_3426972).sum := by decide
  have hdescent : baseEnd_3426972 < baseStart_3426972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426991 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_3426991 : Nat := 118140960795 + 3426991 * 2 ^ 59
def prefixEnd_3426991 : Nat := 4983230072969 + 3 ^ 40 * 3426991 * 2
def baseEnd_3426991 : Nat := 1759693581632306615652061

theorem tailTrace_3426991 : CollatzResearch.WordTrace tailWord_3426991 prefixEnd_3426991 1759693581632306615652061 := by
  unfold tailWord_3426991
  simp only [CollatzResearch.WordTrace]
  refine ⟨124992630327604365311112827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83328420218402910207408551 124992630327604365311112827)
  ·
    refine ⟨187488945491406547966669241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124992630327604365311112827 187488945491406547966669241)
    ·
      refine ⟨140616709118554910975001931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187488945491406547966669241 140616709118554910975001931)
      ·
        refine ⟨210925063677832366462502897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140616709118554910975001931 210925063677832366462502897)
        ·
          refine ⟨158193797758374274846877173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210925063677832366462502897 158193797758374274846877173)
          ·
            refine ⟨14830668539847588266894735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158193797758374274846877173 14830668539847588266894735)
            ·
              refine ⟨22246002809771382400342103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830668539847588266894735 22246002809771382400342103)
              ·
                refine ⟨33369004214657073600513155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22246002809771382400342103 33369004214657073600513155)
                ·
                  refine ⟨50053506321985610400769733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33369004214657073600513155 50053506321985610400769733)
                  ·
                    refine ⟨9385032435372301950144325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50053506321985610400769733 9385032435372301950144325)
                    ·
                      refine ⟨1759693581632306615652061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9385032435372301950144325 1759693581632306615652061)
                      ·
                        rfl

theorem cell23_3426991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_3426991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426991 prefixEnd_3426991 := by exact prefixLift 3426991
  have htrace : WordTrace (prefixWord ++ tailWord_3426991) baseStart_3426991 baseEnd_3426991 := by
    simpa [prefixWord, tailWord_3426991, baseEnd_3426991] using wordTrace_append hprefix tailTrace_3426991
  have hstable : (prefixWord ++ tailWord_3426991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426991).length < 2 ^ (prefixWord ++ tailWord_3426991).sum := by decide
  have hdescent : baseEnd_3426991 < baseStart_3426991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3426995 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 1, 4, 2]
def baseStart_3426995 : Nat := 118140960795 + 3426995 * 2 ^ 59
def prefixEnd_3426995 : Nat := 4983230072969 + 3 ^ 40 * 3426995 * 2
def baseEnd_3426995 : Nat := 1759695635554924600002043

theorem tailTrace_3426995 : CollatzResearch.WordTrace tailWord_3426995 prefixEnd_3426995 1759695635554924600002043 := by
  unfold tailWord_3426995
  simp only [CollatzResearch.WordTrace]
  refine ⟨124992776219589873994258439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83328517479726582662838959 124992776219589873994258439)
  ·
    refine ⟨187489164329384810991387659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124992776219589873994258439 187489164329384810991387659)
    ·
      refine ⟨281233746494077216487081489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187489164329384810991387659 281233746494077216487081489)
      ·
        refine ⟨210925309870557912365311117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281233746494077216487081489 210925309870557912365311117)
        ·
          refine ⟨79096991201459217136991669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210925309870557912365311117 79096991201459217136991669)
          ·
            refine ⟨7415342925136801606592969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79096991201459217136991669 7415342925136801606592969)
            ·
              refine ⟨5561507193852601204944727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415342925136801606592969 5561507193852601204944727)
              ·
                refine ⟨8342260790778901807417091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561507193852601204944727 8342260790778901807417091)
                ·
                  refine ⟨12513391186168352711125637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342260790778901807417091 12513391186168352711125637)
                  ·
                    refine ⟨2346260847406566133336057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12513391186168352711125637 2346260847406566133336057)
                    ·
                      refine ⟨1759695635554924600002043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346260847406566133336057 1759695635554924600002043)
                      ·
                        rfl

theorem cell23_3426995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4, 2].length) (baseStart_3426995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3426995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3426995 prefixEnd_3426995 := by exact prefixLift 3426995
  have htrace : WordTrace (prefixWord ++ tailWord_3426995) baseStart_3426995 baseEnd_3426995 := by
    simpa [prefixWord, tailWord_3426995, baseEnd_3426995] using wordTrace_append hprefix tailTrace_3426995
  have hstable : (prefixWord ++ tailWord_3426995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3426995).length < 2 ^ (prefixWord ++ tailWord_3426995).sum := by decide
  have hdescent : baseEnd_3426995 < baseStart_3426995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3426995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427029 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3427029 : Nat := 118140960795 + 3427029 * 2 ^ 59
def prefixEnd_3427029 : Nat := 4983230072969 + 3 ^ 40 * 3427029 * 2
def baseEnd_3427029 : Nat := 1759713093897177466976887

theorem tailTrace_3427029 : CollatzResearch.WordTrace tailWord_3427029 prefixEnd_3427029 1759713093897177466976887 := by
  unfold tailWord_3427029
  simp only [CollatzResearch.WordTrace]
  refine ⟨124994016301466697800996141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83329344200977798533997427 124994016301466697800996141)
  ·
    refine ⟨46872756113050011675373553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124994016301466697800996141 46872756113050011675373553)
    ·
      refine ⟨35154567084787508756530165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46872756113050011675373553 35154567084787508756530165)
      ·
        refine ⟨3295740664198828945924703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35154567084787508756530165 3295740664198828945924703)
        ·
          refine ⟨4943610996298243418887055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295740664198828945924703 4943610996298243418887055)
          ·
            refine ⟨7415416494447365128330583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943610996298243418887055 7415416494447365128330583)
            ·
              refine ⟨11123124741671047692495875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415416494447365128330583 11123124741671047692495875)
              ·
                refine ⟨16684687112506571538743813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123124741671047692495875 16684687112506571538743813)
                ·
                  refine ⟨3128378833594982163514465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16684687112506571538743813 3128378833594982163514465)
                  ·
                    refine ⟨2346284125196236622635849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3128378833594982163514465 2346284125196236622635849)
                    ·
                      refine ⟨1759713093897177466976887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346284125196236622635849 1759713093897177466976887)
                      ·
                        rfl

theorem cell23_3427029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3427029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427029 prefixEnd_3427029 := by exact prefixLift 3427029
  have htrace : WordTrace (prefixWord ++ tailWord_3427029) baseStart_3427029 baseEnd_3427029 := by
    simpa [prefixWord, tailWord_3427029, baseEnd_3427029] using wordTrace_append hprefix tailTrace_3427029
  have hstable : (prefixWord ++ tailWord_3427029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427029).length < 2 ^ (prefixWord ++ tailWord_3427029).sum := by decide
  have hdescent : baseEnd_3427029 < baseStart_3427029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427068 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3427068 : Nat := 118140960795 + 3427068 * 2 ^ 59
def prefixEnd_3427068 : Nat := 4983230072969 + 3 ^ 40 * 3427068 * 2
def baseEnd_3427068 : Nat := 1759733119642702814389207

theorem tailTrace_3427068 : CollatzResearch.WordTrace tailWord_3427068 prefixEnd_3427068 1759733119642702814389207 := by
  unfold tailWord_3427068
  simp only [CollatzResearch.WordTrace]
  refine ⟨62497719374162703730832929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83330292498883604974443905 62497719374162703730832929)
  ·
    refine ⟨46873289530622027798124697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62497719374162703730832929 46873289530622027798124697)
    ·
      refine ⟨35154967147966520848593523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46873289530622027798124697 35154967147966520848593523)
      ·
        refine ⟨52732450721949781272890285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35154967147966520848593523 52732450721949781272890285)
        ·
          refine ⟨19774669020731167977333857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52732450721949781272890285 19774669020731167977333857)
          ·
            refine ⟨14831001765548375983000393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19774669020731167977333857 14831001765548375983000393)
            ·
              refine ⟨11123251324161281987250295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14831001765548375983000393 11123251324161281987250295)
              ·
                refine ⟨16684876986241922980875443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123251324161281987250295 16684876986241922980875443)
                ·
                  refine ⟨25027315479362884471313165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16684876986241922980875443 25027315479362884471313165)
                  ·
                    refine ⟨9385243304761081676742437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25027315479362884471313165 9385243304761081676742437)
                    ·
                      refine ⟨1759733119642702814389207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9385243304761081676742437 1759733119642702814389207)
                      ·
                        rfl

theorem cell23_3427068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3427068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427068 prefixEnd_3427068 := by exact prefixLift 3427068
  have htrace : WordTrace (prefixWord ++ tailWord_3427068) baseStart_3427068 baseEnd_3427068 := by
    simpa [prefixWord, tailWord_3427068, baseEnd_3427068] using wordTrace_append hprefix tailTrace_3427068
  have hstable : (prefixWord ++ tailWord_3427068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427068).length < 2 ^ (prefixWord ++ tailWord_3427068).sum := by decide
  have hdescent : baseEnd_3427068 < baseStart_3427068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427071 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_3427071 : Nat := 118140960795 + 3427071 * 2 ^ 59
def prefixEnd_3427071 : Nat := 4983230072969 + 3 ^ 40 * 3427071 * 2
def baseEnd_3427071 : Nat := 1759734660084666302651693

theorem tailTrace_3427071 : CollatzResearch.WordTrace tailWord_3427071 prefixEnd_3427071 1759734660084666302651693 := by
  unfold tailWord_3427071
  simp only [CollatzResearch.WordTrace]
  refine ⟨124995548167314538974025067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83330365444876359316016711 124995548167314538974025067)
  ·
    refine ⟨187493322250971808461037601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124995548167314538974025067 187493322250971808461037601)
    ·
      refine ⟨140619991688228856345778201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187493322250971808461037601 140619991688228856345778201)
      ·
        refine ⟨105464993766171642259333651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140619991688228856345778201 105464993766171642259333651)
        ·
          refine ⟨158197490649257463389000477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105464993766171642259333651 158197490649257463389000477)
          ·
            refine ⟨59324058993471548770875179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158197490649257463389000477 59324058993471548770875179)
            ·
              refine ⟨88986088490207323156312769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59324058993471548770875179 88986088490207323156312769)
              ·
                refine ⟨66739566367655492367234577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88986088490207323156312769 66739566367655492367234577)
                ·
                  refine ⟨50054674775741619275425933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66739566367655492367234577 50054674775741619275425933)
                  ·
                    refine ⟨18770503040903107228284725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50054674775741619275425933 18770503040903107228284725)
                    ·
                      refine ⟨1759734660084666302651693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18770503040903107228284725 1759734660084666302651693)
                      ·
                        rfl

theorem cell23_3427071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_3427071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427071 prefixEnd_3427071 := by exact prefixLift 3427071
  have htrace : WordTrace (prefixWord ++ tailWord_3427071) baseStart_3427071 baseEnd_3427071 := by
    simpa [prefixWord, tailWord_3427071, baseEnd_3427071] using wordTrace_append hprefix tailTrace_3427071
  have hstable : (prefixWord ++ tailWord_3427071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427071).length < 2 ^ (prefixWord ++ tailWord_3427071).sum := by decide
  have hdescent : baseEnd_3427071 < baseStart_3427071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427081 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_3427081 : Nat := 118140960795 + 3427081 * 2 ^ 59
def prefixEnd_3427081 : Nat := 4983230072969 + 3 ^ 40 * 3427081 * 2
def baseEnd_3427081 : Nat := 1759739794891211263526647

theorem tailTrace_3427081 : CollatzResearch.WordTrace tailWord_3427081 prefixEnd_3427081 1759739794891211263526647 := by
  unfold tailWord_3427081
  simp only [CollatzResearch.WordTrace]
  refine ⟨124995912897278310681889097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83330608598185540454592731 124995912897278310681889097)
  ·
    refine ⟨93746934672958733011416823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124995912897278310681889097 93746934672958733011416823)
    ·
      refine ⟨140620402009438099517125235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93746934672958733011416823 140620402009438099517125235)
      ·
        refine ⟨210930603014157149275687853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140620402009438099517125235 210930603014157149275687853)
        ·
          refine ⟨79098976130308930978382945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210930603014157149275687853 79098976130308930978382945)
          ·
            refine ⟨59324232097731698233787209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79098976130308930978382945 59324232097731698233787209)
            ·
              refine ⟨44493174073298773675340407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59324232097731698233787209 44493174073298773675340407)
              ·
                refine ⟨66739761109948160513010611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44493174073298773675340407 66739761109948160513010611)
                ·
                  refine ⟨100109641664922240769515917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66739761109948160513010611 100109641664922240769515917)
                  ·
                    refine ⟨37541115624345840288568469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100109641664922240769515917 37541115624345840288568469)
                    ·
                      refine ⟨1759739794891211263526647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37541115624345840288568469 1759739794891211263526647)
                      ·
                        rfl

theorem cell23_3427081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_3427081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427081 prefixEnd_3427081 := by exact prefixLift 3427081
  have htrace : WordTrace (prefixWord ++ tailWord_3427081) baseStart_3427081 baseEnd_3427081 := by
    simpa [prefixWord, tailWord_3427081, baseEnd_3427081] using wordTrace_append hprefix tailTrace_3427081
  have hstable : (prefixWord ++ tailWord_3427081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427081).length < 2 ^ (prefixWord ++ tailWord_3427081).sum := by decide
  have hdescent : baseEnd_3427081 < baseStart_3427081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427091 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 8]
def baseStart_3427091 : Nat := 118140960795 + 3427091 * 2 ^ 59
def prefixEnd_3427091 : Nat := 4983230072969 + 3 ^ 40 * 3427091 * 2
def baseEnd_3427091 : Nat := 195527214410861802711289

theorem tailTrace_3427091 : CollatzResearch.WordTrace tailWord_3427091 prefixEnd_3427091 195527214410861802711289 := by
  unfold tailWord_3427091
  simp only [CollatzResearch.WordTrace]
  refine ⟨124996277627242082389753127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83330851751494721593168751 124996277627242082389753127)
  ·
    refine ⟨187494416440863123584629691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124996277627242082389753127 187494416440863123584629691)
    ·
      refine ⟨281241624661294685376944537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187494416440863123584629691 281241624661294685376944537)
      ·
        refine ⟨210931218495971014032708403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281241624661294685376944537 210931218495971014032708403)
        ·
          refine ⟨316396827743956521049062605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210931218495971014032708403 316396827743956521049062605)
          ·
            refine ⟨118648810403983695393398477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316396827743956521049062605 118648810403983695393398477)
            ·
              refine ⟨44493303901493885772524429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118648810403983695393398477 44493303901493885772524429)
              ·
                refine ⟨16684988963060207164696661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44493303901493885772524429 16684988963060207164696661)
                ·
                  refine ⟨195527214410861802711289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16684988963060207164696661 195527214410861802711289)
                  ·
                    rfl

theorem cell23_3427091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 8].length) (baseStart_3427091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427091 prefixEnd_3427091 := by exact prefixLift 3427091
  have htrace : WordTrace (prefixWord ++ tailWord_3427091) baseStart_3427091 baseEnd_3427091 := by
    simpa [prefixWord, tailWord_3427091, baseEnd_3427091] using wordTrace_append hprefix tailTrace_3427091
  have hstable : (prefixWord ++ tailWord_3427091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427091).length < 2 ^ (prefixWord ++ tailWord_3427091).sum := by decide
  have hdescent : baseEnd_3427091 < baseStart_3427091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427175 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3427175 : Nat := 118140960795 + 3427175 * 2 ^ 59
def prefixEnd_3427175 : Nat := 4983230072969 + 3 ^ 40 * 3427175 * 2
def baseEnd_3427175 : Nat := 1759788062072733895751215

theorem tailTrace_3427175 : CollatzResearch.WordTrace tailWord_3427175 prefixEnd_3427175 1759788062072733895751215 := by
  unfold tailWord_3427175
  simp only [CollatzResearch.WordTrace]
  refine ⟨124999341358937764735810979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83332894239291843157207319 124999341358937764735810979)
  ·
    refine ⟨187499012038406647103716469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124999341358937764735810979 187499012038406647103716469)
    ·
      refine ⟨17578032378600623165973419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187499012038406647103716469 17578032378600623165973419)
      ·
        refine ⟨26367048567900934748960129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17578032378600623165973419 26367048567900934748960129)
        ·
          refine ⟨19775286425925701061720097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26367048567900934748960129 19775286425925701061720097)
          ·
            refine ⟨14831464819444275796290073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19775286425925701061720097 14831464819444275796290073)
            ·
              refine ⟨11123598614583206847217555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14831464819444275796290073 11123598614583206847217555)
              ·
                refine ⟨16685397921874810270826333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123598614583206847217555 16685397921874810270826333)
                ·
                  refine ⟨6257024220703053851559875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16685397921874810270826333 6257024220703053851559875)
                  ·
                    refine ⟨9385536331054580777339813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257024220703053851559875 9385536331054580777339813)
                    ·
                      refine ⟨1759788062072733895751215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9385536331054580777339813 1759788062072733895751215)
                      ·
                        rfl

theorem cell23_3427175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3427175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427175 prefixEnd_3427175 := by exact prefixLift 3427175
  have htrace : WordTrace (prefixWord ++ tailWord_3427175) baseStart_3427175 baseEnd_3427175 := by
    simpa [prefixWord, tailWord_3427175, baseEnd_3427175] using wordTrace_append hprefix tailTrace_3427175
  have hstable : (prefixWord ++ tailWord_3427175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427175).length < 2 ^ (prefixWord ++ tailWord_3427175).sum := by decide
  have hdescent : baseEnd_3427175 < baseStart_3427175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427189 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3427189 : Nat := 118140960795 + 3427189 * 2 ^ 59
def prefixEnd_3427189 : Nat := 4983230072969 + 3 ^ 40 * 3427189 * 2
def baseEnd_3427189 : Nat := 586598416933965613658717

theorem tailTrace_3427189 : CollatzResearch.WordTrace tailWord_3427189 prefixEnd_3427189 586598416933965613658717 := by
  unfold tailWord_3427189
  simp only [CollatzResearch.WordTrace]
  refine ⟨124999851980887045126820621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83333234653924696751213747 124999851980887045126820621)
  ·
    refine ⟨46874944492832641922557733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124999851980887045126820621 46874944492832641922557733)
    ·
      refine ⟨8789052092406120360479575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46874944492832641922557733 8789052092406120360479575)
      ·
        refine ⟨13183578138609180540719363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789052092406120360479575 13183578138609180540719363)
        ·
          refine ⟨19775367207913770811079045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13183578138609180540719363 19775367207913770811079045)
          ·
            refine ⟨3707881351483832027077321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19775367207913770811079045 3707881351483832027077321)
            ·
              refine ⟨2780911013612874020307991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707881351483832027077321 2780911013612874020307991)
              ·
                refine ⟨4171366520419311030461987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780911013612874020307991 4171366520419311030461987)
                ·
                  refine ⟨6257049780628966545692981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171366520419311030461987 6257049780628966545692981)
                  ·
                    refine ⟨586598416933965613658717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6257049780628966545692981 586598416933965613658717)
                    ·
                      rfl

theorem cell23_3427189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3427189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427189 prefixEnd_3427189 := by exact prefixLift 3427189
  have htrace : WordTrace (prefixWord ++ tailWord_3427189) baseStart_3427189 baseEnd_3427189 := by
    simpa [prefixWord, tailWord_3427189, baseEnd_3427189] using wordTrace_append hprefix tailTrace_3427189
  have hstable : (prefixWord ++ tailWord_3427189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427189).length < 2 ^ (prefixWord ++ tailWord_3427189).sum := by decide
  have hdescent : baseEnd_3427189 < baseStart_3427189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427209 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 3, 2, 2]
def baseStart_3427209 : Nat := 118140960795 + 3427209 * 2 ^ 59
def prefixEnd_3427209 : Nat := 4983230072969 + 3 ^ 40 * 3427209 * 2
def baseEnd_3427209 : Nat := 1759805520414986762726059

theorem tailTrace_3427209 : CollatzResearch.WordTrace tailWord_3427209 prefixEnd_3427209 1759805520414986762726059 := by
  unfold tailWord_3427209
  simp only [CollatzResearch.WordTrace]
  refine ⟨125000581440814588542548681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83333720960543059028365787 125000581440814588542548681)
  ·
    refine ⟨93750436080610941406911511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125000581440814588542548681 93750436080610941406911511)
    ·
      refine ⟨140625654120916412110367267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93750436080610941406911511 140625654120916412110367267)
      ·
        refine ⟨210938481181374618165550901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140625654120916412110367267 210938481181374618165550901)
        ·
          refine ⟨19775482610753870453020397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210938481181374618165550901 19775482610753870453020397)
          ·
            refine ⟨7415805979032701419882649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19775482610753870453020397 7415805979032701419882649)
            ·
              refine ⟨5561854484274526064911987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415805979032701419882649 5561854484274526064911987)
              ·
                refine ⟨8342781726411789097367981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5561854484274526064911987 8342781726411789097367981)
                ·
                  refine ⟨3128543147404420911512993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8342781726411789097367981 3128543147404420911512993)
                  ·
                    refine ⟨2346407360553315683634745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3128543147404420911512993 2346407360553315683634745)
                    ·
                      refine ⟨1759805520414986762726059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346407360553315683634745 1759805520414986762726059)
                      ·
                        rfl

theorem cell23_3427209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 2, 2].length) (baseStart_3427209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427209 prefixEnd_3427209 := by exact prefixLift 3427209
  have htrace : WordTrace (prefixWord ++ tailWord_3427209) baseStart_3427209 baseEnd_3427209 := by
    simpa [prefixWord, tailWord_3427209, baseEnd_3427209] using wordTrace_append hprefix tailTrace_3427209
  have hstable : (prefixWord ++ tailWord_3427209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427209).length < 2 ^ (prefixWord ++ tailWord_3427209).sum := by decide
  have hdescent : baseEnd_3427209 < baseStart_3427209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427270 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3427270 : Nat := 118140960795 + 3427270 * 2 ^ 59
def prefixEnd_3427270 : Nat := 4983230072969 + 3 ^ 40 * 3427270 * 2
def baseEnd_3427270 : Nat := 586612280911637008021093

theorem tailTrace_3427270 : CollatzResearch.WordTrace tailWord_3427270 prefixEnd_3427270 586612280911637008021093 := by
  unfold tailWord_3427270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3906337696674799873766227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83335204195729063973679509 3906337696674799873766227)
  ·
    refine ⟨5859506545012199810649341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3906337696674799873766227 5859506545012199810649341)
    ·
      refine ⟨2197314954379574928993503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5859506545012199810649341 2197314954379574928993503)
      ·
        refine ⟨3295972431569362393490255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197314954379574928993503 3295972431569362393490255)
        ·
          refine ⟨4943958647354043590235383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295972431569362393490255 4943958647354043590235383)
          ·
            refine ⟨7415937971031065385353075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943958647354043590235383 7415937971031065385353075)
            ·
              refine ⟨11123906956546598078029613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415937971031065385353075 11123906956546598078029613)
              ·
                refine ⟨4171465108704974279261105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11123906956546598078029613 4171465108704974279261105)
                ·
                  refine ⟨3128598831528730709445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171465108704974279261105 3128598831528730709445829)
                  ·
                    refine ⟨586612280911637008021093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128598831528730709445829 586612280911637008021093)
                    ·
                      rfl

theorem cell23_3427270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3427270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427270 prefixEnd_3427270 := by exact prefixLift 3427270
  have htrace : WordTrace (prefixWord ++ tailWord_3427270) baseStart_3427270 baseEnd_3427270 := by
    simpa [prefixWord, tailWord_3427270, baseEnd_3427270] using wordTrace_append hprefix tailTrace_3427270
  have hstable : (prefixWord ++ tailWord_3427270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427270).length < 2 ^ (prefixWord ++ tailWord_3427270).sum := by decide
  have hdescent : baseEnd_3427270 < baseStart_3427270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427286 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3427286 : Nat := 118140960795 + 3427286 * 2 ^ 59
def prefixEnd_3427286 : Nat := 4983230072969 + 3 ^ 40 * 3427286 * 2
def baseEnd_3427286 : Nat := 1759845058425382961463205

theorem tailTrace_3427286 : CollatzResearch.WordTrace tailWord_3427286 prefixEnd_3427286 1759845058425382961463205 := by
  unfold tailWord_3427286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7812711866345976918318857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83335593241023753795401141 7812711866345976918318857)
  ·
    refine ⟨5859533899759482688739143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7812711866345976918318857 5859533899759482688739143)
    ·
      refine ⟨8789300849639224033108715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859533899759482688739143 8789300849639224033108715)
      ·
        refine ⟨13183951274458836049663073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8789300849639224033108715 13183951274458836049663073)
        ·
          refine ⟨9887963455844127037247305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183951274458836049663073 9887963455844127037247305)
          ·
            refine ⟨7415972591883095277935479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887963455844127037247305 7415972591883095277935479)
            ·
              refine ⟨11123958887824642916903219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415972591883095277935479 11123958887824642916903219)
              ·
                refine ⟨16685938331736964375354829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123958887824642916903219 16685938331736964375354829)
                ·
                  refine ⟨6257226874401361640758061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16685938331736964375354829 6257226874401361640758061)
                  ·
                    refine ⟨2346460077900510615284273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6257226874401361640758061 2346460077900510615284273)
                    ·
                      refine ⟨1759845058425382961463205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346460077900510615284273 1759845058425382961463205)
                      ·
                        rfl

theorem cell23_3427286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3427286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427286 prefixEnd_3427286 := by exact prefixLift 3427286
  have htrace : WordTrace (prefixWord ++ tailWord_3427286) baseStart_3427286 baseEnd_3427286 := by
    simpa [prefixWord, tailWord_3427286, baseEnd_3427286] using wordTrace_append hprefix tailTrace_3427286
  have hstable : (prefixWord ++ tailWord_3427286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427286).length < 2 ^ (prefixWord ++ tailWord_3427286).sum := by decide
  have hdescent : baseEnd_3427286 < baseStart_3427286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427335 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3427335 : Nat := 118140960795 + 3427335 * 2 ^ 59
def prefixEnd_3427335 : Nat := 4983230072969 + 3 ^ 40 * 3427335 * 2
def baseEnd_3427335 : Nat := 586623406325817756583493

theorem tailTrace_3427335 : CollatzResearch.WordTrace tailWord_3427335 prefixEnd_3427335 586623406325817756583493 := by
  unfold tailWord_3427335
  simp only [CollatzResearch.WordTrace]
  refine ⟨125005177038358112061635459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83336784692238741374423639 125005177038358112061635459)
  ·
    refine ⟨187507765557537168092453189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125005177038358112061635459 187507765557537168092453189)
    ·
      refine ⟨35157706042038219017334973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187507765557537168092453189 35157706042038219017334973)
      ·
        refine ⟨13184139765764332131500615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35157706042038219017334973 13184139765764332131500615)
        ·
          refine ⟨19776209648646498197250923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184139765764332131500615 19776209648646498197250923)
          ·
            refine ⟨29664314472969747295876385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19776209648646498197250923 29664314472969747295876385)
            ·
              refine ⟨22248235854727310471907289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29664314472969747295876385 22248235854727310471907289)
              ·
                refine ⟨16686176891045482853930467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22248235854727310471907289 16686176891045482853930467)
                ·
                  refine ⟨25029265336568224280895701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16686176891045482853930467 25029265336568224280895701)
                  ·
                    refine ⟨586623406325817756583493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25029265336568224280895701 586623406325817756583493)
                    ·
                      rfl

theorem cell23_3427335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3427335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427335 prefixEnd_3427335 := by exact prefixLift 3427335
  have htrace : WordTrace (prefixWord ++ tailWord_3427335) baseStart_3427335 baseEnd_3427335 := by
    simpa [prefixWord, tailWord_3427335, baseEnd_3427335] using wordTrace_append hprefix tailTrace_3427335
  have hstable : (prefixWord ++ tailWord_3427335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427335).length < 2 ^ (prefixWord ++ tailWord_3427335).sum := by decide
  have hdescent : baseEnd_3427335 < baseStart_3427335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427352 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_3427352 : Nat := 118140960795 + 3427352 * 2 ^ 59
def prefixEnd_3427352 : Nat := 4983230072969 + 3 ^ 40 * 3427352 * 2
def baseEnd_3427352 : Nat := 586626316049526567745967

theorem tailTrace_3427352 : CollatzResearch.WordTrace tailWord_3427352 prefixEnd_3427352 586626316049526567745967 := by
  unfold tailWord_3427352
  simp only [CollatzResearch.WordTrace]
  refine ⟨62502898539648261982502155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83337198052864349310002873 62502898539648261982502155)
  ·
    refine ⟨93754347809472392973753233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62502898539648261982502155 93754347809472392973753233)
    ·
      refine ⟨70315760857104294730314925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93754347809472392973753233 70315760857104294730314925)
      ·
        refine ⟨26368410321414110523868097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70315760857104294730314925 26368410321414110523868097)
        ·
          refine ⟨19776307741060582892901073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26368410321414110523868097 19776307741060582892901073)
          ·
            refine ⟨14832230805795437169675805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19776307741060582892901073 14832230805795437169675805)
            ·
              refine ⟨5562086552173288938628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14832230805795437169675805 5562086552173288938628427)
              ·
                refine ⟨8343129828259933407942641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562086552173288938628427 8343129828259933407942641)
                ·
                  refine ⟨6257347371194950055956981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343129828259933407942641 6257347371194950055956981)
                  ·
                    refine ⟨586626316049526567745967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6257347371194950055956981 586626316049526567745967)
                    ·
                      rfl

theorem cell23_3427352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_3427352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427352 prefixEnd_3427352 := by exact prefixLift 3427352
  have htrace : WordTrace (prefixWord ++ tailWord_3427352) baseStart_3427352 baseEnd_3427352 := by
    simpa [prefixWord, tailWord_3427352, baseEnd_3427352] using wordTrace_append hprefix tailTrace_3427352
  have hstable : (prefixWord ++ tailWord_3427352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427352).length < 2 ^ (prefixWord ++ tailWord_3427352).sum := by decide
  have hdescent : baseEnd_3427352 < baseStart_3427352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427372 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_3427372 : Nat := 118140960795 + 3427372 * 2 ^ 59
def prefixEnd_3427372 : Nat := 4983230072969 + 3 ^ 40 * 3427372 * 2
def baseEnd_3427372 : Nat := 1759889217761669624987809

theorem tailTrace_3427372 : CollatzResearch.WordTrace tailWord_3427372 prefixEnd_3427372 1759889217761669624987809 := by
  unfold tailWord_3427372
  simp only [CollatzResearch.WordTrace]
  refine ⟨62503263269612033690366185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83337684359482711587154913 62503263269612033690366185)
  ·
    refine ⟨46877447452209025267774639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62503263269612033690366185 46877447452209025267774639)
    ·
      refine ⟨70316171178313537901661959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46877447452209025267774639 70316171178313537901661959)
      ·
        refine ⟨105474256767470306852492939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70316171178313537901661959 105474256767470306852492939)
        ·
          refine ⟨158211385151205460278739409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105474256767470306852492939 158211385151205460278739409)
          ·
            refine ⟨118658538863404095209054557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158211385151205460278739409 118658538863404095209054557)
            ·
              refine ⟨44496952073776535703395459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118658538863404095209054557 44496952073776535703395459)
              ·
                refine ⟨66745428110664803555093189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44496952073776535703395459 66745428110664803555093189)
                ·
                  refine ⟨12514767770749650666579973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66745428110664803555093189 12514767770749650666579973)
                  ·
                    refine ⟨2346518957015559499983745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12514767770749650666579973 2346518957015559499983745)
                    ·
                      refine ⟨1759889217761669624987809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346518957015559499983745 1759889217761669624987809)
                      ·
                        rfl

theorem cell23_3427372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_3427372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427372 prefixEnd_3427372 := by exact prefixLift 3427372
  have htrace : WordTrace (prefixWord ++ tailWord_3427372) baseStart_3427372 baseEnd_3427372 := by
    simpa [prefixWord, tailWord_3427372, baseEnd_3427372] using wordTrace_append hprefix tailTrace_3427372
  have hstable : (prefixWord ++ tailWord_3427372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427372).length < 2 ^ (prefixWord ++ tailWord_3427372).sum := by decide
  have hdescent : baseEnd_3427372 < baseStart_3427372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427389 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3427389 : Nat := 118140960795 + 3427389 * 2 ^ 59
def prefixEnd_3427389 : Nat := 4983230072969 + 3 ^ 40 * 3427389 * 2
def baseEnd_3427389 : Nat := 1759897946932796058475231

theorem tailTrace_3427389 : CollatzResearch.WordTrace tailWord_3427389 prefixEnd_3427389 1759897946932796058475231 := by
  unfold tailWord_3427389
  simp only [CollatzResearch.WordTrace]
  refine ⟨125007146580162479284101221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83338097720108319522734147 125007146580162479284101221)
  ·
    refine ⟨23438839983780464865768979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125007146580162479284101221 23438839983780464865768979)
    ·
      refine ⟨35158259975670697298653469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438839983780464865768979 35158259975670697298653469)
      ·
        refine ⟨13184347490876511486995051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35158259975670697298653469 13184347490876511486995051)
        ·
          refine ⟨19776521236314767230492577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184347490876511486995051 19776521236314767230492577)
          ·
            refine ⟨14832390927236075422869433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19776521236314767230492577 14832390927236075422869433)
            ·
              refine ⟨11124293195427056567152075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14832390927236075422869433 11124293195427056567152075)
              ·
                refine ⟨16686439793140584850728113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11124293195427056567152075 16686439793140584850728113)
                ·
                  refine ⟨12514829844855438638046085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16686439793140584850728113 12514829844855438638046085)
                  ·
                    refine ⟨2346530595910394744633641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12514829844855438638046085 2346530595910394744633641)
                    ·
                      refine ⟨1759897946932796058475231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346530595910394744633641 1759897946932796058475231)
                      ·
                        rfl

theorem cell23_3427389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3427389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427389 prefixEnd_3427389 := by exact prefixLift 3427389
  have htrace : WordTrace (prefixWord ++ tailWord_3427389) baseStart_3427389 baseEnd_3427389 := by
    simpa [prefixWord, tailWord_3427389, baseEnd_3427389] using wordTrace_append hprefix tailTrace_3427389
  have hstable : (prefixWord ++ tailWord_3427389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427389).length < 2 ^ (prefixWord ++ tailWord_3427389).sum := by decide
  have hdescent : baseEnd_3427389 < baseStart_3427389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427426 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3427426 : Nat := 118140960795 + 3427426 * 2 ^ 59
def prefixEnd_3427426 : Nat := 4983230072969 + 3 ^ 40 * 3427426 * 2
def baseEnd_3427426 : Nat := 1759916945717012413712561

theorem tailTrace_3427426 : CollatzResearch.WordTrace tailWord_3427426 prefixEnd_3427426 1759916945717012413712561 := by
  unfold tailWord_3427426
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252124020257108650799533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83338997387352289735465421 31252124020257108650799533)
  ·
    refine ⟨11719546507596415744049825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31252124020257108650799533 11719546507596415744049825)
    ·
      refine ⟨8789659880697311808037369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11719546507596415744049825 8789659880697311808037369)
      ·
        refine ⟨6592244910522983856028027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8789659880697311808037369 6592244910522983856028027)
        ·
          refine ⟨9888367365784475784042041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592244910522983856028027 9888367365784475784042041)
          ·
            refine ⟨7416275524338356838031531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9888367365784475784042041 7416275524338356838031531)
            ·
              refine ⟨11124413286507535257047297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416275524338356838031531 11124413286507535257047297)
              ·
                refine ⟨8343309964880651442785473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11124413286507535257047297 8343309964880651442785473)
                ·
                  refine ⟨6257482473660488582089105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343309964880651442785473 6257482473660488582089105)
                  ·
                    refine ⟨4693111855245366436566829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6257482473660488582089105 4693111855245366436566829)
                    ·
                      refine ⟨1759916945717012413712561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693111855245366436566829 1759916945717012413712561)
                      ·
                        rfl

theorem cell23_3427426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3427426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427426 prefixEnd_3427426 := by exact prefixLift 3427426
  have htrace : WordTrace (prefixWord ++ tailWord_3427426) baseStart_3427426 baseEnd_3427426 := by
    simpa [prefixWord, tailWord_3427426, baseEnd_3427426] using wordTrace_append hprefix tailTrace_3427426
  have hstable : (prefixWord ++ tailWord_3427426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427426).length < 2 ^ (prefixWord ++ tailWord_3427426).sum := by decide
  have hdescent : baseEnd_3427426 < baseStart_3427426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427442 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_3427442 : Nat := 118140960795 + 3427442 * 2 ^ 59
def prefixEnd_3427442 : Nat := 4983230072969 + 3 ^ 40 * 3427442 * 2
def baseEnd_3427442 : Nat := 586641720469161450370829

theorem tailTrace_3427442 : CollatzResearch.WordTrace tailWord_3427442 prefixEnd_3427442 586641720469161450370829 := by
  unfold tailWord_3427442
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252269912242617333945145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83339386432646979557187053 31252269912242617333945145)
  ·
    refine ⟨23439202434181963000458859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31252269912242617333945145 23439202434181963000458859)
    ·
      refine ⟨35158803651272944500688289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23439202434181963000458859 35158803651272944500688289)
      ·
        refine ⟨26369102738454708375516217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35158803651272944500688289 26369102738454708375516217)
        ·
          refine ⟨19776827053841031281637163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26369102738454708375516217 19776827053841031281637163)
          ·
            refine ⟨29665240580761546922455745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19776827053841031281637163 29665240580761546922455745)
            ·
              refine ⟨22248930435571160191841809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29665240580761546922455745 22248930435571160191841809)
              ·
                refine ⟨16686697826678370143881357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22248930435571160191841809 16686697826678370143881357)
                ·
                  refine ⟨6257511685004388803955509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16686697826678370143881357 6257511685004388803955509)
                  ·
                    refine ⟨586641720469161450370829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6257511685004388803955509 586641720469161450370829)
                    ·
                      rfl

theorem cell23_3427442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_3427442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427442 prefixEnd_3427442 := by exact prefixLift 3427442
  have htrace : WordTrace (prefixWord ++ tailWord_3427442) baseStart_3427442 baseEnd_3427442 := by
    simpa [prefixWord, tailWord_3427442, baseEnd_3427442] using wordTrace_append hprefix tailTrace_3427442
  have hstable : (prefixWord ++ tailWord_3427442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427442).length < 2 ^ (prefixWord ++ tailWord_3427442).sum := by decide
  have hdescent : baseEnd_3427442 < baseStart_3427442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427455 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 7, 6]
def baseStart_3427455 : Nat := 118140960795 + 3427455 * 2 ^ 59
def prefixEnd_3427455 : Nat := 4983230072969 + 3 ^ 40 * 3427455 * 2
def baseEnd_3427455 : Nat := 586643945551997600083309

theorem tailTrace_3427455 : CollatzResearch.WordTrace tailWord_3427455 prefixEnd_3427455 586643945551997600083309 := by
  unfold tailWord_3427455
  simp only [CollatzResearch.WordTrace]
  refine ⟨125009553797923372556003819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83339702531948915037335879 125009553797923372556003819)
  ·
    refine ⟨187514330696885058834005729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125009553797923372556003819 187514330696885058834005729)
    ·
      refine ⟨140635748022663794125504297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187514330696885058834005729 140635748022663794125504297)
      ·
        refine ⟨105476811016997845594128223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140635748022663794125504297 105476811016997845594128223)
        ·
          refine ⟨158215216525496768391192335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105476811016997845594128223 158215216525496768391192335)
          ·
            refine ⟨237322824788245152586788503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158215216525496768391192335 237322824788245152586788503)
            ·
              refine ⟨355984237182367728880182755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237322824788245152586788503 355984237182367728880182755)
              ·
                refine ⟨533976355773551593320274133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355984237182367728880182755 533976355773551593320274133)
                ·
                  refine ⟨12515070838442615468443925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 533976355773551593320274133 12515070838442615468443925)
                  ·
                    refine ⟨586643945551997600083309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12515070838442615468443925 586643945551997600083309)
                    ·
                      rfl

theorem cell23_3427455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_3427455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427455 prefixEnd_3427455 := by exact prefixLift 3427455
  have htrace : WordTrace (prefixWord ++ tailWord_3427455) baseStart_3427455 baseEnd_3427455 := by
    simpa [prefixWord, tailWord_3427455, baseEnd_3427455] using wordTrace_append hprefix tailTrace_3427455
  have hstable : (prefixWord ++ tailWord_3427455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427455).length < 2 ^ (prefixWord ++ tailWord_3427455).sum := by decide
  have hdescent : baseEnd_3427455 < baseStart_3427455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427466 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2]
def baseStart_3427466 : Nat := 118140960795 + 3427466 * 2 ^ 59
def prefixEnd_3427466 : Nat := 4983230072969 + 3 ^ 40 * 3427466 * 2
def baseEnd_3427466 : Nat := 1759937484943192257212377

theorem tailTrace_3427466 : CollatzResearch.WordTrace tailWord_3427466 prefixEnd_3427466 1759937484943192257212377 := by
  unfold tailWord_3427466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252488750220880358663563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83339970000589014289769501 31252488750220880358663563)
  ·
    refine ⟨46878733125331320537995345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31252488750220880358663563 46878733125331320537995345)
    ·
      refine ⟨35159049843998490403496509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46878733125331320537995345 35159049843998490403496509)
      ·
        refine ⟨13184643691499433901311191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35159049843998490403496509 13184643691499433901311191)
        ·
          refine ⟨19776965537249150851966787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13184643691499433901311191 19776965537249150851966787)
          ·
            refine ⟨29665448305873726277950181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19776965537249150851966787 29665448305873726277950181)
            ·
              refine ⟨5562271557351323677115659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29665448305873726277950181 5562271557351323677115659)
              ·
                refine ⟨8343407336026985515673489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562271557351323677115659 8343407336026985515673489)
                ·
                  refine ⟨6257555502020239136755117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343407336026985515673489 6257555502020239136755117)
                  ·
                    refine ⟨2346583313257589676283169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6257555502020239136755117 2346583313257589676283169)
                    ·
                      refine ⟨1759937484943192257212377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346583313257589676283169 1759937484943192257212377)
                      ·
                        rfl

theorem cell23_3427466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_3427466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427466 prefixEnd_3427466 := by exact prefixLift 3427466
  have htrace : WordTrace (prefixWord ++ tailWord_3427466) baseStart_3427466 baseEnd_3427466 := by
    simpa [prefixWord, tailWord_3427466, baseEnd_3427466] using wordTrace_append hprefix tailTrace_3427466
  have hstable : (prefixWord ++ tailWord_3427466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427466).length < 2 ^ (prefixWord ++ tailWord_3427466).sum := by decide
  have hdescent : baseEnd_3427466 < baseStart_3427466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427472 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_3427472 : Nat := 118140960795 + 3427472 * 2 ^ 59
def prefixEnd_3427472 : Nat := 4983230072969 + 3 ^ 40 * 3427472 * 2
def baseEnd_3427472 : Nat := 586646855275706411245783

theorem tailTrace_3427472 : CollatzResearch.WordTrace tailWord_3427472 prefixEnd_3427472 586646855275706411245783 := by
  unfold tailWord_3427472
  simp only [CollatzResearch.WordTrace]
  refine ⟨62505086919430892229686335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83340115892574522972915113 62505086919430892229686335)
  ·
    refine ⟨93757630379146338344529503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62505086919430892229686335 93757630379146338344529503)
    ·
      refine ⟨140636445568719507516794255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93757630379146338344529503 140636445568719507516794255)
      ·
        refine ⟨210954668353079261275191383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140636445568719507516794255 210954668353079261275191383)
        ·
          refine ⟨316432002529618891912787075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210954668353079261275191383 316432002529618891912787075)
          ·
            refine ⟨474648003794428337869180613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316432002529618891912787075 474648003794428337869180613)
            ·
              refine ⟨88996500711455313350471365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 474648003794428337869180613 88996500711455313350471365)
              ·
                refine ⟨16686843883397871253213381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88996500711455313350471365 16686843883397871253213381)
                ·
                  refine ⟨3128783228137100859977509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16686843883397871253213381 3128783228137100859977509)
                  ·
                    refine ⟨586646855275706411245783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128783228137100859977509 586646855275706411245783)
                    ·
                      rfl

theorem cell23_3427472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_3427472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427472 prefixEnd_3427472 := by exact prefixLift 3427472
  have htrace : WordTrace (prefixWord ++ tailWord_3427472) baseStart_3427472 baseEnd_3427472 := by
    simpa [prefixWord, tailWord_3427472, baseEnd_3427472] using wordTrace_append hprefix tailTrace_3427472
  have hstable : (prefixWord ++ tailWord_3427472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427472).length < 2 ^ (prefixWord ++ tailWord_3427472).sum := by decide
  have hdescent : baseEnd_3427472 < baseStart_3427472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427490 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_3427490 : Nat := 118140960795 + 3427490 * 2 ^ 59
def prefixEnd_3427490 : Nat := 4983230072969 + 3 ^ 40 * 3427490 * 2
def baseEnd_3427490 : Nat := 1759949808478900163312267

theorem tailTrace_3427490 : CollatzResearch.WordTrace tailWord_3427490 prefixEnd_3427490 1759949808478900163312267 := by
  unfold tailWord_3427490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252707588199143383381981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83340553568531049022351949 31252707588199143383381981)
  ·
    refine ⟨11719765345574678768768243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31252707588199143383381981 11719765345574678768768243)
    ·
      refine ⟨17579648018362018153152365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11719765345574678768768243 17579648018362018153152365)
      ·
        refine ⟨6592368006885756807432137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17579648018362018153152365 6592368006885756807432137)
        ·
          refine ⟨4944276005164317605574103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6592368006885756807432137 4944276005164317605574103)
          ·
            refine ⟨7416414007746476408361155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944276005164317605574103 7416414007746476408361155)
            ·
              refine ⟨11124621011619714612541733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416414007746476408361155 11124621011619714612541733)
              ·
                refine ⟨2085866439678696489851575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11124621011619714612541733 2085866439678696489851575)
                ·
                  refine ⟨3128799659518044734777363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085866439678696489851575 3128799659518044734777363)
                  ·
                    refine ⟨4693199489277067102166045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128799659518044734777363 4693199489277067102166045)
                    ·
                      refine ⟨1759949808478900163312267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693199489277067102166045 1759949808478900163312267)
                      ·
                        rfl

theorem cell23_3427490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_3427490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427490 prefixEnd_3427490 := by exact prefixLift 3427490
  have htrace : WordTrace (prefixWord ++ tailWord_3427490) baseStart_3427490 baseEnd_3427490 := by
    simpa [prefixWord, tailWord_3427490, baseEnd_3427490] using wordTrace_append hprefix tailTrace_3427490
  have hstable : (prefixWord ++ tailWord_3427490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427490).length < 2 ^ (prefixWord ++ tailWord_3427490).sum := by decide
  have hdescent : baseEnd_3427490 < baseStart_3427490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427530 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2]
def baseStart_3427530 : Nat := 118140960795 + 3427530 * 2 ^ 59
def prefixEnd_3427530 : Nat := 4983230072969 + 3 ^ 40 * 3427530 * 2
def baseEnd_3427530 : Nat := 1759970347705080006812083

theorem tailTrace_3427530 : CollatzResearch.WordTrace tailWord_3427530 prefixEnd_3427530 1759970347705080006812083 := by
  unfold tailWord_3427530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31253072318162915091246011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83341526181767773576656029 31253072318162915091246011)
  ·
    refine ⟨46879608477244372636869017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31253072318162915091246011 46879608477244372636869017)
    ·
      refine ⟨35159706357933279477651763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46879608477244372636869017 35159706357933279477651763)
      ·
        refine ⟨52739559536899919216477645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35159706357933279477651763 52739559536899919216477645)
        ·
          refine ⟨19777334826337469706179117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52739559536899919216477645 19777334826337469706179117)
          ·
            refine ⟨7416500559876551139817169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19777334826337469706179117 7416500559876551139817169)
            ·
              refine ⟨5562375419907413354862877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416500559876551139817169 5562375419907413354862877)
              ·
                refine ⟨2085890782465280008073579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5562375419907413354862877 2085890782465280008073579)
                ·
                  refine ⟨3128836173697920012110369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085890782465280008073579 3128836173697920012110369)
                  ·
                    refine ⟨2346627130273440009082777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3128836173697920012110369 2346627130273440009082777)
                    ·
                      refine ⟨1759970347705080006812083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346627130273440009082777 1759970347705080006812083)
                      ·
                        rfl

theorem cell23_3427530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_3427530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427530 prefixEnd_3427530 := by exact prefixLift 3427530
  have htrace : WordTrace (prefixWord ++ tailWord_3427530) baseStart_3427530 baseEnd_3427530 := by
    simpa [prefixWord, tailWord_3427530, baseEnd_3427530] using wordTrace_append hprefix tailTrace_3427530
  have hstable : (prefixWord ++ tailWord_3427530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427530).length < 2 ^ (prefixWord ++ tailWord_3427530).sum := by decide
  have hdescent : baseEnd_3427530 < baseStart_3427530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427540 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3427540 : Nat := 118140960795 + 3427540 * 2 ^ 59
def prefixEnd_3427540 : Nat := 4983230072969 + 3 ^ 40 * 3427540 * 2
def baseEnd_3427540 : Nat := 586658494170541655895679

theorem tailTrace_3427540 : CollatzResearch.WordTrace tailWord_3427540 prefixEnd_3427540 586658494170541655895679 := by
  unfold tailWord_3427540
  simp only [CollatzResearch.WordTrace]
  refine ⟨62506327001307716036424037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83341769335076954715232049 62506327001307716036424037)
  ·
    refine ⟨11719936312745196756829507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62506327001307716036424037 11719936312745196756829507)
    ·
      refine ⟨17579904469117795135244261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11719936312745196756829507 17579904469117795135244261)
      ·
        refine ⟨3296232087959586587858299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17579904469117795135244261 3296232087959586587858299)
        ·
          refine ⟨4944348131939379881787449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296232087959586587858299 4944348131939379881787449)
          ·
            refine ⟨3708261098954534911340587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944348131939379881787449 3708261098954534911340587)
            ·
              refine ⟨5562391648431802367010881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708261098954534911340587 5562391648431802367010881)
              ·
                refine ⟨4171793736323851775258161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562391648431802367010881 4171793736323851775258161)
                ·
                  refine ⟨3128845302242888831443621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171793736323851775258161 3128845302242888831443621)
                  ·
                    refine ⟨586658494170541655895679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128845302242888831443621 586658494170541655895679)
                    ·
                      rfl

theorem cell23_3427540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3427540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427540 prefixEnd_3427540 := by exact prefixLift 3427540
  have htrace : WordTrace (prefixWord ++ tailWord_3427540) baseStart_3427540 baseEnd_3427540 := by
    simpa [prefixWord, tailWord_3427540, baseEnd_3427540] using wordTrace_append hprefix tailTrace_3427540
  have hstable : (prefixWord ++ tailWord_3427540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427540).length < 2 ^ (prefixWord ++ tailWord_3427540).sum := by decide
  have hdescent : baseEnd_3427540 < baseStart_3427540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427563 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 2, 1, 3]
def baseStart_3427563 : Nat := 118140960795 + 3427563 * 2 ^ 59
def prefixEnd_3427563 : Nat := 4983230072969 + 3 ^ 40 * 3427563 * 2
def baseEnd_3427563 : Nat := 1759987292566678377699431

theorem tailTrace_3427563 : CollatzResearch.WordTrace tailWord_3427563 prefixEnd_3427563 1759987292566678377699431 := by
  unfold tailWord_3427563
  simp only [CollatzResearch.WordTrace]
  refine ⟨125013492881532107000935343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83342328587688071333956895 125013492881532107000935343)
  ·
    refine ⟨187520239322298160501403015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125013492881532107000935343 187520239322298160501403015)
    ·
      refine ⟨281280358983447240752104523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187520239322298160501403015 281280358983447240752104523)
      ·
        refine ⟨421920538475170861128156785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281280358983447240752104523 421920538475170861128156785)
        ·
          refine ⟨316440403856378145846117589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421920538475170861128156785 316440403856378145846117589)
          ·
            refine ⟨7416571965383862793268381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 316440403856378145846117589 7416571965383862793268381)
            ·
              refine ⟨2781214487018948547475643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7416571965383862793268381 2781214487018948547475643)
              ·
                refine ⟨4171821730528422821213465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781214487018948547475643 4171821730528422821213465)
                ·
                  refine ⟨3128866297896317115910099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171821730528422821213465 3128866297896317115910099)
                  ·
                    refine ⟨4693299446844475673865149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128866297896317115910099 4693299446844475673865149)
                    ·
                      refine ⟨1759987292566678377699431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693299446844475673865149 1759987292566678377699431)
                      ·
                        rfl

theorem cell23_3427563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 1, 3].length) (baseStart_3427563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427563 prefixEnd_3427563 := by exact prefixLift 3427563
  have htrace : WordTrace (prefixWord ++ tailWord_3427563) baseStart_3427563 baseEnd_3427563 := by
    simpa [prefixWord, tailWord_3427563, baseEnd_3427563] using wordTrace_append hprefix tailTrace_3427563
  have hstable : (prefixWord ++ tailWord_3427563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427563).length < 2 ^ (prefixWord ++ tailWord_3427563).sum := by decide
  have hdescent : baseEnd_3427563 < baseStart_3427563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427614 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3427614 : Nat := 118140960795 + 3427614 * 2 ^ 59
def prefixEnd_3427614 : Nat := 4983230072969 + 3 ^ 40 * 3427614 * 2
def baseEnd_3427614 : Nat := 1760013480080057678161697

theorem tailTrace_3427614 : CollatzResearch.WordTrace tailWord_3427614 prefixEnd_3427614 1760013480080057678161697 := by
  unfold tailWord_3427614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15626919125543417838880237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83343568669564895140694597 15626919125543417838880237)
  ·
    refine ⟨5860094672078781689580089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15626919125543417838880237 5860094672078781689580089)
    ·
      refine ⟨4395071004059086267185067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5860094672078781689580089 4395071004059086267185067)
      ·
        refine ⟨6592606506088629400777601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395071004059086267185067 6592606506088629400777601)
        ·
          refine ⟨4944454879566472050583201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6592606506088629400777601 4944454879566472050583201)
          ·
            refine ⟨3708341159674854037937401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944454879566472050583201 3708341159674854037937401)
            ·
              refine ⟨2781255869756140528453051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708341159674854037937401 2781255869756140528453051)
              ·
                refine ⟨4171883804634210792679577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781255869756140528453051 4171883804634210792679577)
                ·
                  refine ⟨3128912853475658094509683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171883804634210792679577 3128912853475658094509683)
                  ·
                    refine ⟨4693369280213487141764525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128912853475658094509683 4693369280213487141764525)
                    ·
                      refine ⟨1760013480080057678161697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693369280213487141764525 1760013480080057678161697)
                      ·
                        rfl

theorem cell23_3427614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3427614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427614 prefixEnd_3427614 := by exact prefixLift 3427614
  have htrace : WordTrace (prefixWord ++ tailWord_3427614) baseStart_3427614 baseEnd_3427614 := by
    simpa [prefixWord, tailWord_3427614, baseEnd_3427614] using wordTrace_append hprefix tailTrace_3427614
  have hstable : (prefixWord ++ tailWord_3427614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427614).length < 2 ^ (prefixWord ++ tailWord_3427614).sum := by decide
  have hdescent : baseEnd_3427614 < baseStart_3427614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427632 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_3427632 : Nat := 118140960795 + 3427632 * 2 ^ 59
def prefixEnd_3427632 : Nat := 4983230072969 + 3 ^ 40 * 3427632 * 2
def baseEnd_3427632 : Nat := 1760022722731838607736613

theorem tailTrace_3427632 : CollatzResearch.WordTrace tailWord_3427632 prefixEnd_3427632 1760022722731838607736613 := by
  unfold tailWord_3427632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62508004759141065892598575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83344006345521421190131433 62508004759141065892598575)
  ·
    refine ⟨93762007138711598838897863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62508004759141065892598575 93762007138711598838897863)
    ·
      refine ⟨140643010708067398258346795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93762007138711598838897863 140643010708067398258346795)
      ·
        refine ⟨210964516062101097387520193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140643010708067398258346795 210964516062101097387520193)
        ·
          refine ⟨158223387046575823040640145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210964516062101097387520193 158223387046575823040640145)
          ·
            refine ⟨118667540284931867280480109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158223387046575823040640145 118667540284931867280480109)
            ·
              refine ⟨44500327606849450230180041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118667540284931867280480109 44500327606849450230180041)
              ·
                refine ⟨33375245705137087672635031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44500327606849450230180041 33375245705137087672635031)
                ·
                  refine ⟨50062868557705631508952547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33375245705137087672635031 50062868557705631508952547)
                  ·
                    refine ⟨75094302836558447263428821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50062868557705631508952547 75094302836558447263428821)
                    ·
                      refine ⟨1760022722731838607736613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 75094302836558447263428821 1760022722731838607736613)
                      ·
                        rfl

theorem cell23_3427632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_3427632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427632 prefixEnd_3427632 := by exact prefixLift 3427632
  have htrace : WordTrace (prefixWord ++ tailWord_3427632) baseStart_3427632 baseEnd_3427632 := by
    simpa [prefixWord, tailWord_3427632, baseEnd_3427632] using wordTrace_append hprefix tailTrace_3427632
  have hstable : (prefixWord ++ tailWord_3427632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427632).length < 2 ^ (prefixWord ++ tailWord_3427632).sum := by decide
  have hdescent : baseEnd_3427632 < baseStart_3427632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427679 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_3427679 : Nat := 118140960795 + 3427679 * 2 ^ 59
def prefixEnd_3427679 : Nat := 4983230072969 + 3 ^ 40 * 3427679 * 2
def baseEnd_3427679 : Nat := 1760046856322599923848897

theorem tailTrace_3427679 : CollatzResearch.WordTrace tailWord_3427679 prefixEnd_3427679 1760046856322599923848897 := by
  unfold tailWord_3427679
  simp only [CollatzResearch.WordTrace]
  refine ⟨125017723749111858812158091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83345149166074572541438727 125017723749111858812158091)
  ·
    refine ⟨187526585623667788218237137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125017723749111858812158091 187526585623667788218237137)
    ·
      refine ⟨140644939217750841163677853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187526585623667788218237137 140644939217750841163677853)
      ·
        refine ⟨52741852206656565436379195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140644939217750841163677853 52741852206656565436379195)
        ·
          refine ⟨79112778309984848154568793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52741852206656565436379195 79112778309984848154568793)
          ·
            refine ⟨59334583732488636115926595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79112778309984848154568793 59334583732488636115926595)
            ·
              refine ⟨89001875598732954173889893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59334583732488636115926595 89001875598732954173889893)
              ·
                refine ⟨16687851674762428907604355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89001875598732954173889893 16687851674762428907604355)
                ·
                  refine ⟨25031777512143643361406533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16687851674762428907604355 25031777512143643361406533)
                  ·
                    refine ⟨4693458283526933130263725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25031777512143643361406533 4693458283526933130263725)
                    ·
                      refine ⟨1760046856322599923848897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693458283526933130263725 1760046856322599923848897)
                      ·
                        rfl

theorem cell23_3427679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_3427679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427679 prefixEnd_3427679 := by exact prefixLift 3427679
  have htrace : WordTrace (prefixWord ++ tailWord_3427679) baseStart_3427679 baseEnd_3427679 := by
    simpa [prefixWord, tailWord_3427679, baseEnd_3427679] using wordTrace_append hprefix tailTrace_3427679
  have hstable : (prefixWord ++ tailWord_3427679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427679).length < 2 ^ (prefixWord ++ tailWord_3427679).sum := by decide
  have hdescent : baseEnd_3427679 < baseStart_3427679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427690 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3427690 : Nat := 118140960795 + 3427690 * 2 ^ 59
def prefixEnd_3427690 : Nat := 4983230072969 + 3 ^ 40 * 3427690 * 2
def baseEnd_3427690 : Nat := 586684168203266460270449

theorem tailTrace_3427690 : CollatzResearch.WordTrace tailWord_3427690 prefixEnd_3427690 586684168203266460270449 := by
  unfold tailWord_3427690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31254531238018001922702131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83345416634714671793872349 31254531238018001922702131)
  ·
    refine ⟨46881796857027002884053197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31254531238018001922702131 46881796857027002884053197)
    ·
      refine ⟨17580673821385126081519949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46881796857027002884053197 17580673821385126081519949)
      ·
        refine ⟨6592752683019422280569981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17580673821385126081519949 6592752683019422280569981)
        ·
          refine ⟨2472282256132283355213743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6592752683019422280569981 2472282256132283355213743)
          ·
            refine ⟨3708423384198425032820615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472282256132283355213743 3708423384198425032820615)
            ·
              refine ⟨5562635076297637549230923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708423384198425032820615 5562635076297637549230923)
              ·
                refine ⟨8343952614446456323846385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562635076297637549230923 8343952614446456323846385)
                ·
                  refine ⟨6257964460834842242884789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343952614446456323846385 6257964460834842242884789)
                  ·
                    refine ⟨586684168203266460270449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6257964460834842242884789 586684168203266460270449)
                    ·
                      rfl

theorem cell23_3427690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3427690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427690 prefixEnd_3427690 := by exact prefixLift 3427690
  have htrace : WordTrace (prefixWord ++ tailWord_3427690) baseStart_3427690 baseEnd_3427690 := by
    simpa [prefixWord, tailWord_3427690, baseEnd_3427690] using wordTrace_append hprefix tailTrace_3427690
  have hstable : (prefixWord ++ tailWord_3427690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427690).length < 2 ^ (prefixWord ++ tailWord_3427690).sum := by decide
  have hdescent : baseEnd_3427690 < baseStart_3427690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427693 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3427693 : Nat := 118140960795 + 3427693 * 2 ^ 59
def prefixEnd_3427693 : Nat := 4983230072969 + 3 ^ 40 * 3427693 * 2
def baseEnd_3427693 : Nat := 1760054045051762869073833

theorem tailTrace_3427693 : CollatzResearch.WordTrace tailWord_3427693 prefixEnd_3427693 1760054045051762869073833 := by
  unfold tailWord_3427693
  simp only [CollatzResearch.WordTrace]
  refine ⟨125018234371061139203167733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83345489580707426135445155 125018234371061139203167733)
  ·
    refine ⟨11720459472286981800296975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125018234371061139203167733 11720459472286981800296975)
    ·
      refine ⟨17580689208430472700445463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11720459472286981800296975 17580689208430472700445463)
      ·
        refine ⟨26371033812645709050668195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17580689208430472700445463 26371033812645709050668195)
        ·
          refine ⟨39556550718968563576002293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26371033812645709050668195 39556550718968563576002293)
          ·
            refine ⟨3708426629903302835250215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39556550718968563576002293 3708426629903302835250215)
            ·
              refine ⟨5562639944854954252875323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708426629903302835250215 5562639944854954252875323)
              ·
                refine ⟨8343959917282431379312985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562639944854954252875323 8343959917282431379312985)
                ·
                  refine ⟨6257969937961823534484739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8343959917282431379312985 6257969937961823534484739)
                  ·
                    refine ⟨9386954906942735301727109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6257969937961823534484739 9386954906942735301727109)
                    ·
                      refine ⟨1760054045051762869073833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9386954906942735301727109 1760054045051762869073833)
                      ·
                        rfl

theorem cell23_3427693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3427693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427693 prefixEnd_3427693 := by exact prefixLift 3427693
  have htrace : WordTrace (prefixWord ++ tailWord_3427693) baseStart_3427693 baseEnd_3427693 := by
    simpa [prefixWord, tailWord_3427693, baseEnd_3427693] using wordTrace_append hprefix tailTrace_3427693
  have hstable : (prefixWord ++ tailWord_3427693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427693).length < 2 ^ (prefixWord ++ tailWord_3427693).sum := by decide
  have hdescent : baseEnd_3427693 < baseStart_3427693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427703 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 1, 4]
def baseStart_3427703 : Nat := 118140960795 + 3427703 * 2 ^ 59
def prefixEnd_3427703 : Nat := 4983230072969 + 3 ^ 40 * 3427703 * 2
def baseEnd_3427703 : Nat := 586686393286102609982929

theorem tailTrace_3427703 : CollatzResearch.WordTrace tailWord_3427703 prefixEnd_3427703 586686393286102609982929 := by
  unfold tailWord_3427703
  simp only [CollatzResearch.WordTrace]
  refine ⟨125018599101024910911031763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83345732734016607274021175 125018599101024910911031763)
  ·
    refine ⟨187527898651537366366547645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125018599101024910911031763 187527898651537366366547645)
    ·
      refine ⟨70322961994326512387455367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187527898651537366366547645 70322961994326512387455367)
      ·
        refine ⟨105484442991489768581183051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70322961994326512387455367 105484442991489768581183051)
        ·
          refine ⟨158226664487234652871774577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105484442991489768581183051 158226664487234652871774577)
          ·
            refine ⟨118669998365425989653830933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158226664487234652871774577 118669998365425989653830933)
            ·
              refine ⟨5562656173379343265023325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118669998365425989653830933 5562656173379343265023325)
              ·
                refine ⟨2085996065017253724383747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5562656173379343265023325 2085996065017253724383747)
                ·
                  refine ⟨3128994097525880586575621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085996065017253724383747 3128994097525880586575621)
                  ·
                    refine ⟨586686393286102609982929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128994097525880586575621 586686393286102609982929)
                    ·
                      rfl

theorem cell23_3427703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_3427703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427703 prefixEnd_3427703 := by exact prefixLift 3427703
  have htrace : WordTrace (prefixWord ++ tailWord_3427703) baseStart_3427703 baseEnd_3427703 := by
    simpa [prefixWord, tailWord_3427703, baseEnd_3427703] using wordTrace_append hprefix tailTrace_3427703
  have hstable : (prefixWord ++ tailWord_3427703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427703).length < 2 ^ (prefixWord ++ tailWord_3427703).sum := by decide
  have hdescent : baseEnd_3427703 < baseStart_3427703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427716 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 6]
def baseStart_3427716 : Nat := 118140960795 + 3427716 * 2 ^ 59
def prefixEnd_3427716 : Nat := 4983230072969 + 3 ^ 40 * 3427716 * 2
def baseEnd_3427716 : Nat := 195562872789646253231803

theorem tailTrace_3427716 : CollatzResearch.WordTrace tailWord_3427716 prefixEnd_3427716 195562872789646253231803 := by
  unfold tailWord_3427716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62509536624988907065627501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83346048833318542754170001 62509536624988907065627501)
  ·
    refine ⟨23441076234370840149610313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62509536624988907065627501 23441076234370840149610313)
    ·
      refine ⟨17580807175778130112207735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23441076234370840149610313 17580807175778130112207735)
      ·
        refine ⟨26371210763667195168311603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17580807175778130112207735 26371210763667195168311603)
        ·
          refine ⟨39556816145500792752467405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26371210763667195168311603 39556816145500792752467405)
          ·
            refine ⟨14833806054562797282175277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39556816145500792752467405 14833806054562797282175277)
            ·
              refine ⟨5562677270461048980815729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14833806054562797282175277 5562677270461048980815729)
              ·
                refine ⟨4172007952845786735611797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562677270461048980815729 4172007952845786735611797)
                ·
                  refine ⟨195562872789646253231803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4172007952845786735611797 195562872789646253231803)
                  ·
                    rfl

theorem cell23_3427716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_3427716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427716 prefixEnd_3427716 := by exact prefixLift 3427716
  have htrace : WordTrace (prefixWord ++ tailWord_3427716) baseStart_3427716 baseEnd_3427716 := by
    simpa [prefixWord, tailWord_3427716, baseEnd_3427716] using wordTrace_append hprefix tailTrace_3427716
  have hstable : (prefixWord ++ tailWord_3427716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427716).length < 2 ^ (prefixWord ++ tailWord_3427716).sum := by decide
  have hdescent : baseEnd_3427716 < baseStart_3427716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427719 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3427719 : Nat := 118140960795 + 3427719 * 2 ^ 59
def prefixEnd_3427719 : Nat := 4983230072969 + 3 ^ 40 * 3427719 * 2
def baseEnd_3427719 : Nat := 1760067395548779767348713

theorem tailTrace_3427719 : CollatzResearch.WordTrace tailWord_3427719 prefixEnd_3427719 1760067395548779767348713 := by
  unfold tailWord_3427719
  simp only [CollatzResearch.WordTrace]
  refine ⟨125019182668966945643614211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83346121779311297095742807 125019182668966945643614211)
  ·
    refine ⟨187528774003450418465421317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125019182668966945643614211 187528774003450418465421317)
    ·
      refine ⟨35161645125646953462266497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187528774003450418465421317 35161645125646953462266497)
      ·
        refine ⟨26371233844235215096699873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35161645125646953462266497 26371233844235215096699873)
        ·
          refine ⟨19778425383176411322524905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26371233844235215096699873 19778425383176411322524905)
          ·
            refine ⟨14833819037382308491893679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19778425383176411322524905 14833819037382308491893679)
            ·
              refine ⟨22250728556073462737840519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14833819037382308491893679 22250728556073462737840519)
              ·
                refine ⟨33376092834110194106760779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22250728556073462737840519 33376092834110194106760779)
                ·
                  refine ⟨50064139251165291160141169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33376092834110194106760779 50064139251165291160141169)
                  ·
                    refine ⟨37548104438373968370105877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50064139251165291160141169 37548104438373968370105877)
                    ·
                      refine ⟨1760067395548779767348713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37548104438373968370105877 1760067395548779767348713)
                      ·
                        rfl

theorem cell23_3427719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3427719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427719 prefixEnd_3427719 := by exact prefixLift 3427719
  have htrace : WordTrace (prefixWord ++ tailWord_3427719) baseStart_3427719 baseEnd_3427719 := by
    simpa [prefixWord, tailWord_3427719, baseEnd_3427719] using wordTrace_append hprefix tailTrace_3427719
  have hstable : (prefixWord ++ tailWord_3427719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427719).length < 2 ^ (prefixWord ++ tailWord_3427719).sum := by decide
  have hdescent : baseEnd_3427719 < baseStart_3427719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427743 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3427743 : Nat := 118140960795 + 3427743 * 2 ^ 59
def prefixEnd_3427743 : Nat := 4983230072969 + 3 ^ 40 * 3427743 * 2
def baseEnd_3427743 : Nat := 1760079719084487673448603

theorem tailTrace_3427743 : CollatzResearch.WordTrace tailWord_3427743 prefixEnd_3427743 1760079719084487673448603 := by
  unfold tailWord_3427743
  simp only [CollatzResearch.WordTrace]
  refine ⟨125020058020879997742487883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83346705347253331828325255 125020058020879997742487883)
  ·
    refine ⟨187530087031319996613731825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125020058020879997742487883 187530087031319996613731825)
    ·
      refine ⟨140647565273489997460298869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187530087031319996613731825 140647565273489997460298869)
      ·
        refine ⟨13185709244389687261903019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140647565273489997460298869 13185709244389687261903019)
        ·
          refine ⟨19778563866584530892854529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13185709244389687261903019 19778563866584530892854529)
          ·
            refine ⟨14833922899938398169640897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19778563866584530892854529 14833922899938398169640897)
            ·
              refine ⟨11125442174953798627230673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14833922899938398169640897 11125442174953798627230673)
              ·
                refine ⟨8344081631215348970423005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11125442174953798627230673 8344081631215348970423005)
                ·
                  refine ⟨3129030611705755863908627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8344081631215348970423005 3129030611705755863908627)
                  ·
                    refine ⟨4693545917558633795862941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3129030611705755863908627 4693545917558633795862941)
                    ·
                      refine ⟨1760079719084487673448603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693545917558633795862941 1760079719084487673448603)
                      ·
                        rfl

theorem cell23_3427743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3427743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427743 prefixEnd_3427743 := by exact prefixLift 3427743
  have htrace : WordTrace (prefixWord ++ tailWord_3427743) baseStart_3427743 baseEnd_3427743 := by
    simpa [prefixWord, tailWord_3427743, baseEnd_3427743] using wordTrace_append hprefix tailTrace_3427743
  have hstable : (prefixWord ++ tailWord_3427743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427743).length < 2 ^ (prefixWord ++ tailWord_3427743).sum := by decide
  have hdescent : baseEnd_3427743 < baseStart_3427743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427759 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 1, 6]
def baseStart_3427759 : Nat := 118140960795 + 3427759 * 2 ^ 59
def prefixEnd_3427759 : Nat := 4983230072969 + 3 ^ 40 * 3427759 * 2
def baseEnd_3427759 : Nat := 586695978258319870282843

theorem tailTrace_3427759 : CollatzResearch.WordTrace tailWord_3427759 prefixEnd_3427759 586695978258319870282843 := by
  unfold tailWord_3427759
  simp only [CollatzResearch.WordTrace]
  refine ⟨125020641588822032475070331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83347094392548021650046887 125020641588822032475070331)
  ·
    refine ⟨187530962383233048712605497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125020641588822032475070331 187530962383233048712605497)
    ·
      refine ⟨140648221787424786534454123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187530962383233048712605497 140648221787424786534454123)
      ·
        refine ⟨210972332681137179801681185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140648221787424786534454123 210972332681137179801681185)
        ·
          refine ⟨158229249510852884851260889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210972332681137179801681185 158229249510852884851260889)
          ·
            refine ⟨118671937133139663638445667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158229249510852884851260889 118671937133139663638445667)
            ·
              refine ⟨178007905699709495457668501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118671937133139663638445667 178007905699709495457668501)
              ·
                refine ⟨8344120579673882599578211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178007905699709495457668501 8344120579673882599578211)
                ·
                  refine ⟨12516180869510823899367317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344120579673882599578211 12516180869510823899367317)
                  ·
                    refine ⟨586695978258319870282843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12516180869510823899367317 586695978258319870282843)
                    ·
                      rfl

theorem cell23_3427759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_3427759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427759 prefixEnd_3427759 := by exact prefixLift 3427759
  have htrace : WordTrace (prefixWord ++ tailWord_3427759) baseStart_3427759 baseEnd_3427759 := by
    simpa [prefixWord, tailWord_3427759, baseEnd_3427759] using wordTrace_append hprefix tailTrace_3427759
  have hstable : (prefixWord ++ tailWord_3427759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427759).length < 2 ^ (prefixWord ++ tailWord_3427759).sum := by decide
  have hdescent : baseEnd_3427759 < baseStart_3427759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427776 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_3427776 : Nat := 118140960795 + 3427776 * 2 ^ 59
def prefixEnd_3427776 : Nat := 4983230072969 + 3 ^ 40 * 3427776 * 2
def baseEnd_3427776 : Nat := 586698887982028681445317

theorem tailTrace_3427776 : CollatzResearch.WordTrace tailWord_3427776 prefixEnd_3427776 586698887982028681445317 := by
  unfold tailWord_3427776
  simp only [CollatzResearch.WordTrace]
  refine ⟨62510630814880222189219591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83347507753173629585626121 62510630814880222189219591)
  ·
    refine ⟨93765946222320333283829387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62510630814880222189219591 93765946222320333283829387)
    ·
      refine ⟨140648919333480499925744081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93765946222320333283829387 140648919333480499925744081)
      ·
        refine ⟨105486689500110374944308061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140648919333480499925744081 105486689500110374944308061)
        ·
          refine ⟨39557508562541390604115523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105486689500110374944308061 39557508562541390604115523)
          ·
            refine ⟨59336262843812085906173285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39557508562541390604115523 59336262843812085906173285)
            ·
              refine ⟨11125549283214766107407491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59336262843812085906173285 11125549283214766107407491)
              ·
                refine ⟨16688323924822149161111237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11125549283214766107407491 16688323924822149161111237)
                ·
                  refine ⟨3129060735904152967708357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16688323924822149161111237 3129060735904152967708357)
                  ·
                    refine ⟨586698887982028681445317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129060735904152967708357 586698887982028681445317)
                    ·
                      rfl

theorem cell23_3427776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_3427776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427776 prefixEnd_3427776 := by exact prefixLift 3427776
  have htrace : WordTrace (prefixWord ++ tailWord_3427776) baseStart_3427776 baseEnd_3427776 := by
    simpa [prefixWord, tailWord_3427776, baseEnd_3427776] using wordTrace_append hprefix tailTrace_3427776
  have hstable : (prefixWord ++ tailWord_3427776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427776).length < 2 ^ (prefixWord ++ tailWord_3427776).sum := by decide
  have hdescent : baseEnd_3427776 < baseStart_3427776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427779 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_3427779 : Nat := 118140960795 + 3427779 * 2 ^ 59
def prefixEnd_3427779 : Nat := 4983230072969 + 3 ^ 40 * 3427779 * 2
def baseEnd_3427779 : Nat := 1760098204388049532598437

theorem tailTrace_3427779 : CollatzResearch.WordTrace tailWord_3427779 prefixEnd_3427779 1760098204388049532598437 := by
  unfold tailWord_3427779
  simp only [CollatzResearch.WordTrace]
  refine ⟨125021371048749575890798391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83347580699166383927198927 125021371048749575890798391)
  ·
    refine ⟨187532056573124363836197587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125021371048749575890798391 187532056573124363836197587)
    ·
      refine ⟨281298084859686545754296381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187532056573124363836197587 281298084859686545754296381)
      ·
        refine ⟨105486781822382454657861143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281298084859686545754296381 105486781822382454657861143)
        ·
          refine ⟨158230172733573681986791715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105486781822382454657861143 158230172733573681986791715)
          ·
            refine ⟨237345259100360522980187573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158230172733573681986791715 237345259100360522980187573)
            ·
              refine ⟨22251118040658799029392585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237345259100360522980187573 22251118040658799029392585)
              ·
                refine ⟨16688338530494099272044439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22251118040658799029392585 16688338530494099272044439)
                ·
                  refine ⟨25032507795741148908066659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16688338530494099272044439 25032507795741148908066659)
                  ·
                    refine ⟨37548761693611723362099989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25032507795741148908066659 37548761693611723362099989)
                    ·
                      refine ⟨1760098204388049532598437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37548761693611723362099989 1760098204388049532598437)
                      ·
                        rfl

theorem cell23_3427779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_3427779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427779 prefixEnd_3427779 := by exact prefixLift 3427779
  have htrace : WordTrace (prefixWord ++ tailWord_3427779) baseStart_3427779 baseEnd_3427779 := by
    simpa [prefixWord, tailWord_3427779, baseEnd_3427779] using wordTrace_append hprefix tailTrace_3427779
  have hstable : (prefixWord ++ tailWord_3427779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427779).length < 2 ^ (prefixWord ++ tailWord_3427779).sum := by decide
  have hdescent : baseEnd_3427779 < baseStart_3427779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427786 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3427786 : Nat := 118140960795 + 3427786 * 2 ^ 59
def prefixEnd_3427786 : Nat := 4983230072969 + 3 ^ 40 * 3427786 * 2
def baseEnd_3427786 : Nat := 1760101798752631005210905

theorem tailTrace_3427786 : CollatzResearch.WordTrace tailWord_3427786 prefixEnd_3427786 1760101798752631005210905 := by
  unfold tailWord_3427786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255406589931054021575803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83347750906482810724202141 31255406589931054021575803)
  ·
    refine ⟨46883109884896581032363705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31255406589931054021575803 46883109884896581032363705)
    ·
      refine ⟨35162332413672435774272779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46883109884896581032363705 35162332413672435774272779)
      ·
        refine ⟨52743498620508653661409169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35162332413672435774272779 52743498620508653661409169)
        ·
          refine ⟨39557623965381490246056877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52743498620508653661409169 39557623965381490246056877)
          ·
            refine ⟨14834108987018058842271329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39557623965381490246056877 14834108987018058842271329)
            ·
              refine ⟨11125581740263544131703497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14834108987018058842271329 11125581740263544131703497)
              ·
                refine ⟨8344186305197658098777623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11125581740263544131703497 8344186305197658098777623)
                ·
                  refine ⟨12516279457796487148166435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344186305197658098777623 12516279457796487148166435)
                  ·
                    refine ⟨18774419186694730722249653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12516279457796487148166435 18774419186694730722249653)
                    ·
                      refine ⟨1760101798752631005210905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18774419186694730722249653 1760101798752631005210905)
                      ·
                        rfl

theorem cell23_3427786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3427786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427786 prefixEnd_3427786 := by exact prefixLift 3427786
  have htrace : WordTrace (prefixWord ++ tailWord_3427786) baseStart_3427786 baseEnd_3427786 := by
    simpa [prefixWord, tailWord_3427786, baseEnd_3427786] using wordTrace_append hprefix tailTrace_3427786
  have hstable : (prefixWord ++ tailWord_3427786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427786).length < 2 ^ (prefixWord ++ tailWord_3427786).sum := by decide
  have hdescent : baseEnd_3427786 < baseStart_3427786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427813 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3427813 : Nat := 118140960795 + 3427813 * 2 ^ 59
def prefixEnd_3427813 : Nat := 4983230072969 + 3 ^ 40 * 3427813 * 2
def baseEnd_3427813 : Nat := 1760115662730302399573281

theorem tailTrace_3427813 : CollatzResearch.WordTrace tailWord_3427813 prefixEnd_3427813 1760115662730302399573281 := by
  unfold tailWord_3427813
  simp only [CollatzResearch.WordTrace]
  refine ⟨125022611130626399697536093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83348407420417599798357395 125022611130626399697536093)
  ·
    refine ⟨46883479173984899886576035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125022611130626399697536093 46883479173984899886576035)
    ·
      refine ⟨70325218760977349829864053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46883479173984899886576035 70325218760977349829864053)
      ·
        refine ⟨6592989258841626546549755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70325218760977349829864053 6592989258841626546549755)
        ·
          refine ⟨9889483888262439819824633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592989258841626546549755 9889483888262439819824633)
          ·
            refine ⟨7417112916196829864868475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9889483888262439819824633 7417112916196829864868475)
            ·
              refine ⟨11125669374295244797302713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417112916196829864868475 11125669374295244797302713)
              ·
                refine ⟨8344252030721433597977035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11125669374295244797302713 8344252030721433597977035)
                ·
                  refine ⟨12516378046082150396965553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8344252030721433597977035 12516378046082150396965553)
                  ·
                    refine ⟨9387283534561612797724165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12516378046082150396965553 9387283534561612797724165)
                    ·
                      refine ⟨1760115662730302399573281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9387283534561612797724165 1760115662730302399573281)
                      ·
                        rfl

theorem cell23_3427813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3427813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427813 prefixEnd_3427813 := by exact prefixLift 3427813
  have htrace : WordTrace (prefixWord ++ tailWord_3427813) baseStart_3427813 baseEnd_3427813 := by
    simpa [prefixWord, tailWord_3427813, baseEnd_3427813] using wordTrace_append hprefix tailTrace_3427813
  have hstable : (prefixWord ++ tailWord_3427813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427813).length < 2 ^ (prefixWord ++ tailWord_3427813).sum := by decide
  have hdescent : baseEnd_3427813 < baseStart_3427813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427850 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3427850 : Nat := 118140960795 + 3427850 * 2 ^ 59
def prefixEnd_3427850 : Nat := 4983230072969 + 3 ^ 40 * 3427850 * 2
def baseEnd_3427850 : Nat := 1760134661514518754810611

theorem tailTrace_3427850 : CollatzResearch.WordTrace tailWord_3427850 prefixEnd_3427850 1760134661514518754810611 := by
  unfold tailWord_3427850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255990157873088754158251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83349307087661570011088669 31255990157873088754158251)
  ·
    refine ⟨46883985236809633131237377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31255990157873088754158251 46883985236809633131237377)
    ·
      refine ⟨35162988927607224848428033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46883985236809633131237377 35162988927607224848428033)
      ·
        refine ⟨26372241695705418636321025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35162988927607224848428033 26372241695705418636321025)
        ·
          refine ⟨19779181271779063977240769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26372241695705418636321025 19779181271779063977240769)
          ·
            refine ⟨14834385953834297982930577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19779181271779063977240769 14834385953834297982930577)
            ·
              refine ⟨11125789465375723487197933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14834385953834297982930577 11125789465375723487197933)
              ·
                refine ⟨4172171049515896307699225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11125789465375723487197933 4172171049515896307699225)
                ·
                  refine ⟨3129128287136922230774419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172171049515896307699225 3129128287136922230774419)
                  ·
                    refine ⟨4693692430705383346161629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3129128287136922230774419 4693692430705383346161629)
                    ·
                      refine ⟨1760134661514518754810611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693692430705383346161629 1760134661514518754810611)
                      ·
                        rfl

theorem cell23_3427850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3427850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427850 prefixEnd_3427850 := by exact prefixLift 3427850
  have htrace : WordTrace (prefixWord ++ tailWord_3427850) baseStart_3427850 baseEnd_3427850 := by
    simpa [prefixWord, tailWord_3427850, baseEnd_3427850] using wordTrace_append hprefix tailTrace_3427850
  have hstable : (prefixWord ++ tailWord_3427850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427850).length < 2 ^ (prefixWord ++ tailWord_3427850).sum := by decide
  have hdescent : baseEnd_3427850 < baseStart_3427850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427896 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 7]
def baseStart_3427896 : Nat := 118140960795 + 3427896 * 2 ^ 59
def prefixEnd_3427896 : Nat := 4983230072969 + 3 ^ 40 * 3427896 * 2
def baseEnd_3427896 : Nat := 195573142402736174981711

theorem tailTrace_3427896 : CollatzResearch.WordTrace tailWord_3427896 prefixEnd_3427896 195573142402736174981711 := by
  unfold tailWord_3427896
  simp only [CollatzResearch.WordTrace]
  refine ⟨62512819194662852436403771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83350425592883803248538361 62512819194662852436403771)
  ·
    refine ⟨93769228791994278654605657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62512819194662852436403771 93769228791994278654605657)
    ·
      refine ⟨70326921593995708990954243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93769228791994278654605657 70326921593995708990954243)
      ·
        refine ⟨105490382390993563486431365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70326921593995708990954243 105490382390993563486431365)
        ·
          refine ⟨19779446698311293153705881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105490382390993563486431365 19779446698311293153705881)
          ·
            refine ⟨14834585023733469865279411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19779446698311293153705881 14834585023733469865279411)
            ·
              refine ⟨22251877535600204797919117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14834585023733469865279411 22251877535600204797919117)
              ·
                refine ⟨8344454075850076799219669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22251877535600204797919117 8344454075850076799219669)
                ·
                  refine ⟨195573142402736174981711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8344454075850076799219669 195573142402736174981711)
                  ·
                    rfl

theorem cell23_3427896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_3427896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427896 prefixEnd_3427896 := by exact prefixLift 3427896
  have htrace : WordTrace (prefixWord ++ tailWord_3427896) baseStart_3427896 baseEnd_3427896 := by
    simpa [prefixWord, tailWord_3427896, baseEnd_3427896] using wordTrace_append hprefix tailTrace_3427896
  have hstable : (prefixWord ++ tailWord_3427896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427896).length < 2 ^ (prefixWord ++ tailWord_3427896).sum := by decide
  have hdescent : baseEnd_3427896 < baseStart_3427896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427936 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_3427936 : Nat := 118140960795 + 3427936 * 2 ^ 59
def prefixEnd_3427936 : Nat := 4983230072969 + 3 ^ 40 * 3427936 * 2
def baseEnd_3427936 : Nat := 1760178820850805418335215

theorem tailTrace_3427936 : CollatzResearch.WordTrace tailWord_3427936 prefixEnd_3427936 1760178820850805418335215 := by
  unfold tailWord_3427936
  simp only [CollatzResearch.WordTrace]
  refine ⟨62513548654590395852131831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83351398206120527802842441 62513548654590395852131831)
  ·
    refine ⟨93770322981885593778197747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62513548654590395852131831 93770322981885593778197747)
    ·
      refine ⟨140655484472828390667296621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93770322981885593778197747 140655484472828390667296621)
      ·
        refine ⟨52745806677310646500236233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140655484472828390667296621 52745806677310646500236233)
        ·
          refine ⟨39559355007982984875177175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52745806677310646500236233 39559355007982984875177175)
          ·
            refine ⟨59339032511974477312765763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39559355007982984875177175 59339032511974477312765763)
            ·
              refine ⟨89008548767961715969148645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59339032511974477312765763 89008548767961715969148645)
              ·
                refine ⟨16689102893992821744215371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89008548767961715969148645 16689102893992821744215371)
                ·
                  refine ⟨25033654340989232616323057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16689102893992821744215371 25033654340989232616323057)
                  ·
                    refine ⟨18775240755741924462242293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25033654340989232616323057 18775240755741924462242293)
                    ·
                      refine ⟨1760178820850805418335215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18775240755741924462242293 1760178820850805418335215)
                      ·
                        rfl

theorem cell23_3427936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_3427936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427936 prefixEnd_3427936 := by exact prefixLift 3427936
  have htrace : WordTrace (prefixWord ++ tailWord_3427936) baseStart_3427936 baseEnd_3427936 := by
    simpa [prefixWord, tailWord_3427936, baseEnd_3427936] using wordTrace_append hprefix tailTrace_3427936
  have hstable : (prefixWord ++ tailWord_3427936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427936).length < 2 ^ (prefixWord ++ tailWord_3427936).sum := by decide
  have hdescent : baseEnd_3427936 < baseStart_3427936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427963 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 6, 2]
def baseStart_3427963 : Nat := 118140960795 + 3427963 * 2 ^ 59
def prefixEnd_3427963 : Nat := 4983230072969 + 3 ^ 40 * 3427963 * 2
def baseEnd_3427963 : Nat := 1760192684828476812697591

theorem tailTrace_3427963 : CollatzResearch.WordTrace tailWord_3427963 prefixEnd_3427963 1760192684828476812697591 := by
  unfold tailWord_3427963
  simp only [CollatzResearch.WordTrace]
  refine ⟨125028082080082975315496543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83352054720055316876997695 125028082080082975315496543)
  ·
    refine ⟨187542123120124462973244815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125028082080082975315496543 187542123120124462973244815)
    ·
      refine ⟨281313184680186694459867223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187542123120124462973244815 281313184680186694459867223)
      ·
        refine ⟨421969777020280041689800835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281313184680186694459867223 421969777020280041689800835)
        ·
          refine ⟨632954665530420062534701253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421969777020280041689800835 632954665530420062534701253)
          ·
            refine ⟨118678999786953761725256485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632954665530420062534701253 118678999786953761725256485)
            ·
              refine ⟨22252312460053830323485591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118678999786953761725256485 22252312460053830323485591)
              ·
                refine ⟨33378468690080745485228387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22252312460053830323485591 33378468690080745485228387)
                ·
                  refine ⟨50067703035121118227842581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33378468690080745485228387 50067703035121118227842581)
                  ·
                    refine ⟨2346923579771302416930121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50067703035121118227842581 2346923579771302416930121)
                    ·
                      refine ⟨1760192684828476812697591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346923579771302416930121 1760192684828476812697591)
                      ·
                        rfl

theorem cell23_3427963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6, 2].length) (baseStart_3427963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427963 prefixEnd_3427963 := by exact prefixLift 3427963
  have htrace : WordTrace (prefixWord ++ tailWord_3427963) baseStart_3427963 baseEnd_3427963 := by
    simpa [prefixWord, tailWord_3427963, baseEnd_3427963] using wordTrace_append hprefix tailTrace_3427963
  have hstable : (prefixWord ++ tailWord_3427963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427963).length < 2 ^ (prefixWord ++ tailWord_3427963).sum := by decide
  have hdescent : baseEnd_3427963 < baseStart_3427963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3427973 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_3427973 : Nat := 118140960795 + 3427973 * 2 ^ 59
def prefixEnd_3427973 : Nat := 4983230072969 + 3 ^ 40 * 3427973 * 2
def baseEnd_3427973 : Nat := 586732606545007257857515

theorem tailTrace_3427973 : CollatzResearch.WordTrace tailWord_3427973 prefixEnd_3427973 586732606545007257857515 := by
  unfold tailWord_3427973
  simp only [CollatzResearch.WordTrace]
  refine ⟨125028446810046747023360573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83352297873364498015573715 125028446810046747023360573)
  ·
    refine ⟨46885667553767530133760215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125028446810046747023360573 46885667553767530133760215)
    ·
      refine ⟨70328501330651295200640323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46885667553767530133760215 70328501330651295200640323)
      ·
        refine ⟨105492751995976942800960485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70328501330651295200640323 105492751995976942800960485)
        ·
          refine ⟨19779890999245676775180091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105492751995976942800960485 19779890999245676775180091)
          ·
            refine ⟨29669836498868515162770137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19779890999245676775180091 29669836498868515162770137)
            ·
              refine ⟨22252377374151386372077603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29669836498868515162770137 22252377374151386372077603)
              ·
                refine ⟨33378566061227079558116405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22252377374151386372077603 33378566061227079558116405)
                ·
                  refine ⟨3129240568240038708573413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33378566061227079558116405 3129240568240038708573413)
                  ·
                    refine ⟨586732606545007257857515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129240568240038708573413 586732606545007257857515)
                    ·
                      rfl

theorem cell23_3427973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_3427973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3427973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3427973 prefixEnd_3427973 := by exact prefixLift 3427973
  have htrace : WordTrace (prefixWord ++ tailWord_3427973) baseStart_3427973 baseEnd_3427973 := by
    simpa [prefixWord, tailWord_3427973, baseEnd_3427973] using wordTrace_append hprefix tailTrace_3427973
  have hstable : (prefixWord ++ tailWord_3427973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3427973).length < 2 ^ (prefixWord ++ tailWord_3427973).sum := by decide
  have hdescent : baseEnd_3427973 < baseStart_3427973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3427973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428000 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3428000 : Nat := 118140960795 + 3428000 * 2 ^ 59
def prefixEnd_3428000 : Nat := 4983230072969 + 3 ^ 40 * 3428000 * 2
def baseEnd_3428000 : Nat := 1760211683612693167934921

theorem tailTrace_3428000 : CollatzResearch.WordTrace tailWord_3428000 prefixEnd_3428000 1760211683612693167934921 := by
  unfold tailWord_3428000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62514715790474465317296727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83352954387299287089728969 62514715790474465317296727)
  ·
    refine ⟨93772073685711697975945091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62514715790474465317296727 93772073685711697975945091)
    ·
      refine ⟨140658110528567546963917637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93772073685711697975945091 140658110528567546963917637)
      ·
        refine ⟨26373395724106415055734557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140658110528567546963917637 26373395724106415055734557)
        ·
          refine ⟨9890023396539905645900459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26373395724106415055734557 9890023396539905645900459)
          ·
            refine ⟨14835035094809858468850689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9890023396539905645900459 14835035094809858468850689)
            ·
              refine ⟨11126276321107393851638017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14835035094809858468850689 11126276321107393851638017)
              ·
                refine ⟨8344707240830545388728513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126276321107393851638017 8344707240830545388728513)
                ·
                  refine ⟨6258530430622909041546385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344707240830545388728513 6258530430622909041546385)
                  ·
                    refine ⟨4693897822967181781159789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258530430622909041546385 4693897822967181781159789)
                    ·
                      refine ⟨1760211683612693167934921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4693897822967181781159789 1760211683612693167934921)
                      ·
                        rfl

theorem cell23_3428000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3428000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428000 prefixEnd_3428000 := by exact prefixLift 3428000
  have htrace : WordTrace (prefixWord ++ tailWord_3428000) baseStart_3428000 baseEnd_3428000 := by
    simpa [prefixWord, tailWord_3428000, baseEnd_3428000] using wordTrace_append hprefix tailTrace_3428000
  have hstable : (prefixWord ++ tailWord_3428000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428000).length < 2 ^ (prefixWord ++ tailWord_3428000).sum := by decide
  have hdescent : baseEnd_3428000 < baseStart_3428000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428003 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 6]
def baseStart_3428003 : Nat := 118140960795 + 3428003 * 2 ^ 59
def prefixEnd_3428003 : Nat := 4983230072969 + 3 ^ 40 * 3428003 * 2
def baseEnd_3428003 : Nat := 195579247117184072910823

theorem tailTrace_3428003 : CollatzResearch.WordTrace tailWord_3428003 prefixEnd_3428003 195579247117184072910823 := by
  unfold tailWord_3428003
  simp only [CollatzResearch.WordTrace]
  refine ⟨125029540999938062146952663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83353027333292041431301775 125029540999938062146952663)
  ·
    refine ⟨187544311499907093220428995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125029540999938062146952663 187544311499907093220428995)
    ·
      refine ⟨281316467249860639830643493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187544311499907093220428995 281316467249860639830643493)
      ·
        refine ⟨52746837609348869968245655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281316467249860639830643493 52746837609348869968245655)
        ·
          refine ⟨79120256414023304952368483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52746837609348869968245655 79120256414023304952368483)
          ·
            refine ⟨118680384621034957428552725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79120256414023304952368483 118680384621034957428552725)
            ·
              refine ⟨5563143029111013629463409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118680384621034957428552725 5563143029111013629463409)
              ·
                refine ⟨4172357271833260222097557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5563143029111013629463409 4172357271833260222097557)
                ·
                  refine ⟨195579247117184072910823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4172357271833260222097557 195579247117184072910823)
                  ·
                    rfl

theorem cell23_3428003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 6].length) (baseStart_3428003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428003 prefixEnd_3428003 := by exact prefixLift 3428003
  have htrace : WordTrace (prefixWord ++ tailWord_3428003) baseStart_3428003 baseEnd_3428003 := by
    simpa [prefixWord, tailWord_3428003, baseEnd_3428003] using wordTrace_append hprefix tailTrace_3428003
  have hstable : (prefixWord ++ tailWord_3428003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428003).length < 2 ^ (prefixWord ++ tailWord_3428003).sum := by decide
  have hdescent : baseEnd_3428003 < baseStart_3428003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428014 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3428014 : Nat := 118140960795 + 3428014 * 2 ^ 59
def prefixEnd_3428014 : Nat := 4983230072969 + 3 ^ 40 * 3428014 * 2
def baseEnd_3428014 : Nat := 1760218872341856113159857

theorem tailTrace_3428014 : CollatzResearch.WordTrace tailWord_3428014 prefixEnd_3428014 1760218872341856113159857 := by
  unfold tailWord_3428014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628742775362276378200387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83353294801932140683735397 15628742775362276378200387)
  ·
    refine ⟨23443114163043414567300581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15628742775362276378200387 23443114163043414567300581)
    ·
      refine ⟨4395583905570640231368859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23443114163043414567300581 4395583905570640231368859)
      ·
        refine ⟨6593375858355960347053289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395583905570640231368859 6593375858355960347053289)
        ·
          refine ⟨4945031893766970260289967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6593375858355960347053289 4945031893766970260289967)
          ·
            refine ⟨7417547840650455390434951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945031893766970260289967 7417547840650455390434951)
            ·
              refine ⟨11126321760975683085652427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417547840650455390434951 11126321760975683085652427)
              ·
                refine ⟨16689482641463524628478641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126321760975683085652427 16689482641463524628478641)
                ·
                  refine ⟨12517111981097643471358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16689482641463524628478641 12517111981097643471358981)
                  ·
                    refine ⟨2346958496455808150879809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12517111981097643471358981 2346958496455808150879809)
                    ·
                      refine ⟨1760218872341856113159857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346958496455808150879809 1760218872341856113159857)
                      ·
                        rfl

theorem cell23_3428014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3428014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428014 prefixEnd_3428014 := by exact prefixLift 3428014
  have htrace : WordTrace (prefixWord ++ tailWord_3428014) baseStart_3428014 baseEnd_3428014 := by
    simpa [prefixWord, tailWord_3428014, baseEnd_3428014] using wordTrace_append hprefix tailTrace_3428014
  have hstable : (prefixWord ++ tailWord_3428014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428014).length < 2 ^ (prefixWord ++ tailWord_3428014).sum := by decide
  have hdescent : baseEnd_3428014 < baseStart_3428014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428040 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_3428040 : Nat := 118140960795 + 3428040 * 2 ^ 59
def prefixEnd_3428040 : Nat := 4983230072969 + 3 ^ 40 * 3428040 * 2
def baseEnd_3428040 : Nat := 1760232222838873011434737

theorem tailTrace_3428040 : CollatzResearch.WordTrace tailWord_3428040 prefixEnd_3428040 1760232222838873011434737 := by
  unfold tailWord_3428040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62515445250402008733024787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83353927000536011644033049 62515445250402008733024787)
  ·
    refine ⟨93773167875603013099537181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62515445250402008733024787 93773167875603013099537181)
    ·
      refine ⟨35164937953351129912326443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93773167875603013099537181 35164937953351129912326443)
      ·
        refine ⟨52747406930026694868489665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35164937953351129912326443 52747406930026694868489665)
        ·
          refine ⟨39560555197520021151367249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52747406930026694868489665 39560555197520021151367249)
          ·
            refine ⟨29670416398140015863525437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39560555197520021151367249 29670416398140015863525437)
            ·
              refine ⟨11126406149302505948822039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29670416398140015863525437 11126406149302505948822039)
              ·
                refine ⟨16689609223953758923233059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126406149302505948822039 16689609223953758923233059)
                ·
                  refine ⟨25034413835930638384849589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16689609223953758923233059 25034413835930638384849589)
                  ·
                    refine ⟨2346976297118497348579649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25034413835930638384849589 2346976297118497348579649)
                    ·
                      refine ⟨1760232222838873011434737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2346976297118497348579649 1760232222838873011434737)
                      ·
                        rfl

theorem cell23_3428040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_3428040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428040 prefixEnd_3428040 := by exact prefixLift 3428040
  have htrace : WordTrace (prefixWord ++ tailWord_3428040) baseStart_3428040 baseEnd_3428040 := by
    simpa [prefixWord, tailWord_3428040, baseEnd_3428040] using wordTrace_append hprefix tailTrace_3428040
  have hstable : (prefixWord ++ tailWord_3428040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428040).length < 2 ^ (prefixWord ++ tailWord_3428040).sum := by decide
  have hdescent : baseEnd_3428040 < baseStart_3428040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428084 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_3428084 : Nat := 118140960795 + 3428084 * 2 ^ 59
def prefixEnd_3428084 : Nat := 4983230072969 + 3 ^ 40 * 3428084 * 2
def baseEnd_3428084 : Nat := 586751605329223613094845

theorem tailTrace_3428084 : CollatzResearch.WordTrace tailWord_3428084 prefixEnd_3428084 586751605329223613094845 := by
  unfold tailWord_3428084
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516247656322306490325653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83354996875096408653767537 62516247656322306490325653)
  ·
    refine ⟨2930449108890108116734015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62516247656322306490325653 2930449108890108116734015)
    ·
      refine ⟨4395673663335162175101023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930449108890108116734015 4395673663335162175101023)
      ·
        refine ⟨6593510495002743262651535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395673663335162175101023 6593510495002743262651535)
        ·
          refine ⟨9890265742504114893977303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6593510495002743262651535 9890265742504114893977303)
          ·
            refine ⟨14835398613756172340965955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9890265742504114893977303 14835398613756172340965955)
            ·
              refine ⟨22253097920634258511448933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14835398613756172340965955 22253097920634258511448933)
              ·
                refine ⟨4172455860118923470896675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22253097920634258511448933 4172455860118923470896675)
                ·
                  refine ⟨6258683790178385206345013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172455860118923470896675 6258683790178385206345013)
                  ·
                    refine ⟨586751605329223613094845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6258683790178385206345013 586751605329223613094845)
                    ·
                      rfl

theorem cell23_3428084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_3428084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428084 prefixEnd_3428084 := by exact prefixLift 3428084
  have htrace : WordTrace (prefixWord ++ tailWord_3428084) baseStart_3428084 baseEnd_3428084 := by
    simpa [prefixWord, tailWord_3428084, baseEnd_3428084] using wordTrace_append hprefix tailTrace_3428084
  have hstable : (prefixWord ++ tailWord_3428084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428084).length < 2 ^ (prefixWord ++ tailWord_3428084).sum := by decide
  have hdescent : baseEnd_3428084 < baseStart_3428084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428087 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_3428087 : Nat := 118140960795 + 3428087 * 2 ^ 59
def prefixEnd_3428087 : Nat := 4983230072969 + 3 ^ 40 * 3428087 * 2
def baseEnd_3428087 : Nat := 1760256356429634327547021

theorem tailTrace_3428087 : CollatzResearch.WordTrace tailWord_3428087 prefixEnd_3428087 1760256356429634327547021 := by
  unfold tailWord_3428087
  simp only [CollatzResearch.WordTrace]
  refine ⟨125032604731633744493010515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83355069821089162995340343 125032604731633744493010515)
  ·
    refine ⟨187548907097450616739515773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125032604731633744493010515 187548907097450616739515773)
    ·
      refine ⟨70330840161543981277318415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187548907097450616739515773 70330840161543981277318415)
      ·
        refine ⟨105496260242315971915977623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70330840161543981277318415 105496260242315971915977623)
        ·
          refine ⟨158244390363473957873966435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105496260242315971915977623 158244390363473957873966435)
          ·
            refine ⟨237366585545210936810949653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158244390363473957873966435 237366585545210936810949653)
            ·
              refine ⟨11126558697431762663013265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237366585545210936810949653 11126558697431762663013265)
              ·
                refine ⟨8344919023073821997259949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126558697431762663013265 8344919023073821997259949)
                ·
                  refine ⟨3129344633652683248972481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8344919023073821997259949 3129344633652683248972481)
                  ·
                    refine ⟨2347008475239512436729361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3129344633652683248972481 2347008475239512436729361)
                    ·
                      refine ⟨1760256356429634327547021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347008475239512436729361 1760256356429634327547021)
                      ·
                        rfl

theorem cell23_3428087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_3428087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428087 prefixEnd_3428087 := by exact prefixLift 3428087
  have htrace : WordTrace (prefixWord ++ tailWord_3428087) baseStart_3428087 baseEnd_3428087 := by
    simpa [prefixWord, tailWord_3428087, baseEnd_3428087] using wordTrace_append hprefix tailTrace_3428087
  have hstable : (prefixWord ++ tailWord_3428087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428087).length < 2 ^ (prefixWord ++ tailWord_3428087).sum := by decide
  have hdescent : baseEnd_3428087 < baseStart_3428087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428143 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_3428143 : Nat := 118140960795 + 3428143 * 2 ^ 59
def prefixEnd_3428143 : Nat := 4983230072969 + 3 ^ 40 * 3428143 * 2
def baseEnd_3428143 : Nat := 1760285111346286108446763

theorem tailTrace_3428143 : CollatzResearch.WordTrace tailWord_3428143 prefixEnd_3428143 1760285111346286108446763 := by
  unfold tailWord_3428143
  simp only [CollatzResearch.WordTrace]
  refine ⟨125034647219430866057049083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83356431479620577371366055 125034647219430866057049083)
  ·
    refine ⟨187551970829146299085573625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125034647219430866057049083 187551970829146299085573625)
    ·
      refine ⟨140663978121859724314180219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187551970829146299085573625 140663978121859724314180219)
      ·
        refine ⟨210995967182789586471270329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140663978121859724314180219 210995967182789586471270329)
        ·
          refine ⟨158246975387092189853452747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210995967182789586471270329 158246975387092189853452747)
          ·
            refine ⟨237370463080638284780179121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158246975387092189853452747 237370463080638284780179121)
            ·
              refine ⟨178027847310478713585134341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237370463080638284780179121 178027847310478713585134341)
              ·
                refine ⟨33380221370714758797212689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178027847310478713585134341 33380221370714758797212689)
                ·
                  refine ⟨25035166028036069097909517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33380221370714758797212689 25035166028036069097909517)
                  ·
                    refine ⟨9388187260513525911716069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25035166028036069097909517 9388187260513525911716069)
                    ·
                      refine ⟨1760285111346286108446763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9388187260513525911716069 1760285111346286108446763)
                      ·
                        rfl

theorem cell23_3428143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_3428143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428143 prefixEnd_3428143 := by exact prefixLift 3428143
  have htrace : WordTrace (prefixWord ++ tailWord_3428143) baseStart_3428143 baseEnd_3428143 := by
    simpa [prefixWord, tailWord_3428143, baseEnd_3428143] using wordTrace_append hprefix tailTrace_3428143
  have hstable : (prefixWord ++ tailWord_3428143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428143).length < 2 ^ (prefixWord ++ tailWord_3428143).sum := by decide
  have hdescent : baseEnd_3428143 < baseStart_3428143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428194 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3428194 : Nat := 118140960795 + 3428194 * 2 ^ 59
def prefixEnd_3428194 : Nat := 4983230072969 + 3 ^ 40 * 3428194 * 2
def baseEnd_3428194 : Nat := 1760311298859665408909029

theorem tailTrace_3428194 : CollatzResearch.WordTrace tailWord_3428194 prefixEnd_3428194 1760311298859665408909029 := by
  unfold tailWord_3428194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259126835561525441788909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83357671561497401178103757 31259126835561525441788909)
  ·
    refine ⟨11722172563335572040670841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31259126835561525441788909 11722172563335572040670841)
    ·
      refine ⟨8791629422501679030503131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11722172563335572040670841 8791629422501679030503131)
      ·
        refine ⟨13187444133752518545754697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8791629422501679030503131 13187444133752518545754697)
        ·
          refine ⟨9890583100314388909316023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13187444133752518545754697 9890583100314388909316023)
          ·
            refine ⟨14835874650471583363974035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9890583100314388909316023 14835874650471583363974035)
            ·
              refine ⟨22253811975707375045961053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14835874650471583363974035 22253811975707375045961053)
              ·
                refine ⟨8345179490890265642235395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22253811975707375045961053 8345179490890265642235395)
                ·
                  refine ⟨12517769236335398463353093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8345179490890265642235395 12517769236335398463353093)
                  ·
                    refine ⟨2347081731812887211878705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12517769236335398463353093 2347081731812887211878705)
                    ·
                      refine ⟨1760311298859665408909029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347081731812887211878705 1760311298859665408909029)
                      ·
                        rfl

theorem cell23_3428194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3428194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428194 prefixEnd_3428194 := by exact prefixLift 3428194
  have htrace : WordTrace (prefixWord ++ tailWord_3428194) baseStart_3428194 baseEnd_3428194 := by
    simpa [prefixWord, tailWord_3428194, baseEnd_3428194] using wordTrace_append hprefix tailTrace_3428194
  have hstable : (prefixWord ++ tailWord_3428194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428194).length < 2 ^ (prefixWord ++ tailWord_3428194).sum := by decide
  have hdescent : baseEnd_3428194 < baseStart_3428194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428200 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 7]
def baseStart_3428200 : Nat := 118140960795 + 3428200 * 2 ^ 59
def prefixEnd_3428200 : Nat := 4983230072969 + 3 ^ 40 * 3428200 * 2
def baseEnd_3428200 : Nat := 195590486638176931714889

theorem tailTrace_3428200 : CollatzResearch.WordTrace tailWord_3428200 prefixEnd_3428200 195590486638176931714889 := by
  unfold tailWord_3428200
  simp only [CollatzResearch.WordTrace]
  refine ⟨62518363090112182395937027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83357817453482909861249369 62518363090112182395937027)
  ·
    refine ⟨93777544635168273593905541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62518363090112182395937027 93777544635168273593905541)
    ·
      refine ⟨17583289619094051298857289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93777544635168273593905541 17583289619094051298857289)
      ·
        refine ⟨13187467214320538474142967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17583289619094051298857289 13187467214320538474142967)
        ·
          refine ⟨19781200821480807711214451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187467214320538474142967 19781200821480807711214451)
          ·
            refine ⟨29671801232221211566821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19781200821480807711214451 29671801232221211566821677)
            ·
              refine ⟨11126925462082954337558129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29671801232221211566821677 11126925462082954337558129)
              ·
                refine ⟨8345194096562215753168597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126925462082954337558129 8345194096562215753168597)
                ·
                  refine ⟨195590486638176931714889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8345194096562215753168597 195590486638176931714889)
                  ·
                    rfl

theorem cell23_3428200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_3428200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428200 prefixEnd_3428200 := by exact prefixLift 3428200
  have htrace : WordTrace (prefixWord ++ tailWord_3428200) baseStart_3428200 baseEnd_3428200 := by
    simpa [prefixWord, tailWord_3428200, baseEnd_3428200] using wordTrace_append hprefix tailTrace_3428200
  have hstable : (prefixWord ++ tailWord_3428200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428200).length < 2 ^ (prefixWord ++ tailWord_3428200).sum := by decide
  have hdescent : baseEnd_3428200 < baseStart_3428200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428210 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3428210 : Nat := 118140960795 + 3428210 * 2 ^ 59
def prefixEnd_3428210 : Nat := 4983230072969 + 3 ^ 40 * 3428210 * 2
def baseEnd_3428210 : Nat := 1760319514550137346308955

theorem tailTrace_3428210 : CollatzResearch.WordTrace tailWord_3428210 prefixEnd_3428210 1760319514550137346308955 := by
  unfold tailWord_3428210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259272727547034124934521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83358060606792090999825389 31259272727547034124934521)
  ·
    refine ⟨23444454545660275593700891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31259272727547034124934521 23444454545660275593700891)
    ·
      refine ⟨35166681818490413390551337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23444454545660275593700891 35166681818490413390551337)
      ·
        refine ⟨26375011363867810042913503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35166681818490413390551337 26375011363867810042913503)
        ·
          refine ⟨39562517045801715064370255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26375011363867810042913503 39562517045801715064370255)
          ·
            refine ⟨59343775568702572596555383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39562517045801715064370255 59343775568702572596555383)
            ·
              refine ⟨89015663353053858894833075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59343775568702572596555383 89015663353053858894833075)
              ·
                refine ⟨133523495029580788342249613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89015663353053858894833075 133523495029580788342249613)
                ·
                  refine ⟨50071310636092795628343605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133523495029580788342249613 50071310636092795628343605)
                  ·
                    refine ⟨4694185372133699590157213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50071310636092795628343605 4694185372133699590157213)
                    ·
                      refine ⟨1760319514550137346308955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4694185372133699590157213 1760319514550137346308955)
                      ·
                        rfl

theorem cell23_3428210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3428210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428210 prefixEnd_3428210 := by exact prefixLift 3428210
  have htrace : WordTrace (prefixWord ++ tailWord_3428210) baseStart_3428210 baseEnd_3428210 := by
    simpa [prefixWord, tailWord_3428210, baseEnd_3428210] using wordTrace_append hprefix tailTrace_3428210
  have hstable : (prefixWord ++ tailWord_3428210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428210).length < 2 ^ (prefixWord ++ tailWord_3428210).sum := by decide
  have hdescent : baseEnd_3428210 < baseStart_3428210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428217 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 5]
def baseStart_3428217 : Nat := 118140960795 + 3428217 * 2 ^ 59
def prefixEnd_3428217 : Nat := 4983230072969 + 3 ^ 40 * 3428217 * 2
def baseEnd_3428217 : Nat := 195591456546079868769047

theorem tailTrace_3428217 : CollatzResearch.WordTrace tailWord_3428217 prefixEnd_3428217 195591456546079868769047 := by
  unfold tailWord_3428217
  simp only [CollatzResearch.WordTrace]
  refine ⟨125037346221162776695242905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83358230814108517796828603 125037346221162776695242905)
  ·
    refine ⟨93778009665872082521432179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125037346221162776695242905 93778009665872082521432179)
    ·
      refine ⟨140667014498808123782148269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93778009665872082521432179 140667014498808123782148269)
      ·
        refine ⟨52750130437053046418305601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140667014498808123782148269 52750130437053046418305601)
        ·
          refine ⟨39562597827789784813729201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52750130437053046418305601 39562597827789784813729201)
          ·
            refine ⟨29671948370842338610296901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39562597827789784813729201 29671948370842338610296901)
            ·
              refine ⟨5563490319532938489430669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29671948370842338610296901 5563490319532938489430669)
              ·
                refine ⟨2086308869824851933536501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5563490319532938489430669 2086308869824851933536501)
                ·
                  refine ⟨195591456546079868769047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2086308869824851933536501 195591456546079868769047)
                  ·
                    rfl

theorem cell23_3428217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 5].length) (baseStart_3428217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428217 prefixEnd_3428217 := by exact prefixLift 3428217
  have htrace : WordTrace (prefixWord ++ tailWord_3428217) baseStart_3428217 baseEnd_3428217 := by
    simpa [prefixWord, tailWord_3428217, baseEnd_3428217] using wordTrace_append hprefix tailTrace_3428217
  have hstable : (prefixWord ++ tailWord_3428217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428217).length < 2 ^ (prefixWord ++ tailWord_3428217).sum := by decide
  have hdescent : baseEnd_3428217 < baseStart_3428217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428287 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_3428287 : Nat := 118140960795 + 3428287 * 2 ^ 59
def prefixEnd_3428287 : Nat := 4983230072969 + 3 ^ 40 * 3428287 * 2
def baseEnd_3428287 : Nat := 1760359052560533545046101

theorem tailTrace_3428287 : CollatzResearch.WordTrace tailWord_3428287 prefixEnd_3428287 1760359052560533545046101 := by
  unfold tailWord_3428287
  simp only [CollatzResearch.WordTrace]
  refine ⟨125039899330909178650291115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83359932887272785766860743 125039899330909178650291115)
  ·
    refine ⟨187559848996363767975436673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125039899330909178650291115 187559848996363767975436673)
    ·
      refine ⟨140669886747272825981577505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187559848996363767975436673 140669886747272825981577505)
      ·
        refine ⟨105502415060454619486183129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140669886747272825981577505 105502415060454619486183129)
        ·
          refine ⟨79126811295340964614637347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105502415060454619486183129 79126811295340964614637347)
          ·
            refine ⟨118690216943011446921956021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79126811295340964614637347 118690216943011446921956021)
            ·
              refine ⟨11127207838407323148933377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118690216943011446921956021 11127207838407323148933377)
              ·
                refine ⟨8345405878805492361700033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11127207838407323148933377 8345405878805492361700033)
                ·
                  refine ⟨6259054409104119271275025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345405878805492361700033 6259054409104119271275025)
                  ·
                    refine ⟨4694290806828089453456269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6259054409104119271275025 4694290806828089453456269)
                    ·
                      refine ⟨1760359052560533545046101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4694290806828089453456269 1760359052560533545046101)
                      ·
                        rfl

theorem cell23_3428287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_3428287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428287 prefixEnd_3428287 := by exact prefixLift 3428287
  have htrace : WordTrace (prefixWord ++ tailWord_3428287) baseStart_3428287 baseEnd_3428287 := by
    simpa [prefixWord, tailWord_3428287, baseEnd_3428287] using wordTrace_append hprefix tailTrace_3428287
  have hstable : (prefixWord ++ tailWord_3428287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428287).length < 2 ^ (prefixWord ++ tailWord_3428287).sum := by decide
  have hdescent : baseEnd_3428287 < baseStart_3428287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428344 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_3428344 : Nat := 118140960795 + 3428344 * 2 ^ 59
def prefixEnd_3428344 : Nat := 4983230072969 + 3 ^ 40 * 3428344 * 2
def baseEnd_3428344 : Nat := 1760388320957839822033339

theorem tailTrace_3428344 : CollatzResearch.WordTrace tailWord_3428344 prefixEnd_3428344 1760388320957839822033339 := by
  unfold tailWord_3428344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62520989145851338692558043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83361318861135118256744057 62520989145851338692558043)
  ·
    refine ⟨93781483718777008038837065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62520989145851338692558043 93781483718777008038837065)
    ·
      refine ⟨70336112789082756029127799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93781483718777008038837065 70336112789082756029127799)
      ·
        refine ⟨105504169183624134043691699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70336112789082756029127799 105504169183624134043691699)
        ·
          refine ⟨158256253775436201065537549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105504169183624134043691699 158256253775436201065537549)
          ·
            refine ⟨59346095165788575399576581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158256253775436201065537549 59346095165788575399576581)
            ·
              refine ⟨11127392843585357887420609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59346095165788575399576581 11127392843585357887420609)
              ·
                refine ⟨8345544632689018415565457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11127392843585357887420609 8345544632689018415565457)
                ·
                  refine ⟨6259158474516763811674093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345544632689018415565457 6259158474516763811674093)
                  ·
                    refine ⟨2347184427943786429377785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6259158474516763811674093 2347184427943786429377785)
                    ·
                      refine ⟨1760388320957839822033339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347184427943786429377785 1760388320957839822033339)
                      ·
                        rfl

theorem cell23_3428344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_3428344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428344 prefixEnd_3428344 := by exact prefixLift 3428344
  have htrace : WordTrace (prefixWord ++ tailWord_3428344) baseStart_3428344 baseEnd_3428344 := by
    simpa [prefixWord, tailWord_3428344, baseEnd_3428344] using wordTrace_append hprefix tailTrace_3428344
  have hstable : (prefixWord ++ tailWord_3428344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428344).length < 2 ^ (prefixWord ++ tailWord_3428344).sum := by decide
  have hdescent : baseEnd_3428344 < baseStart_3428344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428357 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_3428357 : Nat := 118140960795 + 3428357 * 2 ^ 59
def prefixEnd_3428357 : Nat := 4983230072969 + 3 ^ 40 * 3428357 * 2
def baseEnd_3428357 : Nat := 1760394996206348271170779

theorem tailTrace_3428357 : CollatzResearch.WordTrace tailWord_3428357 prefixEnd_3428357 1760394996206348271170779 := by
  unfold tailWord_3428357
  simp only [CollatzResearch.WordTrace]
  refine ⟨125042452440655580605339325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83361634960437053736892883 125042452440655580605339325)
  ·
    refine ⟨46890919665245842727002247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125042452440655580605339325 46890919665245842727002247)
    ·
      refine ⟨70336379497868764090503371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46890919665245842727002247 70336379497868764090503371)
      ·
        refine ⟨105504569246803146135755057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70336379497868764090503371 105504569246803146135755057)
        ·
          refine ⟨79128426935102359601816293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105504569246803146135755057 79128426935102359601816293)
          ·
            refine ⟨14836580050331692425340555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79128426935102359601816293 14836580050331692425340555)
            ·
              refine ⟨22254870075497538638010833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14836580050331692425340555 22254870075497538638010833)
              ·
                refine ⟨16691152556623153978508125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22254870075497538638010833 16691152556623153978508125)
                ·
                  refine ⟨6259182208733682741940547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16691152556623153978508125 6259182208733682741940547)
                  ·
                    refine ⟨9388773313100524112910821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6259182208733682741940547 9388773313100524112910821)
                    ·
                      refine ⟨1760394996206348271170779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9388773313100524112910821 1760394996206348271170779)
                      ·
                        rfl

theorem cell23_3428357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_3428357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428357 prefixEnd_3428357 := by exact prefixLift 3428357
  have htrace : WordTrace (prefixWord ++ tailWord_3428357) baseStart_3428357 baseEnd_3428357 := by
    simpa [prefixWord, tailWord_3428357, baseEnd_3428357] using wordTrace_append hprefix tailTrace_3428357
  have hstable : (prefixWord ++ tailWord_3428357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428357).length < 2 ^ (prefixWord ++ tailWord_3428357).sum := by decide
  have hdescent : baseEnd_3428357 < baseStart_3428357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428387 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4]
def baseStart_3428387 : Nat := 118140960795 + 3428387 * 2 ^ 59
def prefixEnd_3428387 : Nat := 4983230072969 + 3 ^ 40 * 3428387 * 2
def baseEnd_3428387 : Nat := 1760410400625983153795641

theorem tailTrace_3428387 : CollatzResearch.WordTrace tailWord_3428387 prefixEnd_3428387 1760410400625983153795641 := by
  unfold tailWord_3428387
  simp only [CollatzResearch.WordTrace]
  refine ⟨125043546630546895728931415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83362364420364597152620943 125043546630546895728931415)
  ·
    refine ⟨187565319945820343593397123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125043546630546895728931415 187565319945820343593397123)
    ·
      refine ⟨281347979918730515390095685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187565319945820343593397123 281347979918730515390095685)
      ·
        refine ⟨52752746234761971635642941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 281347979918730515390095685 52752746234761971635642941)
        ·
          refine ⟨19782279838035739363366103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52752746234761971635642941 19782279838035739363366103)
          ·
            refine ⟨29673419757053609045049155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782279838035739363366103 29673419757053609045049155)
            ·
              refine ⟨44510129635580413567573733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29673419757053609045049155 44510129635580413567573733)
              ·
                refine ⟨8345649306671327543920075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44510129635580413567573733 8345649306671327543920075)
                ·
                  refine ⟨12518473960006991315880113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8345649306671327543920075 12518473960006991315880113)
                  ·
                    refine ⟨9388855470005243486910085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12518473960006991315880113 9388855470005243486910085)
                    ·
                      refine ⟨1760410400625983153795641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9388855470005243486910085 1760410400625983153795641)
                      ·
                        rfl

theorem cell23_3428387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_3428387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428387 prefixEnd_3428387 := by exact prefixLift 3428387
  have htrace : WordTrace (prefixWord ++ tailWord_3428387) baseStart_3428387 baseEnd_3428387 := by
    simpa [prefixWord, tailWord_3428387, baseEnd_3428387] using wordTrace_append hprefix tailTrace_3428387
  have hstable : (prefixWord ++ tailWord_3428387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428387).length < 2 ^ (prefixWord ++ tailWord_3428387).sum := by decide
  have hdescent : baseEnd_3428387 < baseStart_3428387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428388 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_3428388 : Nat := 118140960795 + 3428388 * 2 ^ 59
def prefixEnd_3428388 : Nat := 4983230072969 + 3 ^ 40 * 3428388 * 2
def baseEnd_3428388 : Nat := 586803638035545883294379

theorem tailTrace_3428388 : CollatzResearch.WordTrace tailWord_3428388 prefixEnd_3428388 586803638035545883294379 := by
  unfold tailWord_3428388
  simp only [CollatzResearch.WordTrace]
  refine ⟨62521791551771636449858909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83362388735695515266478545 62521791551771636449858909)
  ·
    refine ⟨23445671831914363668697091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62521791551771636449858909 23445671831914363668697091)
    ·
      refine ⟨35168507747871545503045637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23445671831914363668697091 35168507747871545503045637)
      ·
        refine ⟨6594095202725914781821057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35168507747871545503045637 6594095202725914781821057)
        ·
          refine ⟨4945571402044436086365793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594095202725914781821057 4945571402044436086365793)
          ·
            refine ⟨3709178551533327064774345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945571402044436086365793 3709178551533327064774345)
            ·
              refine ⟨2781883913649995298580759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709178551533327064774345 2781883913649995298580759)
              ·
                refine ⟨4172825870474992947871139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781883913649995298580759 4172825870474992947871139)
                ·
                  refine ⟨6259238805712489421806709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172825870474992947871139 6259238805712489421806709)
                  ·
                    refine ⟨586803638035545883294379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6259238805712489421806709 586803638035545883294379)
                    ·
                      rfl

theorem cell23_3428388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_3428388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428388 prefixEnd_3428388 := by exact prefixLift 3428388
  have htrace : WordTrace (prefixWord ++ tailWord_3428388) baseStart_3428388 baseEnd_3428388 := by
    simpa [prefixWord, tailWord_3428388, baseEnd_3428388] using wordTrace_append hprefix tailTrace_3428388
  have hstable : (prefixWord ++ tailWord_3428388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428388).length < 2 ^ (prefixWord ++ tailWord_3428388).sum := by decide
  have hdescent : baseEnd_3428388 < baseStart_3428388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428401 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_3428401 : Nat := 118140960795 + 3428401 * 2 ^ 59
def prefixEnd_3428401 : Nat := 4983230072969 + 3 ^ 40 * 3428401 * 2
def baseEnd_3428401 : Nat := 586805863118382033006859

theorem tailTrace_3428401 : CollatzResearch.WordTrace tailWord_3428401 prefixEnd_3428401 586805863118382033006859 := by
  unfold tailWord_3428401
  simp only [CollatzResearch.WordTrace]
  refine ⟨125044057252496176119941057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83362704834997450746627371 125044057252496176119941057)
  ·
    refine ⟨93783042939372132089955793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125044057252496176119941057 93783042939372132089955793)
    ·
      refine ⟨70337282204529099067466845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93783042939372132089955793 70337282204529099067466845)
      ·
        refine ⟨26376480826698412150300067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70337282204529099067466845 26376480826698412150300067)
        ·
          refine ⟨39564721240047618225450101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26376480826698412150300067 39564721240047618225450101)
          ·
            refine ⟨3709192616254464208635947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39564721240047618225450101 3709192616254464208635947)
            ·
              refine ⟨5563788924381696312953921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709192616254464208635947 5563788924381696312953921)
              ·
                refine ⟨4172841693286272234715441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5563788924381696312953921 4172841693286272234715441)
                ·
                  refine ⟨3129631269964704176036581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172841693286272234715441 3129631269964704176036581)
                  ·
                    refine ⟨586805863118382033006859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129631269964704176036581 586805863118382033006859)
                    ·
                      rfl

theorem cell23_3428401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_3428401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428401 prefixEnd_3428401 := by exact prefixLift 3428401
  have htrace : WordTrace (prefixWord ++ tailWord_3428401) baseStart_3428401 baseEnd_3428401 := by
    simpa [prefixWord, tailWord_3428401, baseEnd_3428401] using wordTrace_append hprefix tailTrace_3428401
  have hstable : (prefixWord ++ tailWord_3428401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428401).length < 2 ^ (prefixWord ++ tailWord_3428401).sum := by decide
  have hdescent : baseEnd_3428401 < baseStart_3428401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428407 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_3428407 : Nat := 118140960795 + 3428407 * 2 ^ 59
def prefixEnd_3428407 : Nat := 4983230072969 + 3 ^ 40 * 3428407 * 2
def baseEnd_3428407 : Nat := 1760420670239073075545549

theorem tailTrace_3428407 : CollatzResearch.WordTrace tailWord_3428407 prefixEnd_3428407 1760420670239073075545549 := by
  unfold tailWord_3428407
  simp only [CollatzResearch.WordTrace]
  refine ⟨125044276090474439144659475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83362850726982959429772983 125044276090474439144659475)
  ·
    refine ⟨187566414135711658716989213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125044276090474439144659475 187566414135711658716989213)
    ·
      refine ⟨70337405300891872018870955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187566414135711658716989213 70337405300891872018870955)
      ·
        refine ⟨105506107951337808028306433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70337405300891872018870955 105506107951337808028306433)
        ·
          refine ⟨79129580963503356021229825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105506107951337808028306433 79129580963503356021229825)
          ·
            refine ⟨59347185722627517015922369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79129580963503356021229825 59347185722627517015922369)
            ·
              refine ⟨44510389291970637761941777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59347185722627517015922369 44510389291970637761941777)
              ·
                refine ⟨33382791968977978321456333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44510389291970637761941777 33382791968977978321456333)
                ·
                  refine ⟨12518546988366741870546125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33382791968977978321456333 12518546988366741870546125)
                  ·
                    refine ⟨4694455120637528201454797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12518546988366741870546125 4694455120637528201454797)
                    ·
                      refine ⟨1760420670239073075545549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4694455120637528201454797 1760420670239073075545549)
                      ·
                        rfl

theorem cell23_3428407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_3428407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428407 prefixEnd_3428407 := by exact prefixLift 3428407
  have htrace : WordTrace (prefixWord ++ tailWord_3428407) baseStart_3428407 baseEnd_3428407 := by
    simpa [prefixWord, tailWord_3428407, baseEnd_3428407] using wordTrace_append hprefix tailTrace_3428407
  have hstable : (prefixWord ++ tailWord_3428407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428407).length < 2 ^ (prefixWord ++ tailWord_3428407).sum := by decide
  have hdescent : baseEnd_3428407 < baseStart_3428407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428408 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_3428408 : Nat := 118140960795 + 3428408 * 2 ^ 59
def prefixEnd_3428408 : Nat := 4983230072969 + 3 ^ 40 * 3428408 * 2
def baseEnd_3428408 : Nat := 1760421183719727571633045

theorem tailTrace_3428408 : CollatzResearch.WordTrace tailWord_3428408 prefixEnd_3428408 1760421183719727571633045 := by
  unfold tailWord_3428408
  simp only [CollatzResearch.WordTrace]
  refine ⟨62522156281735408157722939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83362875042313877543630585 62522156281735408157722939)
  ·
    refine ⟨93783234422603112236584409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62522156281735408157722939 93783234422603112236584409)
    ·
      refine ⟨70337425816952334177438307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93783234422603112236584409 70337425816952334177438307)
      ·
        refine ⟨105506138725428501266157461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70337425816952334177438307 105506138725428501266157461)
        ·
          refine ⟨4945600252754460996851131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105506138725428501266157461 4945600252754460996851131)
          ·
            refine ⟨7418400379131691495276697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945600252754460996851131 7418400379131691495276697)
            ·
              refine ⟨5563800284348768621457523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418400379131691495276697 5563800284348768621457523)
              ·
                refine ⟨8345700426523152932186285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563800284348768621457523 8345700426523152932186285)
                ·
                  refine ⟨3129637659946182349569857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8345700426523152932186285 3129637659946182349569857)
                  ·
                    refine ⟨2347228244959636762177393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3129637659946182349569857 2347228244959636762177393)
                    ·
                      refine ⟨1760421183719727571633045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347228244959636762177393 1760421183719727571633045)
                      ·
                        rfl

theorem cell23_3428408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_3428408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428408 prefixEnd_3428408 := by exact prefixLift 3428408
  have htrace : WordTrace (prefixWord ++ tailWord_3428408) baseStart_3428408 baseEnd_3428408 := by
    simpa [prefixWord, tailWord_3428408, baseEnd_3428408] using wordTrace_append hprefix tailTrace_3428408
  have hstable : (prefixWord ++ tailWord_3428408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428408).length < 2 ^ (prefixWord ++ tailWord_3428408).sum := by decide
  have hdescent : baseEnd_3428408 < baseStart_3428408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428437 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3428437 : Nat := 118140960795 + 3428437 * 2 ^ 59
def prefixEnd_3428437 : Nat := 4983230072969 + 3 ^ 40 * 3428437 * 2
def baseEnd_3428437 : Nat := 1760436074658707958170411

theorem tailTrace_3428437 : CollatzResearch.WordTrace tailWord_3428437 prefixEnd_3428437 1760436074658707958170411 := by
  unfold tailWord_3428437
  simp only [CollatzResearch.WordTrace]
  refine ⟨125045370280365754268251565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83363580186910502845501043 125045370280365754268251565)
  ·
    refine ⟨46892013855137157850594337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125045370280365754268251565 46892013855137157850594337)
    ·
      refine ⟨35169010391352868387945753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46892013855137157850594337 35169010391352868387945753)
      ·
        refine ⟨26376757793514651290959315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35169010391352868387945753 26376757793514651290959315)
        ·
          refine ⟨39565136690271976936438973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26376757793514651290959315 39565136690271976936438973)
          ·
            refine ⟨14836926258851991351164615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39565136690271976936438973 14836926258851991351164615)
            ·
              refine ⟨22255389388277987026746923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14836926258851991351164615 22255389388277987026746923)
              ·
                refine ⟨33383084082416980540120385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22255389388277987026746923 33383084082416980540120385)
                ·
                  refine ⟨25037313061812735405090289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33383084082416980540120385 25037313061812735405090289)
                  ·
                    refine ⟨18777984796359551553817717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25037313061812735405090289 18777984796359551553817717)
                    ·
                      refine ⟨1760436074658707958170411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18777984796359551553817717 1760436074658707958170411)
                      ·
                        rfl

theorem cell23_3428437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3428437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428437 prefixEnd_3428437 := by exact prefixLift 3428437
  have htrace : WordTrace (prefixWord ++ tailWord_3428437) baseStart_3428437 baseEnd_3428437 := by
    simpa [prefixWord, tailWord_3428437, baseEnd_3428437] using wordTrace_append hprefix tailTrace_3428437
  have hstable : (prefixWord ++ tailWord_3428437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428437).length < 2 ^ (prefixWord ++ tailWord_3428437).sum := by decide
  have hdescent : baseEnd_3428437 < baseStart_3428437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428451 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 1, 3, 2]
def baseStart_3428451 : Nat := 118140960795 + 3428451 * 2 ^ 59
def prefixEnd_3428451 : Nat := 4983230072969 + 3 ^ 40 * 3428451 * 2
def baseEnd_3428451 : Nat := 1760443263387870903395347

theorem tailTrace_3428451 : CollatzResearch.WordTrace tailWord_3428451 prefixEnd_3428451 1760443263387870903395347 := by
  unfold tailWord_3428451
  simp only [CollatzResearch.WordTrace]
  refine ⟨125045880902315034659261207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83363920601543356439507471 125045880902315034659261207)
  ·
    refine ⟨187568821353472551988891811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125045880902315034659261207 187568821353472551988891811)
    ·
      refine ⟨281353232030208827983337717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187568821353472551988891811 281353232030208827983337717)
      ·
        refine ⟨26376865502832077623437911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281353232030208827983337717 26376865502832077623437911)
        ·
          refine ⟨39565298254248116435156867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26376865502832077623437911 39565298254248116435156867)
          ·
            refine ⟨59347947381372174652735301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39565298254248116435156867 59347947381372174652735301)
            ·
              refine ⟨11127740134007282747387869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59347947381372174652735301 11127740134007282747387869)
              ·
                refine ⟨4172902550252731030270451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11127740134007282747387869 4172902550252731030270451)
                ·
                  refine ⟨6259353825379096545405677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172902550252731030270451 6259353825379096545405677)
                  ·
                    refine ⟨2347257684517161204527129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6259353825379096545405677 2347257684517161204527129)
                    ·
                      refine ⟨1760443263387870903395347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347257684517161204527129 1760443263387870903395347)
                      ·
                        rfl

theorem cell23_3428451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_3428451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428451 prefixEnd_3428451 := by exact prefixLift 3428451
  have htrace : WordTrace (prefixWord ++ tailWord_3428451) baseStart_3428451 baseEnd_3428451 := by
    simpa [prefixWord, tailWord_3428451, baseEnd_3428451] using wordTrace_append hprefix tailTrace_3428451
  have hstable : (prefixWord ++ tailWord_3428451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428451).length < 2 ^ (prefixWord ++ tailWord_3428451).sum := by decide
  have hdescent : baseEnd_3428451 < baseStart_3428451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428487 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 7]
def baseStart_3428487 : Nat := 118140960795 + 3428487 * 2 ^ 59
def prefixEnd_3428487 : Nat := 4983230072969 + 3 ^ 40 * 3428487 * 2
def baseEnd_3428487 : Nat := 195606860965714751393909

theorem tailTrace_3428487 : CollatzResearch.WordTrace tailWord_3428487 prefixEnd_3428487 195606860965714751393909 := by
  unfold tailWord_3428487
  simp only [CollatzResearch.WordTrace]
  refine ⟨125047193930184612807571715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83364795953456408538381143 125047193930184612807571715)
  ·
    refine ⟨187570790895276919211357573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125047193930184612807571715 187570790895276919211357573)
    ·
      refine ⟨35169523292864422352129545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187570790895276919211357573 35169523292864422352129545)
      ·
        refine ⟨26377142469648316764097159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35169523292864422352129545 26377142469648316764097159)
        ·
          refine ⟨39565713704472475146145739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26377142469648316764097159 39565713704472475146145739)
          ·
            refine ⟨59348570556708712719218609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39565713704472475146145739 59348570556708712719218609)
            ·
              refine ⟨44511427917531534539413957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59348570556708712719218609 44511427917531534539413957)
              ·
                refine ⟨8345892734537162726140117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44511427917531534539413957 8345892734537162726140117)
                ·
                  refine ⟨195606860965714751393909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8345892734537162726140117 195606860965714751393909)
                  ·
                    rfl

theorem cell23_3428487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 7].length) (baseStart_3428487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428487 prefixEnd_3428487 := by exact prefixLift 3428487
  have htrace : WordTrace (prefixWord ++ tailWord_3428487) baseStart_3428487 baseEnd_3428487 := by
    simpa [prefixWord, tailWord_3428487, baseEnd_3428487] using wordTrace_append hprefix tailTrace_3428487
  have hstable : (prefixWord ++ tailWord_3428487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428487).length < 2 ^ (prefixWord ++ tailWord_3428487).sum := by decide
  have hdescent : baseEnd_3428487 < baseStart_3428487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428554 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3428554 : Nat := 118140960795 + 3428554 * 2 ^ 59
def prefixEnd_3428554 : Nat := 4983230072969 + 3 ^ 40 * 3428554 * 2
def baseEnd_3428554 : Nat := 1760496151895284000407373

theorem tailTrace_3428554 : CollatzResearch.WordTrace tailWord_3428554 prefixEnd_3428554 1760496151895284000407373 := by
  unfold tailWord_3428554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31262409405235470812565179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83366425080627922166840477 31262409405235470812565179)
  ·
    refine ⟨46893614107853206218847769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31262409405235470812565179 46893614107853206218847769)
    ·
      refine ⟨35170210580889904664135827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46893614107853206218847769 35170210580889904664135827)
      ·
        refine ⟨52755315871334856996203741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35170210580889904664135827 52755315871334856996203741)
        ·
          refine ⟨19783243451750571373576403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52755315871334856996203741 19783243451750571373576403)
          ·
            refine ⟨29674865177625857060364605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19783243451750571373576403 29674865177625857060364605)
            ·
              refine ⟨11128074441609696397636727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29674865177625857060364605 11128074441609696397636727)
              ·
                refine ⟨16692111662414544596455091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11128074441609696397636727 16692111662414544596455091)
                ·
                  refine ⟨25038167493621816894682637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16692111662414544596455091 25038167493621816894682637)
                  ·
                    refine ⟨9389312810108181335505989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25038167493621816894682637 9389312810108181335505989)
                    ·
                      refine ⟨1760496151895284000407373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9389312810108181335505989 1760496151895284000407373)
                      ·
                        rfl

theorem cell23_3428554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3428554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428554 prefixEnd_3428554 := by exact prefixLift 3428554
  have htrace : WordTrace (prefixWord ++ tailWord_3428554) baseStart_3428554 baseEnd_3428554 := by
    simpa [prefixWord, tailWord_3428554, baseEnd_3428554] using wordTrace_append hprefix tailTrace_3428554
  have hstable : (prefixWord ++ tailWord_3428554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428554).length < 2 ^ (prefixWord ++ tailWord_3428554).sum := by decide
  have hdescent : baseEnd_3428554 < baseStart_3428554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428581 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_3428581 : Nat := 118140960795 + 3428581 * 2 ^ 59
def prefixEnd_3428581 : Nat := 4983230072969 + 3 ^ 40 * 3428581 * 2
def baseEnd_3428581 : Nat := 586836671957651798256583

theorem tailTrace_3428581 : CollatzResearch.WordTrace tailWord_3428581 prefixEnd_3428581 586836671957651798256583 := by
  unfold tailWord_3428581
  simp only [CollatzResearch.WordTrace]
  refine ⟨125050622391844066861493597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83367081594562711240995731 125050622391844066861493597)
  ·
    refine ⟨46893983396941525073060099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125050622391844066861493597 46893983396941525073060099)
    ·
      refine ⟨70340975095412287609590149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46893983396941525073060099 70340975095412287609590149)
      ·
        refine ⟨13188932830389803926798153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70340975095412287609590149 13188932830389803926798153)
        ·
          refine ⟨9891699622792352945098615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13188932830389803926798153 9891699622792352945098615)
          ·
            refine ⟨14837549434188529417647923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9891699622792352945098615 14837549434188529417647923)
            ·
              refine ⟨22256324151282794126471885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14837549434188529417647923 22256324151282794126471885)
              ·
                refine ⟨8346121556731047797426957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22256324151282794126471885 8346121556731047797426957)
                ·
                  refine ⟨3129795583774142924035109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8346121556731047797426957 3129795583774142924035109)
                  ·
                    refine ⟨586836671957651798256583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129795583774142924035109 586836671957651798256583)
                    ·
                      rfl

theorem cell23_3428581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_3428581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428581 prefixEnd_3428581 := by exact prefixLift 3428581
  have htrace : WordTrace (prefixWord ++ tailWord_3428581) baseStart_3428581 baseEnd_3428581 := by
    simpa [prefixWord, tailWord_3428581, baseEnd_3428581] using wordTrace_append hprefix tailTrace_3428581
  have hstable : (prefixWord ++ tailWord_3428581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428581).length < 2 ^ (prefixWord ++ tailWord_3428581).sum := by decide
  have hdescent : baseEnd_3428581 < baseStart_3428581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428645 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 6]
def baseStart_3428645 : Nat := 118140960795 + 3428645 * 2 ^ 59
def prefixEnd_3428645 : Nat := 4983230072969 + 3 ^ 40 * 3428645 * 2
def baseEnd_3428645 : Nat := 195615875403871460485495

theorem tailTrace_3428645 : CollatzResearch.WordTrace tailWord_3428645 prefixEnd_3428645 195615875403871460485495 := by
  unfold tailWord_3428645
  simp only [CollatzResearch.WordTrace]
  refine ⟨125052956663612205791823389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83368637775741470527882259 125052956663612205791823389)
  ·
    refine ⟨46894858748854577171933771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125052956663612205791823389 46894858748854577171933771)
    ·
      refine ⟨70342288123281865757900657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46894858748854577171933771 70342288123281865757900657)
      ·
        refine ⟨52756716092461399318425493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70342288123281865757900657 52756716092461399318425493)
        ·
          refine ⟨2472971066834128093051195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52756716092461399318425493 2472971066834128093051195)
          ·
            refine ⟨3709456600251192139576793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472971066834128093051195 3709456600251192139576793)
            ·
              refine ⟨2782092450188394104682595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709456600251192139576793 2782092450188394104682595)
              ·
                refine ⟨4173138675282591157023893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782092450188394104682595 4173138675282591157023893)
                ·
                  refine ⟨195615875403871460485495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4173138675282591157023893 195615875403871460485495)
                  ·
                    rfl

theorem cell23_3428645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_3428645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428645 prefixEnd_3428645 := by exact prefixLift 3428645
  have htrace : WordTrace (prefixWord ++ tailWord_3428645) baseStart_3428645 baseEnd_3428645 := by
    simpa [prefixWord, tailWord_3428645, baseEnd_3428645] using wordTrace_append hprefix tailTrace_3428645
  have hstable : (prefixWord ++ tailWord_3428645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428645).length < 2 ^ (prefixWord ++ tailWord_3428645).sum := by decide
  have hdescent : baseEnd_3428645 < baseStart_3428645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428661 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3428661 : Nat := 118140960795 + 3428661 * 2 ^ 59
def prefixEnd_3428661 : Nat := 4983230072969 + 3 ^ 40 * 3428661 * 2
def baseEnd_3428661 : Nat := 1760551094325315081769381

theorem tailTrace_3428661 : CollatzResearch.WordTrace tailWord_3428661 prefixEnd_3428661 1760551094325315081769381 := by
  unfold tailWord_3428661
  simp only [CollatzResearch.WordTrace]
  refine ⟨125053540231554240524405837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83369026821036160349603891 125053540231554240524405837)
  ·
    refine ⟨46895077586832840196652189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125053540231554240524405837 46895077586832840196652189)
    ·
      refine ⟨17585654095062315073744571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46895077586832840196652189 17585654095062315073744571)
      ·
        refine ⟨26378481142593472610616857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17585654095062315073744571 26378481142593472610616857)
        ·
          refine ⟨19783860856945104457962643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26378481142593472610616857 19783860856945104457962643)
          ·
            refine ⟨29675791285417656686943965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19783860856945104457962643 29675791285417656686943965)
            ·
              refine ⟨11128421732031621257603987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29675791285417656686943965 11128421732031621257603987)
              ·
                refine ⟨16692632598047431886405981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11128421732031621257603987 16692632598047431886405981)
                ·
                  refine ⟨6259737224267786957402243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16692632598047431886405981 6259737224267786957402243)
                  ·
                    refine ⟨9389605836401680436103365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6259737224267786957402243 9389605836401680436103365)
                    ·
                      refine ⟨1760551094325315081769381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9389605836401680436103365 1760551094325315081769381)
                      ·
                        rfl

theorem cell23_3428661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3428661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428661 prefixEnd_3428661 := by exact prefixLift 3428661
  have htrace : WordTrace (prefixWord ++ tailWord_3428661) baseStart_3428661 baseEnd_3428661 := by
    simpa [prefixWord, tailWord_3428661, baseEnd_3428661] using wordTrace_append hprefix tailTrace_3428661
  have hstable : (prefixWord ++ tailWord_3428661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428661).length < 2 ^ (prefixWord ++ tailWord_3428661).sum := by decide
  have hdescent : baseEnd_3428661 < baseStart_3428661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428664 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_3428664 : Nat := 118140960795 + 3428664 * 2 ^ 59
def prefixEnd_3428664 : Nat := 4983230072969 + 3 ^ 40 * 3428664 * 2
def baseEnd_3428664 : Nat := 1760552634767278570031867

theorem tailTrace_3428664 : CollatzResearch.WordTrace tailWord_3428664 prefixEnd_3428664 1760552634767278570031867 := by
  unfold tailWord_3428664
  simp only [CollatzResearch.WordTrace]
  refine ⟨62526824825271686018382523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83369099767028914691176697 62526824825271686018382523)
  ·
    refine ⟨93790237237907529027573785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62526824825271686018382523 93790237237907529027573785)
    ·
      refine ⟨70342677928430646770680339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93790237237907529027573785 70342677928430646770680339)
      ·
        refine ⟨105514016892645970156020509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70342677928430646770680339 105514016892645970156020509)
        ·
          refine ⟨39567756334742238808507691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105514016892645970156020509 39567756334742238808507691)
          ·
            refine ⟨59351634502113358212761537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39567756334742238808507691 59351634502113358212761537)
            ·
              refine ⟨44513725876585018659571153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59351634502113358212761537 44513725876585018659571153)
              ·
                refine ⟨33385294407438763994678365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44513725876585018659571153 33385294407438763994678365)
                ·
                  refine ⟨12519485402789536498004387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33385294407438763994678365 12519485402789536498004387)
                  ·
                    refine ⟨18779228104184304747006581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12519485402789536498004387 18779228104184304747006581)
                    ·
                      refine ⟨1760552634767278570031867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18779228104184304747006581 1760552634767278570031867)
                      ·
                        rfl

theorem cell23_3428664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_3428664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428664 prefixEnd_3428664 := by exact prefixLift 3428664
  have htrace : WordTrace (prefixWord ++ tailWord_3428664) baseStart_3428664 baseEnd_3428664 := by
    simpa [prefixWord, tailWord_3428664, baseEnd_3428664] using wordTrace_append hprefix tailTrace_3428664
  have hstable : (prefixWord ++ tailWord_3428664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428664).length < 2 ^ (prefixWord ++ tailWord_3428664).sum := by decide
  have hdescent : baseEnd_3428664 < baseStart_3428664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428665 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3428665 : Nat := 118140960795 + 3428665 * 2 ^ 59
def prefixEnd_3428665 : Nat := 4983230072969 + 3 ^ 40 * 3428665 * 2
def baseEnd_3428665 : Nat := 1760553148247933066119363

theorem tailTrace_3428665 : CollatzResearch.WordTrace tailWord_3428665 prefixEnd_3428665 1760553148247933066119363 := by
  unfold tailWord_3428665
  simp only [CollatzResearch.WordTrace]
  refine ⟨125053686123539749207551449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83369124082359832805034299 125053686123539749207551449)
  ·
    refine ⟨93790264592654811905663587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125053686123539749207551449 93790264592654811905663587)
    ·
      refine ⟨140685396888982217858495381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93790264592654811905663587 140685396888982217858495381)
      ·
        refine ⟨6594627979171041462116971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140685396888982217858495381 6594627979171041462116971)
        ·
          refine ⟨9891941968756562193175457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6594627979171041462116971 9891941968756562193175457)
          ·
            refine ⟨7418956476567421644881593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9891941968756562193175457 7418956476567421644881593)
            ·
              refine ⟨5564217357425566233661195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7418956476567421644881593 5564217357425566233661195)
              ·
                refine ⟨8346326036138349350491793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564217357425566233661195 8346326036138349350491793)
                ·
                  refine ⟨6259744527103762012868845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8346326036138349350491793 6259744527103762012868845)
                  ·
                    refine ⟨2347404197663910754825817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6259744527103762012868845 2347404197663910754825817)
                    ·
                      refine ⟨1760553148247933066119363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347404197663910754825817 1760553148247933066119363)
                      ·
                        rfl

theorem cell23_3428665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3428665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428665 prefixEnd_3428665 := by exact prefixLift 3428665
  have htrace : WordTrace (prefixWord ++ tailWord_3428665) baseStart_3428665 baseEnd_3428665 := by
    simpa [prefixWord, tailWord_3428665, baseEnd_3428665] using wordTrace_append hprefix tailTrace_3428665
  have hstable : (prefixWord ++ tailWord_3428665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428665).length < 2 ^ (prefixWord ++ tailWord_3428665).sum := by decide
  have hdescent : baseEnd_3428665 < baseStart_3428665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428688 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 2, 4]
def baseStart_3428688 : Nat := 118140960795 + 3428688 * 2 ^ 59
def prefixEnd_3428688 : Nat := 4983230072969 + 3 ^ 40 * 3428688 * 2
def baseEnd_3428688 : Nat := 586854986100995492043919

theorem tailTrace_3428688 : CollatzResearch.WordTrace tailWord_3428688 prefixEnd_3428688 586854986100995492043919 := by
  unfold tailWord_3428688
  simp only [CollatzResearch.WordTrace]
  refine ⟨62527262501228212067819359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83369683334970949423759145 62527262501228212067819359)
  ·
    refine ⟨93790893751842318101729039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62527262501228212067819359 93790893751842318101729039)
    ·
      refine ⟨140686340627763477152593559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93790893751842318101729039 140686340627763477152593559)
      ·
        refine ⟨211029510941645215728890339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140686340627763477152593559 211029510941645215728890339)
        ·
          refine ⟨316544266412467823593335509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211029510941645215728890339 316544266412467823593335509)
          ·
            refine ⟨7419006244042214615468801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 316544266412467823593335509 7419006244042214615468801)
            ·
              refine ⟨5564254683031660961601601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419006244042214615468801 5564254683031660961601601)
              ·
                refine ⟨4173191012273745721201201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564254683031660961601601 4173191012273745721201201)
                ·
                  refine ⟨3129893259205309290900901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173191012273745721201201 3129893259205309290900901)
                  ·
                    refine ⟨586854986100995492043919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129893259205309290900901 586854986100995492043919)
                    ·
                      rfl

theorem cell23_3428688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_3428688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428688 prefixEnd_3428688 := by exact prefixLift 3428688
  have htrace : WordTrace (prefixWord ++ tailWord_3428688) baseStart_3428688 baseEnd_3428688 := by
    simpa [prefixWord, tailWord_3428688, baseEnd_3428688] using wordTrace_append hprefix tailTrace_3428688
  have hstable : (prefixWord ++ tailWord_3428688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428688).length < 2 ^ (prefixWord ++ tailWord_3428688).sum := by decide
  have hdescent : baseEnd_3428688 < baseStart_3428688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428745 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 3]
def baseStart_3428745 : Nat := 118140960795 + 3428745 * 2 ^ 59
def prefixEnd_3428745 : Nat := 4983230072969 + 3 ^ 40 * 3428745 * 2
def baseEnd_3428745 : Nat := 1760594226700292753118995

theorem tailTrace_3428745 : CollatzResearch.WordTrace tailWord_3428745 prefixEnd_3428745 1760594226700292753118995 := by
  unfold tailWord_3428745
  simp only [CollatzResearch.WordTrace]
  refine ⟨125056603963249922870463689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83371069308833281913642459 125056603963249922870463689)
  ·
    refine ⟨93792452972437442152847767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125056603963249922870463689 93792452972437442152847767)
    ·
      refine ⟨140688679458656163229271651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93792452972437442152847767 140688679458656163229271651)
      ·
        refine ⟨211033019187984244843907477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140688679458656163229271651 211033019187984244843907477)
        ·
          refine ⟨9892172774436761477058163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211033019187984244843907477 9892172774436761477058163)
          ·
            refine ⟨14838259161655142215587245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892172774436761477058163 14838259161655142215587245)
            ·
              refine ⟨5564347185620678330845217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14838259161655142215587245 5564347185620678330845217)
              ·
                refine ⟨4173260389215508748133913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564347185620678330845217 4173260389215508748133913)
                ·
                  refine ⟨3129945291911631561100435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173260389215508748133913 3129945291911631561100435)
                  ·
                    refine ⟨4694917937867447341650653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3129945291911631561100435 4694917937867447341650653)
                    ·
                      refine ⟨1760594226700292753118995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4694917937867447341650653 1760594226700292753118995)
                      ·
                        rfl

theorem cell23_3428745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_3428745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428745 prefixEnd_3428745 := by exact prefixLift 3428745
  have htrace : WordTrace (prefixWord ++ tailWord_3428745) baseStart_3428745 baseEnd_3428745 := by
    simpa [prefixWord, tailWord_3428745, baseEnd_3428745] using wordTrace_append hprefix tailTrace_3428745
  have hstable : (prefixWord ++ tailWord_3428745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428745).length < 2 ^ (prefixWord ++ tailWord_3428745).sum := by decide
  have hdescent : baseEnd_3428745 < baseStart_3428745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428762 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3]
def baseStart_3428762 : Nat := 118140960795 + 3428762 * 2 ^ 59
def prefixEnd_3428762 : Nat := 4983230072969 + 3 ^ 40 * 3428762 * 2
def baseEnd_3428762 : Nat := 1760602955871419186606417

theorem tailTrace_3428762 : CollatzResearch.WordTrace tailWord_3428762 prefixEnd_3428762 1760602955871419186606417 := by
  unfold tailWord_3428762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31264306001047083693458135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83371482669458889849221693 31264306001047083693458135)
  ·
    refine ⟨46896459001570625540187203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31264306001047083693458135 46896459001570625540187203)
    ·
      refine ⟨70344688502355938310280805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46896459001570625540187203 70344688502355938310280805)
      ·
        refine ⟨13189629094191738433177651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70344688502355938310280805 13189629094191738433177651)
        ·
          refine ⟨19784443641287607649766477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189629094191738433177651 19784443641287607649766477)
          ·
            refine ⟨7419166365482852868662429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19784443641287607649766477 7419166365482852868662429)
            ·
              refine ⟨2782187387056069825748411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7419166365482852868662429 2782187387056069825748411)
              ·
                refine ⟨4173281080584104738622617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782187387056069825748411 4173281080584104738622617)
                ·
                  refine ⟨3129960810438078553966963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173281080584104738622617 3129960810438078553966963)
                  ·
                    refine ⟨4694941215657117830950445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3129960810438078553966963 4694941215657117830950445)
                    ·
                      refine ⟨1760602955871419186606417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4694941215657117830950445 1760602955871419186606417)
                      ·
                        rfl

theorem cell23_3428762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_3428762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428762 prefixEnd_3428762 := by exact prefixLift 3428762
  have htrace : WordTrace (prefixWord ++ tailWord_3428762) baseStart_3428762 baseEnd_3428762 := by
    simpa [prefixWord, tailWord_3428762, baseEnd_3428762] using wordTrace_append hprefix tailTrace_3428762
  have hstable : (prefixWord ++ tailWord_3428762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428762).length < 2 ^ (prefixWord ++ tailWord_3428762).sum := by decide
  have hdescent : baseEnd_3428762 < baseStart_3428762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428785 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3428785 : Nat := 118140960795 + 3428785 * 2 ^ 59
def prefixEnd_3428785 : Nat := 4983230072969 + 3 ^ 40 * 3428785 * 2
def baseEnd_3428785 : Nat := 1760614765926472596618811

theorem tailTrace_3428785 : CollatzResearch.WordTrace tailWord_3428785 prefixEnd_3428785 1760614765926472596618811 := by
  unfold tailWord_3428785
  simp only [CollatzResearch.WordTrace]
  refine ⟨125058062883105009701919809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83372041922070006467946539 125058062883105009701919809)
  ·
    refine ⟨93793547162328757276439857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125058062883105009701919809 93793547162328757276439857)
    ·
      refine ⟨70345160371746567957329893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93793547162328757276439857 70345160371746567957329893)
      ·
        refine ⟨13189717569702481491999355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70345160371746567957329893 13189717569702481491999355)
        ·
          refine ⟨19784576354553722237999033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189717569702481491999355 19784576354553722237999033)
          ·
            refine ⟨14838432265915291678499275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19784576354553722237999033 14838432265915291678499275)
            ·
              refine ⟨22257648398872937517748913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838432265915291678499275 22257648398872937517748913)
              ·
                refine ⟨16693236299154703138311685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22257648398872937517748913 16693236299154703138311685)
                ·
                  refine ⟨3129981806091506838433441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16693236299154703138311685 3129981806091506838433441)
                  ·
                    refine ⟨2347486354568630128825081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3129981806091506838433441 2347486354568630128825081)
                    ·
                      refine ⟨1760614765926472596618811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347486354568630128825081 1760614765926472596618811)
                      ·
                        rfl

theorem cell23_3428785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3428785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428785 prefixEnd_3428785 := by exact prefixLift 3428785
  have htrace : WordTrace (prefixWord ++ tailWord_3428785) baseStart_3428785 baseEnd_3428785 := by
    simpa [prefixWord, tailWord_3428785, baseEnd_3428785] using wordTrace_append hprefix tailTrace_3428785
  have hstable : (prefixWord ++ tailWord_3428785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428785).length < 2 ^ (prefixWord ++ tailWord_3428785).sum := by decide
  have hdescent : baseEnd_3428785 < baseStart_3428785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428808 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 7]
def baseStart_3428808 : Nat := 118140960795 + 3428808 * 2 ^ 59
def prefixEnd_3428808 : Nat := 4983230072969 + 3 ^ 40 * 3428808 * 2
def baseEnd_3428808 : Nat := 195625175109058445181245

theorem tailTrace_3428808 : CollatzResearch.WordTrace tailWord_3428808 prefixEnd_3428808 195625175109058445181245 := by
  unfold tailWord_3428808
  simp only [CollatzResearch.WordTrace]
  refine ⟨62529450881010842315003539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83372601174681123086671385 62529450881010842315003539)
  ·
    refine ⟨93794176321516263472505309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62529450881010842315003539 93794176321516263472505309)
    ·
      refine ⟨35172816120568598802189491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93794176321516263472505309 35172816120568598802189491)
      ·
        refine ⟨52759224180852898203284237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35172816120568598802189491 52759224180852898203284237)
        ·
          refine ⟨19784709067819836826231589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52759224180852898203284237 19784709067819836826231589)
          ·
            refine ⟨3709632950216219404918423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19784709067819836826231589 3709632950216219404918423)
            ·
              refine ⟨5564449425324329107377635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709632950216219404918423 5564449425324329107377635)
              ·
                refine ⟨8346674137986493661066453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564449425324329107377635 8346674137986493661066453)
                ·
                  refine ⟨195625175109058445181245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8346674137986493661066453 195625175109058445181245)
                  ·
                    rfl

theorem cell23_3428808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 7].length) (baseStart_3428808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428808 prefixEnd_3428808 := by exact prefixLift 3428808
  have htrace : WordTrace (prefixWord ++ tailWord_3428808) baseStart_3428808 baseEnd_3428808 := by
    simpa [prefixWord, tailWord_3428808, baseEnd_3428808] using wordTrace_append hprefix tailTrace_3428808
  have hstable : (prefixWord ++ tailWord_3428808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428808).length < 2 ^ (prefixWord ++ tailWord_3428808).sum := by decide
  have hdescent : baseEnd_3428808 < baseStart_3428808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428861 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3428861 : Nat := 118140960795 + 3428861 * 2 ^ 59
def prefixEnd_3428861 : Nat := 4983230072969 + 3 ^ 40 * 3428861 * 2
def baseEnd_3428861 : Nat := 1760653790456214299268461

theorem tailTrace_3428861 : CollatzResearch.WordTrace tailWord_3428861 prefixEnd_3428861 1760653790456214299268461 := by
  unfold tailWord_3428861
  simp only [CollatzResearch.WordTrace]
  refine ⟨125060834830829674681686437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83373889887219783121124291 125060834830829674681686437)
  ·
    refine ⟨23448906530780564002816207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125060834830829674681686437 23448906530780564002816207)
    ·
      refine ⟨35173359796170846004224311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23448906530780564002816207 35173359796170846004224311)
      ·
        refine ⟨52760039694256269006336467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35173359796170846004224311 52760039694256269006336467)
        ·
          refine ⟨79140059541384403509504701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52760039694256269006336467 79140059541384403509504701)
          ·
            refine ⟨29677522328019151316064263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79140059541384403509504701 29677522328019151316064263)
            ·
              refine ⟨44516283492028726974096395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29677522328019151316064263 44516283492028726974096395)
              ·
                refine ⟨66774425238043090461144593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44516283492028726974096395 66774425238043090461144593)
                ·
                  refine ⟨50080818928532317845858445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66774425238043090461144593 50080818928532317845858445)
                  ·
                    refine ⟨18780307098199619192196917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50080818928532317845858445 18780307098199619192196917)
                    ·
                      refine ⟨1760653790456214299268461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18780307098199619192196917 1760653790456214299268461)
                      ·
                        rfl

theorem cell23_3428861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3428861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428861 prefixEnd_3428861 := by exact prefixLift 3428861
  have htrace : WordTrace (prefixWord ++ tailWord_3428861) baseStart_3428861 baseEnd_3428861 := by
    simpa [prefixWord, tailWord_3428861, baseEnd_3428861] using wordTrace_append hprefix tailTrace_3428861
  have hstable : (prefixWord ++ tailWord_3428861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428861).length < 2 ^ (prefixWord ++ tailWord_3428861).sum := by decide
  have hdescent : baseEnd_3428861 < baseStart_3428861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428875 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 2, 4, 2]
def baseStart_3428875 : Nat := 118140960795 + 3428875 * 2 ^ 59
def prefixEnd_3428875 : Nat := 4983230072969 + 3 ^ 40 * 3428875 * 2
def baseEnd_3428875 : Nat := 1760660979185377244493397

theorem tailTrace_3428875 : CollatzResearch.WordTrace tailWord_3428875 prefixEnd_3428875 1760660979185377244493397 := by
  unfold tailWord_3428875
  simp only [CollatzResearch.WordTrace]
  refine ⟨125061345452778955072696079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83374230301852636715130719 125061345452778955072696079)
  ·
    refine ⟨187592018179168432609044119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125061345452778955072696079 187592018179168432609044119)
    ·
      refine ⟨281388027268752648913566179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187592018179168432609044119 281388027268752648913566179)
      ·
        refine ⟨422082040903128973370349269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281388027268752648913566179 422082040903128973370349269)
        ·
          refine ⟨9892547833667085313367561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 422082040903128973370349269 9892547833667085313367561)
          ·
            refine ⟨7419410875250313985025671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9892547833667085313367561 7419410875250313985025671)
            ·
              refine ⟨11129116312875470977538507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419410875250313985025671 11129116312875470977538507)
              ·
                refine ⟨16693674469313206466307761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129116312875470977538507 16693674469313206466307761)
                ·
                  refine ⟨12520255851984904849730821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16693674469313206466307761 12520255851984904849730821)
                  ·
                    refine ⟨2347547972247169659324529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12520255851984904849730821 2347547972247169659324529)
                    ·
                      refine ⟨1760660979185377244493397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347547972247169659324529 1760660979185377244493397)
                      ·
                        rfl

theorem cell23_3428875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4, 2].length) (baseStart_3428875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428875 prefixEnd_3428875 := by exact prefixLift 3428875
  have htrace : WordTrace (prefixWord ++ tailWord_3428875) baseStart_3428875 baseEnd_3428875 := by
    simpa [prefixWord, tailWord_3428875, baseEnd_3428875] using wordTrace_append hprefix tailTrace_3428875
  have hstable : (prefixWord ++ tailWord_3428875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428875).length < 2 ^ (prefixWord ++ tailWord_3428875).sum := by decide
  have hdescent : baseEnd_3428875 < baseStart_3428875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428935 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_3428935 : Nat := 118140960795 + 3428935 * 2 ^ 59
def prefixEnd_3428935 : Nat := 4983230072969 + 3 ^ 40 * 3428935 * 2
def baseEnd_3428935 : Nat := 1760691788024647009743121

theorem tailTrace_3428935 : CollatzResearch.WordTrace tailWord_3428935 prefixEnd_3428935 1760691788024647009743121 := by
  unfold tailWord_3428935
  simp only [CollatzResearch.WordTrace]
  refine ⟨125063533832561585319880259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83375689221707723546586839 125063533832561585319880259)
  ·
    refine ⟨187595300748842377979820389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125063533832561585319880259 187595300748842377979820389)
    ·
      refine ⟨35174118890407945871216323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187595300748842377979820389 35174118890407945871216323)
      ·
        refine ⟨52761178335611918806824485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35174118890407945871216323 52761178335611918806824485)
        ·
          refine ⟨9892720937927234776279591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52761178335611918806824485 9892720937927234776279591)
          ·
            refine ⟨14839081406890852164419387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892720937927234776279591 14839081406890852164419387)
            ·
              refine ⟨22258622110336278246629081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14839081406890852164419387 22258622110336278246629081)
              ·
                refine ⟨16693966582752208684971811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22258622110336278246629081 16693966582752208684971811)
                ·
                  refine ⟨25040949874128313027457717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16693966582752208684971811 25040949874128313027457717)
                  ·
                    refine ⟨2347589050699529346324161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25040949874128313027457717 2347589050699529346324161)
                    ·
                      refine ⟨1760691788024647009743121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347589050699529346324161 1760691788024647009743121)
                      ·
                        rfl

theorem cell23_3428935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_3428935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428935 prefixEnd_3428935 := by exact prefixLift 3428935
  have htrace : WordTrace (prefixWord ++ tailWord_3428935) baseStart_3428935 baseEnd_3428935 := by
    simpa [prefixWord, tailWord_3428935, baseEnd_3428935] using wordTrace_append hprefix tailTrace_3428935
  have hstable : (prefixWord ++ tailWord_3428935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428935).length < 2 ^ (prefixWord ++ tailWord_3428935).sum := by decide
  have hdescent : baseEnd_3428935 < baseStart_3428935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428945 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_3428945 : Nat := 118140960795 + 3428945 * 2 ^ 59
def prefixEnd_3428945 : Nat := 4983230072969 + 3 ^ 40 * 3428945 * 2
def baseEnd_3428945 : Nat := 586898974277063990206025

theorem tailTrace_3428945 : CollatzResearch.WordTrace tailWord_3428945 prefixEnd_3428945 586898974277063990206025 := by
  unfold tailWord_3428945
  simp only [CollatzResearch.WordTrace]
  refine ⟨125063898562525357027744289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83375932375016904685162859 125063898562525357027744289)
  ·
    refine ⟨93797923921894017770808217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125063898562525357027744289 93797923921894017770808217)
    ·
      refine ⟨70348442941420513328106163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93797923921894017770808217 70348442941420513328106163)
      ·
        refine ⟨105522664412130769992159245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70348442941420513328106163 105522664412130769992159245)
        ·
          refine ⟨39570999154549038747059717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105522664412130769992159245 39570999154549038747059717)
          ·
            refine ⟨7419562341477944765073697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39570999154549038747059717 7419562341477944765073697)
            ·
              refine ⟨5564671756108458573805273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419562341477944765073697 5564671756108458573805273)
              ·
                refine ⟨4173503817081343930353955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564671756108458573805273 4173503817081343930353955)
                ·
                  refine ⟨6260255725622015895530933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173503817081343930353955 6260255725622015895530933)
                  ·
                    refine ⟨586898974277063990206025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6260255725622015895530933 586898974277063990206025)
                    ·
                      rfl

theorem cell23_3428945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_3428945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428945 prefixEnd_3428945 := by exact prefixLift 3428945
  have htrace : WordTrace (prefixWord ++ tailWord_3428945) baseStart_3428945 baseEnd_3428945 := by
    simpa [prefixWord, tailWord_3428945, baseEnd_3428945] using wordTrace_append hprefix tailTrace_3428945
  have hstable : (prefixWord ++ tailWord_3428945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428945).length < 2 ^ (prefixWord ++ tailWord_3428945).sum := by decide
  have hdescent : baseEnd_3428945 < baseStart_3428945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428976 : List Nat := [2, 1, 1, 1, 7, 1, 3, 2, 1, 1, 3]
def baseStart_3428976 : Nat := 118140960795 + 3428976 * 2 ^ 59
def prefixEnd_3428976 : Nat := 4983230072969 + 3 ^ 40 * 3428976 * 2
def baseEnd_3428976 : Nat := 1760712840731481349330433

theorem tailTrace_3428976 : CollatzResearch.WordTrace tailWord_3428976 prefixEnd_3428976 1760712840731481349330433 := by
  unfold tailWord_3428976
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532514612706524661061391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83376686150275366214748521 62532514612706524661061391)
  ·
    refine ⟨93798771919059786991592087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62532514612706524661061391 93798771919059786991592087)
    ·
      refine ⟨140698157878589680487388131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93798771919059786991592087 140698157878589680487388131)
      ·
        refine ⟨211047236817884520731082197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140698157878589680487388131 211047236817884520731082197)
        ·
          refine ⟨4946419612919168454634739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 211047236817884520731082197 4946419612919168454634739)
          ·
            refine ⟨7419629419378752681952109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946419612919168454634739 7419629419378752681952109)
            ·
              refine ⟨2782361032267032255732041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7419629419378752681952109 2782361032267032255732041)
              ·
                refine ⟨2086770774200274191799031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782361032267032255732041 2086770774200274191799031)
                ·
                  refine ⟨3130156161300411287698547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086770774200274191799031 3130156161300411287698547)
                  ·
                    refine ⟨4695234241950616931547821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130156161300411287698547 4695234241950616931547821)
                    ·
                      refine ⟨1760712840731481349330433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695234241950616931547821 1760712840731481349330433)
                      ·
                        rfl

theorem cell23_3428976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2, 1, 1, 3].length) (baseStart_3428976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428976 prefixEnd_3428976 := by exact prefixLift 3428976
  have htrace : WordTrace (prefixWord ++ tailWord_3428976) baseStart_3428976 baseEnd_3428976 := by
    simpa [prefixWord, tailWord_3428976, baseEnd_3428976] using wordTrace_append hprefix tailTrace_3428976
  have hstable : (prefixWord ++ tailWord_3428976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428976).length < 2 ^ (prefixWord ++ tailWord_3428976).sum := by decide
  have hdescent : baseEnd_3428976 < baseStart_3428976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3428992 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 2, 4]
def baseStart_3428992 : Nat := 118140960795 + 3428992 * 2 ^ 59
def prefixEnd_3428992 : Nat := 4983230072969 + 3 ^ 40 * 3428992 * 2
def baseEnd_3428992 : Nat := 586907018807317762243453

theorem tailTrace_3428992 : CollatzResearch.WordTrace tailWord_3428992 prefixEnd_3428992 586907018807317762243453 := by
  unfold tailWord_3428992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532806396677542027352615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83377075195570056036470153 62532806396677542027352615)
  ·
    refine ⟨93799209595016313041028923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62532806396677542027352615 93799209595016313041028923)
    ·
      refine ⟨140698814392524469561543385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93799209595016313041028923 140698814392524469561543385)
      ·
        refine ⟨105524110794393352171157539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140698814392524469561543385 105524110794393352171157539)
        ·
          refine ⟨158286166191590028256736309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105524110794393352171157539 158286166191590028256736309)
          ·
            refine ⟨14839328080461565149069029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158286166191590028256736309 14839328080461565149069029)
            ·
              refine ⟨2782374015086543465450443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14839328080461565149069029 2782374015086543465450443)
              ·
                refine ⟨4173561022629815198175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782374015086543465450443 4173561022629815198175665)
                ·
                  refine ⟨3130170766972361398631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173561022629815198175665 3130170766972361398631749)
                  ·
                    refine ⟨586907018807317762243453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3130170766972361398631749 586907018807317762243453)
                    ·
                      rfl

theorem cell23_3428992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_3428992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3428992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3428992 prefixEnd_3428992 := by exact prefixLift 3428992
  have htrace : WordTrace (prefixWord ++ tailWord_3428992) baseStart_3428992 baseEnd_3428992 := by
    simpa [prefixWord, tailWord_3428992, baseEnd_3428992] using wordTrace_append hprefix tailTrace_3428992
  have hstable : (prefixWord ++ tailWord_3428992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3428992).length < 2 ^ (prefixWord ++ tailWord_3428992).sum := by decide
  have hdescent : baseEnd_3428992 < baseStart_3428992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3428992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429002 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3429002 : Nat := 118140960795 + 3429002 * 2 ^ 59
def prefixEnd_3429002 : Nat := 4983230072969 + 3 ^ 40 * 3429002 * 2
def baseEnd_3429002 : Nat := 1760726191228498247605313

theorem tailTrace_3429002 : CollatzResearch.WordTrace tailWord_3429002 prefixEnd_3429002 1760726191228498247605313 := by
  unfold tailWord_3429002
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266494380829713940642315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83377318348879237175046173 31266494380829713940642315)
  ·
    refine ⟨46899741571244570910963473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31266494380829713940642315 46899741571244570910963473)
    ·
      refine ⟨35174806178433428183222605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46899741571244570910963473 35174806178433428183222605)
      ·
        refine ⟨13190552316912535568708477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35174806178433428183222605 13190552316912535568708477)
        ·
          refine ⟨4946457118842200838265679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13190552316912535568708477 4946457118842200838265679)
          ·
            refine ⟨7419685678263301257398519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946457118842200838265679 7419685678263301257398519)
            ·
              refine ⟨11129528517394951886097779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419685678263301257398519 11129528517394951886097779)
              ·
                refine ⟨16694292776092427829146669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129528517394951886097779 16694292776092427829146669)
                ·
                  refine ⟨6260359791034660435930001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16694292776092427829146669 6260359791034660435930001)
                  ·
                    refine ⟨4695269843275995326947501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6260359791034660435930001 4695269843275995326947501)
                    ·
                      refine ⟨1760726191228498247605313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695269843275995326947501 1760726191228498247605313)
                      ·
                        rfl

theorem cell23_3429002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3429002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429002 prefixEnd_3429002 := by exact prefixLift 3429002
  have htrace : WordTrace (prefixWord ++ tailWord_3429002) baseStart_3429002 baseEnd_3429002 := by
    simpa [prefixWord, tailWord_3429002, baseEnd_3429002] using wordTrace_append hprefix tailTrace_3429002
  have hstable : (prefixWord ++ tailWord_3429002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429002).length < 2 ^ (prefixWord ++ tailWord_3429002).sum := by decide
  have hdescent : baseEnd_3429002 < baseStart_3429002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429012 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3429012 : Nat := 118140960795 + 3429012 * 2 ^ 59
def prefixEnd_3429012 : Nat := 4983230072969 + 3 ^ 40 * 3429012 * 2
def baseEnd_3429012 : Nat := 1760731326035043208480267

theorem tailTrace_3429012 : CollatzResearch.WordTrace tailWord_3429012 prefixEnd_3429012 1760731326035043208480267 := by
  unfold tailWord_3429012
  simp only [CollatzResearch.WordTrace]
  refine ⟨62533171126641313735216645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83377561502188418313622193 62533171126641313735216645)
  ·
    refine ⟨11724969586245246325353121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62533171126641313735216645 11724969586245246325353121)
    ·
      refine ⟨8793727189683934744014841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11724969586245246325353121 8793727189683934744014841)
      ·
        refine ⟨6595295392262951058011131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8793727189683934744014841 6595295392262951058011131)
        ·
          refine ⟨9892943088394426587016697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595295392262951058011131 9892943088394426587016697)
          ·
            refine ⟨7419707316295819940262523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9892943088394426587016697 7419707316295819940262523)
            ·
              refine ⟨11129560974443729910393785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419707316295819940262523 11129560974443729910393785)
              ·
                refine ⟨8347170730832797432795339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11129560974443729910393785 8347170730832797432795339)
                ·
                  refine ⟨12520756096249196149193009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347170730832797432795339 12520756096249196149193009)
                  ·
                    refine ⟨9390567072186897111894757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12520756096249196149193009 9390567072186897111894757)
                    ·
                      refine ⟨1760731326035043208480267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9390567072186897111894757 1760731326035043208480267)
                      ·
                        rfl

theorem cell23_3429012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3429012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429012 prefixEnd_3429012 := by exact prefixLift 3429012
  have htrace : WordTrace (prefixWord ++ tailWord_3429012) baseStart_3429012 baseEnd_3429012 := by
    simpa [prefixWord, tailWord_3429012, baseEnd_3429012] using wordTrace_append hprefix tailTrace_3429012
  have hstable : (prefixWord ++ tailWord_3429012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429012).length < 2 ^ (prefixWord ++ tailWord_3429012).sum := by decide
  have hdescent : baseEnd_3429012 < baseStart_3429012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429015 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3429015 : Nat := 118140960795 + 3429015 * 2 ^ 59
def prefixEnd_3429015 : Nat := 4983230072969 + 3 ^ 40 * 3429015 * 2
def baseEnd_3429015 : Nat := 1760732866477006696742753

theorem tailTrace_3429015 : CollatzResearch.WordTrace tailWord_3429015 prefixEnd_3429015 1760732866477006696742753 := by
  unfold tailWord_3429015
  simp only [CollatzResearch.WordTrace]
  refine ⟨125066451672271758982792499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83377634448181172655194999 125066451672271758982792499)
  ·
    refine ⟨187599677508407638474188749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125066451672271758982792499 187599677508407638474188749)
    ·
      refine ⟨70349879065652864427820781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187599677508407638474188749 70349879065652864427820781)
      ·
        refine ⟨26381204649619824160432793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70349879065652864427820781 26381204649619824160432793)
        ·
          refine ⟨19785903487214868120324595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26381204649619824160432793 19785903487214868120324595)
          ·
            refine ⟨29678855230822302180486893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19785903487214868120324595 29678855230822302180486893)
            ·
              refine ⟨11129570711558363317682585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29678855230822302180486893 11129570711558363317682585)
              ·
                refine ⟨8347178033668772488261939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11129570711558363317682585 8347178033668772488261939)
                ·
                  refine ⟨12520767050503158732392909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347178033668772488261939 12520767050503158732392909)
                  ·
                    refine ⟨4695287643938684524647341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12520767050503158732392909 4695287643938684524647341)
                    ·
                      refine ⟨1760732866477006696742753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695287643938684524647341 1760732866477006696742753)
                      ·
                        rfl

theorem cell23_3429015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3429015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429015 prefixEnd_3429015 := by exact prefixLift 3429015
  have htrace : WordTrace (prefixWord ++ tailWord_3429015) baseStart_3429015 baseEnd_3429015 := by
    simpa [prefixWord, tailWord_3429015, baseEnd_3429015] using wordTrace_append hprefix tailTrace_3429015
  have hstable : (prefixWord ++ tailWord_3429015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429015).length < 2 ^ (prefixWord ++ tailWord_3429015).sum := by decide
  have hdescent : baseEnd_3429015 < baseStart_3429015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429076 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3429076 : Nat := 118140960795 + 3429076 * 2 ^ 59
def prefixEnd_3429076 : Nat := 4983230072969 + 3 ^ 40 * 3429076 * 2
def baseEnd_3429076 : Nat := 1760764188796930958079973

theorem tailTrace_3429076 : CollatzResearch.WordTrace tailWord_3429076 prefixEnd_3429076 1760764188796930958079973 := by
  unfold tailWord_3429076
  simp only [CollatzResearch.WordTrace]
  refine ⟨62534338262525383200381541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83379117683367177600508721 62534338262525383200381541)
  ·
    refine ⟨11725188424223509350071539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62534338262525383200381541 11725188424223509350071539)
    ·
      refine ⟨17587782636335264025107309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11725188424223509350071539 17587782636335264025107309)
      ·
        refine ⟨6595418488625724009415241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17587782636335264025107309 6595418488625724009415241)
        ·
          refine ⟨4946563866469293007061431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6595418488625724009415241 4946563866469293007061431)
          ·
            refine ⟨7419845799703939510592147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946563866469293007061431 7419845799703939510592147)
            ·
              refine ⟨11129768699555909265888221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419845799703939510592147 11129768699555909265888221)
              ·
                refine ⟨4173663262333465974708083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11129768699555909265888221 4173663262333465974708083)
                ·
                  refine ⟨6260494893500198962062125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173663262333465974708083 6260494893500198962062125)
                  ·
                    refine ⟨2347685585062574610773297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6260494893500198962062125 2347685585062574610773297)
                    ·
                      refine ⟨1760764188796930958079973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347685585062574610773297 1760764188796930958079973)
                      ·
                        rfl

theorem cell23_3429076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3429076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429076 prefixEnd_3429076 := by exact prefixLift 3429076
  have htrace : WordTrace (prefixWord ++ tailWord_3429076) baseStart_3429076 baseEnd_3429076 := by
    simpa [prefixWord, tailWord_3429076, baseEnd_3429076] using wordTrace_append hprefix tailTrace_3429076
  have hstable : (prefixWord ++ tailWord_3429076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429076).length < 2 ^ (prefixWord ++ tailWord_3429076).sum := by decide
  have hdescent : baseEnd_3429076 < baseStart_3429076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429089 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_3429089 : Nat := 118140960795 + 3429089 * 2 ^ 59
def prefixEnd_3429089 : Nat := 4983230072969 + 3 ^ 40 * 3429089 * 2
def baseEnd_3429089 : Nat := 1760770864045439407217413

theorem tailTrace_3429089 : CollatzResearch.WordTrace tailWord_3429089 prefixEnd_3429089 1760770864045439407217413 := by
  unfold tailWord_3429089
  simp only [CollatzResearch.WordTrace]
  refine ⟨125069150674003669620986321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83379433782669113080657547 125069150674003669620986321)
  ·
    refine ⟨93801863005502752215739741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125069150674003669620986321 93801863005502752215739741)
    ·
      refine ⟨35175698627063532080902403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93801863005502752215739741 35175698627063532080902403)
      ·
        refine ⟨52763547940595298121353605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35175698627063532080902403 52763547940595298121353605)
        ·
          refine ⟨9893165238861618397753801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52763547940595298121353605 9893165238861618397753801)
          ·
            refine ⟨7419873929146213798315351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893165238861618397753801 7419873929146213798315351)
            ·
              refine ⟨11129810893719320697473027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419873929146213798315351 11129810893719320697473027)
              ·
                refine ⟨16694716340578981046209541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129810893719320697473027 16694716340578981046209541)
                ·
                  refine ⟨3130259313858558946164289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16694716340578981046209541 3130259313858558946164289)
                  ·
                    refine ⟨2347694485393919209623217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130259313858558946164289 2347694485393919209623217)
                    ·
                      refine ⟨1760770864045439407217413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347694485393919209623217 1760770864045439407217413)
                      ·
                        rfl

theorem cell23_3429089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_3429089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429089 prefixEnd_3429089 := by exact prefixLift 3429089
  have htrace : WordTrace (prefixWord ++ tailWord_3429089) baseStart_3429089 baseEnd_3429089 := by
    simpa [prefixWord, tailWord_3429089, baseEnd_3429089] using wordTrace_append hprefix tailTrace_3429089
  have hstable : (prefixWord ++ tailWord_3429089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429089).length < 2 ^ (prefixWord ++ tailWord_3429089).sum := by decide
  have hdescent : baseEnd_3429089 < baseStart_3429089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429105 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_3429105 : Nat := 118140960795 + 3429105 * 2 ^ 59
def prefixEnd_3429105 : Nat := 4983230072969 + 3 ^ 40 * 3429105 * 2
def baseEnd_3429105 : Nat := 1760779079735911344617339

theorem tailTrace_3429105 : CollatzResearch.WordTrace tailWord_3429105 prefixEnd_3429105 1760779079735911344617339 := by
  unfold tailWord_3429105
  simp only [CollatzResearch.WordTrace]
  refine ⟨125069734241945704353568769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83379822827963802902379179 125069734241945704353568769)
  ·
    refine ⟨93802300681459278265176577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125069734241945704353568769 93802300681459278265176577)
    ·
      refine ⟨70351725511094458698882433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93802300681459278265176577 70351725511094458698882433)
      ·
        refine ⟨52763794133320844024161825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70351725511094458698882433 52763794133320844024161825)
        ·
          refine ⟨39572845599990633018121369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52763794133320844024161825 39572845599990633018121369)
          ·
            refine ⟨29679634199992974763591027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39572845599990633018121369 29679634199992974763591027)
            ·
              refine ⟨44519451299989462145386541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29679634199992974763591027 44519451299989462145386541)
              ·
                refine ⟨16694794237496048304519953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44519451299989462145386541 16694794237496048304519953)
                ·
                  refine ⟨12521095678122036228389965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16694794237496048304519953 12521095678122036228389965)
                  ·
                    refine ⟨4695410879295763585646237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12521095678122036228389965 4695410879295763585646237)
                    ·
                      refine ⟨1760779079735911344617339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695410879295763585646237 1760779079735911344617339)
                      ·
                        rfl

theorem cell23_3429105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_3429105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429105 prefixEnd_3429105 := by exact prefixLift 3429105
  have htrace : WordTrace (prefixWord ++ tailWord_3429105) baseStart_3429105 baseEnd_3429105 := by
    simpa [prefixWord, tailWord_3429105, baseEnd_3429105] using wordTrace_append hprefix tailTrace_3429105
  have hstable : (prefixWord ++ tailWord_3429105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429105).length < 2 ^ (prefixWord ++ tailWord_3429105).sum := by decide
  have hdescent : baseEnd_3429105 < baseStart_3429105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429115 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 7, 2]
def baseStart_3429115 : Nat := 118140960795 + 3429115 * 2 ^ 59
def prefixEnd_3429115 : Nat := 4983230072969 + 3 ^ 40 * 3429115 * 2
def baseEnd_3429115 : Nat := 1760784214542456305492293

theorem tailTrace_3429115 : CollatzResearch.WordTrace tailWord_3429115 prefixEnd_3429115 1760784214542456305492293 := by
  unfold tailWord_3429115
  simp only [CollatzResearch.WordTrace]
  refine ⟨125070098971909476061432799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83380065981272984040955199 125070098971909476061432799)
  ·
    refine ⟨187605148457864214092149199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125070098971909476061432799 187605148457864214092149199)
    ·
      refine ⟨281407722686796321138223799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187605148457864214092149199 281407722686796321138223799)
      ·
        refine ⟨422111584030194481707335699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281407722686796321138223799 422111584030194481707335699)
        ·
          refine ⟨633167376045291722561003549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422111584030194481707335699 633167376045291722561003549)
          ·
            refine ⟨237437766016984395960376331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 633167376045291722561003549 237437766016984395960376331)
            ·
              refine ⟨356156649025476593940564497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237437766016984395960376331 356156649025476593940564497)
              ·
                refine ⟨267117486769107445455423373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356156649025476593940564497 267117486769107445455423373)
                ·
                  refine ⟨100169057538415292045783765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267117486769107445455423373 100169057538415292045783765)
                  ·
                    refine ⟨2347712286056608407323057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 100169057538415292045783765 2347712286056608407323057)
                    ·
                      refine ⟨1760784214542456305492293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347712286056608407323057 1760784214542456305492293)
                      ·
                        rfl

theorem cell23_3429115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7, 2].length) (baseStart_3429115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429115 prefixEnd_3429115 := by exact prefixLift 3429115
  have htrace : WordTrace (prefixWord ++ tailWord_3429115) baseStart_3429115 baseEnd_3429115 := by
    simpa [prefixWord, tailWord_3429115, baseEnd_3429115] using wordTrace_append hprefix tailTrace_3429115
  have hstable : (prefixWord ++ tailWord_3429115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429115).length < 2 ^ (prefixWord ++ tailWord_3429115).sum := by decide
  have hdescent : baseEnd_3429115 < baseStart_3429115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429202 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3429202 : Nat := 118140960795 + 3429202 * 2 ^ 59
def prefixEnd_3429202 : Nat := 4983230072969 + 3 ^ 40 * 3429202 * 2
def baseEnd_3429202 : Nat := 195647654151044162789377

theorem tailTrace_3429202 : CollatzResearch.WordTrace tailWord_3429202 prefixEnd_3429202 195647654151044162789377 := by
  unfold tailWord_3429202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31268318030648572479962465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83382181415062859946566573 31268318030648572479962465)
  ·
    refine ⟨23451238522986429359971849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31268318030648572479962465 23451238522986429359971849)
    ·
      refine ⟨17588428892239822019978887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23451238522986429359971849 17588428892239822019978887)
      ·
        refine ⟨26382643338359733029968331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17588428892239822019978887 26382643338359733029968331)
        ·
          refine ⟨39573965007539599544952497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26382643338359733029968331 39573965007539599544952497)
          ·
            refine ⟨29680473755654699658714373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39573965007539599544952497 29680473755654699658714373)
            ·
              refine ⟨5565088829185256186008945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29680473755654699658714373 5565088829185256186008945)
              ·
                refine ⟨4173816621888942139506709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5565088829185256186008945 4173816621888942139506709)
                ·
                  refine ⟨195647654151044162789377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4173816621888942139506709 195647654151044162789377)
                  ·
                    rfl

theorem cell23_3429202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3429202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429202 prefixEnd_3429202 := by exact prefixLift 3429202
  have htrace : WordTrace (prefixWord ++ tailWord_3429202) baseStart_3429202 baseEnd_3429202 := by
    simpa [prefixWord, tailWord_3429202, baseEnd_3429202] using wordTrace_append hprefix tailTrace_3429202
  have hstable : (prefixWord ++ tailWord_3429202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429202).length < 2 ^ (prefixWord ++ tailWord_3429202).sum := by decide
  have hdescent : baseEnd_3429202 < baseStart_3429202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429205 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3429205 : Nat := 118140960795 + 3429205 * 2 ^ 59
def prefixEnd_3429205 : Nat := 4983230072969 + 3 ^ 40 * 3429205 * 2
def baseEnd_3429205 : Nat := 1760830427801360953366879

theorem tailTrace_3429205 : CollatzResearch.WordTrace tailWord_3429205 prefixEnd_3429205 1760830427801360953366879 := by
  unfold tailWord_3429205
  simp only [CollatzResearch.WordTrace]
  refine ⟨125073381541583421432209069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83382254361055614288139379 125073381541583421432209069)
  ·
    refine ⟨46902518078093783037078401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125073381541583421432209069 46902518078093783037078401)
    ·
      refine ⟨35176888558570337277808801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46902518078093783037078401 35176888558570337277808801)
      ·
        refine ⟨26382666418927752958356601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35176888558570337277808801 26382666418927752958356601)
        ·
          refine ⟨19786999814195814718767451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26382666418927752958356601 19786999814195814718767451)
          ·
            refine ⟨29680499721293722078151177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19786999814195814718767451 29680499721293722078151177)
            ·
              refine ⟨22260374790970291558613383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29680499721293722078151177 22260374790970291558613383)
              ·
                refine ⟨33390562186455437337920075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22260374790970291558613383 33390562186455437337920075)
                ·
                  refine ⟨50085843279683156006880113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33390562186455437337920075 50085843279683156006880113)
                  ·
                    refine ⟨37564382459762367005160085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50085843279683156006880113 37564382459762367005160085)
                    ·
                      refine ⟨1760830427801360953366879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37564382459762367005160085 1760830427801360953366879)
                      ·
                        rfl

theorem cell23_3429205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3429205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429205 prefixEnd_3429205 := by exact prefixLift 3429205
  have htrace : WordTrace (prefixWord ++ tailWord_3429205) baseStart_3429205 baseEnd_3429205 := by
    simpa [prefixWord, tailWord_3429205, baseEnd_3429205] using wordTrace_append hprefix tailTrace_3429205
  have hstable : (prefixWord ++ tailWord_3429205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429205).length < 2 ^ (prefixWord ++ tailWord_3429205).sum := by decide
  have hdescent : baseEnd_3429205 < baseStart_3429205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429215 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 5, 5]
def baseStart_3429215 : Nat := 118140960795 + 3429215 * 2 ^ 59
def prefixEnd_3429215 : Nat := 4983230072969 + 3 ^ 40 * 3429215 * 2
def baseEnd_3429215 : Nat := 586945187535968638080611

theorem tailTrace_3429215 : CollatzResearch.WordTrace tailWord_3429215 prefixEnd_3429215 586945187535968638080611 := by
  unfold tailWord_3429215
  simp only [CollatzResearch.WordTrace]
  refine ⟨125073746271547193140073099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83382497514364795426715399 125073746271547193140073099)
  ·
    refine ⟨187610619407320789710109649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125073746271547193140073099 187610619407320789710109649)
    ·
      refine ⟨140707964555490592282582237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187610619407320789710109649 140707964555490592282582237)
      ·
        refine ⟨52765486708308972105968339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140707964555490592282582237 52765486708308972105968339)
        ·
          refine ⟨79148230062463458158952509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52765486708308972105968339 79148230062463458158952509)
          ·
            refine ⟨29680586273423796809607191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79148230062463458158952509 29680586273423796809607191)
            ·
              refine ⟨44520879410135695214410787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29680586273423796809607191 44520879410135695214410787)
              ·
                refine ⟨66781319115203542821616181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44520879410135695214410787 66781319115203542821616181)
                ·
                  refine ⟨6260748667050332139526517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66781319115203542821616181 6260748667050332139526517)
                  ·
                    refine ⟨586945187535968638080611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6260748667050332139526517 586945187535968638080611)
                    ·
                      rfl

theorem cell23_3429215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_3429215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429215 prefixEnd_3429215 := by exact prefixLift 3429215
  have htrace : WordTrace (prefixWord ++ tailWord_3429215) baseStart_3429215 baseEnd_3429215 := by
    simpa [prefixWord, tailWord_3429215, baseEnd_3429215] using wordTrace_append hprefix tailTrace_3429215
  have hstable : (prefixWord ++ tailWord_3429215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429215).length < 2 ^ (prefixWord ++ tailWord_3429215).sum := by decide
  have hdescent : baseEnd_3429215 < baseStart_3429215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429265 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3429265 : Nat := 118140960795 + 3429265 * 2 ^ 59
def prefixEnd_3429265 : Nat := 4983230072969 + 3 ^ 40 * 3429265 * 2
def baseEnd_3429265 : Nat := 1760861236640630718616603

theorem tailTrace_3429265 : CollatzResearch.WordTrace tailWord_3429265 prefixEnd_3429265 1760861236640630718616603 := by
  unfold tailWord_3429265
  simp only [CollatzResearch.WordTrace]
  refine ⟨125075569921366051679393249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83383713280910701119595499 125075569921366051679393249)
  ·
    refine ⟨93806677441024538759544937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125075569921366051679393249 93806677441024538759544937)
    ·
      refine ⟨70355008080768404069658703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93806677441024538759544937 70355008080768404069658703)
      ·
        refine ⟨105532512121152606104488055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70355008080768404069658703 105532512121152606104488055)
        ·
          refine ⟨158298768181728909156732083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105532512121152606104488055 158298768181728909156732083)
          ·
            refine ⟨237448152272593363735098125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158298768181728909156732083 237448152272593363735098125)
            ·
              refine ⟨89043057102222511400661797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237448152272593363735098125 89043057102222511400661797)
              ·
                refine ⟨16695573206666720887624087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89043057102222511400661797 16695573206666720887624087)
                ·
                  refine ⟨25043359810000081331436131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16695573206666720887624087 25043359810000081331436131)
                  ·
                    refine ⟨37565039715000121997154197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25043359810000081331436131 37565039715000121997154197)
                    ·
                      refine ⟨1760861236640630718616603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37565039715000121997154197 1760861236640630718616603)
                      ·
                        rfl

theorem cell23_3429265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3429265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429265 prefixEnd_3429265 := by exact prefixLift 3429265
  have htrace : WordTrace (prefixWord ++ tailWord_3429265) baseStart_3429265 baseEnd_3429265 := by
    simpa [prefixWord, tailWord_3429265, baseEnd_3429265] using wordTrace_append hprefix tailTrace_3429265
  have hstable : (prefixWord ++ tailWord_3429265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429265).length < 2 ^ (prefixWord ++ tailWord_3429265).sum := by decide
  have hdescent : baseEnd_3429265 < baseStart_3429265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429279 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 1, 6]
def baseStart_3429279 : Nat := 118140960795 + 3429279 * 2 ^ 59
def prefixEnd_3429279 : Nat := 4983230072969 + 3 ^ 40 * 3429279 * 2
def baseEnd_3429279 : Nat := 586956141789931221280513

theorem tailTrace_3429279 : CollatzResearch.WordTrace tailWord_3429279 prefixEnd_3429279 586956141789931221280513 := by
  unfold tailWord_3429279
  simp only [CollatzResearch.WordTrace]
  refine ⟨125076080543315332070402891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83384053695543554713601927 125076080543315332070402891)
  ·
    refine ⟨187614120814972998105604337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125076080543315332070402891 187614120814972998105604337)
    ·
      refine ⟨140710590611229748579203253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187614120814972998105604337 140710590611229748579203253)
      ·
        refine ⟨13191617869802788929300305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140710590611229748579203253 13191617869802788929300305)
        ·
          refine ⟨9893713402352091696975229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13191617869802788929300305 9893713402352091696975229)
          ·
            refine ⟨3710142525882034386365711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9893713402352091696975229 3710142525882034386365711)
            ·
              refine ⟨5565213788823051579548567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710142525882034386365711 5565213788823051579548567)
              ·
                refine ⟨8347820683234577369322851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565213788823051579548567 8347820683234577369322851)
                ·
                  refine ⟨12521731024851866053984277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8347820683234577369322851 12521731024851866053984277)
                  ·
                    refine ⟨586956141789931221280513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12521731024851866053984277 586956141789931221280513)
                    ·
                      rfl

theorem cell23_3429279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_3429279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429279 prefixEnd_3429279 := by exact prefixLift 3429279
  have htrace : WordTrace (prefixWord ++ tailWord_3429279) baseStart_3429279 baseEnd_3429279 := by
    simpa [prefixWord, tailWord_3429279, baseEnd_3429279] using wordTrace_append hprefix tailTrace_3429279
  have hstable : (prefixWord ++ tailWord_3429279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429279).length < 2 ^ (prefixWord ++ tailWord_3429279).sum := by decide
  have hdescent : baseEnd_3429279 < baseStart_3429279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429289 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_3429289 : Nat := 118140960795 + 3429289 * 2 ^ 59
def prefixEnd_3429289 : Nat := 4983230072969 + 3 ^ 40 * 3429289 * 2
def baseEnd_3429289 : Nat := 1760873560176338624716493

theorem tailTrace_3429289 : CollatzResearch.WordTrace tailWord_3429289 prefixEnd_3429289 1760873560176338624716493 := by
  unfold tailWord_3429289
  simp only [CollatzResearch.WordTrace]
  refine ⟨125076445273279103778266921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83384296848852735852177947 125076445273279103778266921)
  ·
    refine ⟨93807333954959327833700191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125076445273279103778266921 93807333954959327833700191)
    ·
      refine ⟨140711000932438991750550287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93807333954959327833700191 140711000932438991750550287)
      ·
        refine ⟨211066501398658487625825431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140711000932438991750550287 211066501398658487625825431)
        ·
          refine ⟨316599752097987731438738147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211066501398658487625825431 316599752097987731438738147)
          ·
            refine ⟨474899628146981597158107221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316599752097987731438738147 474899628146981597158107221)
            ·
              refine ⟨5565230017347440591696569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 474899628146981597158107221 5565230017347440591696569)
              ·
                refine ⟨4173922513010580443772427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5565230017347440591696569 4173922513010580443772427)
                ·
                  refine ⟨6260883769515870665658641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173922513010580443772427 6260883769515870665658641)
                  ·
                    refine ⟨4695662827136902999243981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6260883769515870665658641 4695662827136902999243981)
                    ·
                      refine ⟨1760873560176338624716493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695662827136902999243981 1760873560176338624716493)
                      ·
                        rfl

theorem cell23_3429289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_3429289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429289 prefixEnd_3429289 := by exact prefixLift 3429289
  have htrace : WordTrace (prefixWord ++ tailWord_3429289) baseStart_3429289 baseEnd_3429289 := by
    simpa [prefixWord, tailWord_3429289, baseEnd_3429289] using wordTrace_append hprefix tailTrace_3429289
  have hstable : (prefixWord ++ tailWord_3429289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429289).length < 2 ^ (prefixWord ++ tailWord_3429289).sum := by decide
  have hdescent : baseEnd_3429289 < baseStart_3429289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429303 : List Nat := [1, 1, 3, 1, 3, 1, 5, 3, 1, 2, 2]
def baseStart_3429303 : Nat := 118140960795 + 3429303 * 2 ^ 59
def prefixEnd_3429303 : Nat := 4983230072969 + 3 ^ 40 * 3429303 * 2
def baseEnd_3429303 : Nat := 1760880748905501569941429

theorem tailTrace_3429303 : CollatzResearch.WordTrace tailWord_3429303 prefixEnd_3429303 1760880748905501569941429 := by
  unfold tailWord_3429303
  simp only [CollatzResearch.WordTrace]
  refine ⟨125076955895228384169276563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83384637263485589446184375 125076955895228384169276563)
  ·
    refine ⟨187615433842842576253914845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125076955895228384169276563 187615433842842576253914845)
    ·
      refine ⟨70355787691065966095218067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187615433842842576253914845 70355787691065966095218067)
      ·
        refine ⟨105533681536598949142827101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70355787691065966095218067 105533681536598949142827101)
        ·
          refine ⟨39575130576224605928560163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105533681536598949142827101 39575130576224605928560163)
          ·
            refine ⟨59362695864336908892840245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39575130576224605928560163 59362695864336908892840245)
            ·
              refine ⟨5565252737281585208703773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59362695864336908892840245 5565252737281585208703773)
              ·
                refine ⟨2086969776480594453263915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5565252737281585208703773 2086969776480594453263915)
                ·
                  refine ⟨3130454664720891679895873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086969776480594453263915 3130454664720891679895873)
                  ·
                    refine ⟨2347840998540668759921905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130454664720891679895873 2347840998540668759921905)
                    ·
                      refine ⟨1760880748905501569941429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347840998540668759921905 1760880748905501569941429)
                      ·
                        rfl

theorem cell23_3429303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_3429303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429303 prefixEnd_3429303 := by exact prefixLift 3429303
  have htrace : WordTrace (prefixWord ++ tailWord_3429303) baseStart_3429303 baseEnd_3429303 := by
    simpa [prefixWord, tailWord_3429303, baseEnd_3429303] using wordTrace_append hprefix tailTrace_3429303
  have hstable : (prefixWord ++ tailWord_3429303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429303).length < 2 ^ (prefixWord ++ tailWord_3429303).sum := by decide
  have hdescent : baseEnd_3429303 < baseStart_3429303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429309 : List Nat := [1, 4, 1, 2, 5, 1, 9]
def baseStart_3429309 : Nat := 118140960795 + 3429309 * 2 ^ 59
def prefixEnd_3429309 : Nat := 4983230072969 + 3 ^ 40 * 3429309 * 2
def baseEnd_3429309 : Nat := 21739306540610228968721

theorem tailTrace_3429309 : CollatzResearch.WordTrace tailWord_3429309 prefixEnd_3429309 21739306540610228968721 := by
  unfold tailWord_3429309
  simp only [CollatzResearch.WordTrace]
  refine ⟨125077174733206647193994981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83384783155471098129329987 125077174733206647193994981)
  ·
    refine ⟨23451970262476246348874059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125077174733206647193994981 23451970262476246348874059)
    ·
      refine ⟨35177955393714369523311089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23451970262476246348874059 35177955393714369523311089)
      ·
        refine ⟨26383466545285777142483317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35177955393714369523311089 26383466545285777142483317)
        ·
          refine ⟨2473449988620541607107811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26383466545285777142483317 2473449988620541607107811)
          ·
            refine ⟨3710174982930812410661717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473449988620541607107811 3710174982930812410661717)
            ·
              refine ⟨21739306540610228968721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3710174982930812410661717 21739306540610228968721)
              ·
                rfl

theorem cell23_3429309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 9].length) (baseStart_3429309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429309 prefixEnd_3429309 := by exact prefixLift 3429309
  have htrace : WordTrace (prefixWord ++ tailWord_3429309) baseStart_3429309 baseEnd_3429309 := by
    simpa [prefixWord, tailWord_3429309, baseEnd_3429309] using wordTrace_append hprefix tailTrace_3429309
  have hstable : (prefixWord ++ tailWord_3429309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429309).length < 2 ^ (prefixWord ++ tailWord_3429309).sum := by decide
  have hdescent : baseEnd_3429309 < baseStart_3429309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429319 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_3429319 : Nat := 118140960795 + 3429319 * 2 ^ 59
def prefixEnd_3429319 : Nat := 4983230072969 + 3 ^ 40 * 3429319 * 2
def baseEnd_3429319 : Nat := 1760888964595973507341355

theorem tailTrace_3429319 : CollatzResearch.WordTrace tailWord_3429319 prefixEnd_3429319 1760888964595973507341355 := by
  unfold tailWord_3429319
  simp only [CollatzResearch.WordTrace]
  refine ⟨125077539463170418901859011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83385026308780279267906007 125077539463170418901859011)
  ·
    refine ⟨187616309194755628352788517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125077539463170418901859011 187616309194755628352788517)
    ·
      refine ⟨35178057974016680316147847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187616309194755628352788517 35178057974016680316147847)
      ·
        refine ⟨52767086961025020474221771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35178057974016680316147847 52767086961025020474221771)
        ·
          refine ⟨79150630441537530711332657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52767086961025020474221771 79150630441537530711332657)
          ·
            refine ⟨59362972831153148033499493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79150630441537530711332657 59362972831153148033499493)
            ·
              refine ⟨11130557405841215256281155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59362972831153148033499493 11130557405841215256281155)
              ·
                refine ⟨16695836108761822884421733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11130557405841215256281155 16695836108761822884421733)
                ·
                  refine ⟨3130469270392841790829075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16695836108761822884421733 3130469270392841790829075)
                  ·
                    refine ⟨4695703905589262686243613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130469270392841790829075 4695703905589262686243613)
                    ·
                      refine ⟨1760888964595973507341355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695703905589262686243613 1760888964595973507341355)
                      ·
                        rfl

theorem cell23_3429319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_3429319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429319 prefixEnd_3429319 := by exact prefixLift 3429319
  have htrace : WordTrace (prefixWord ++ tailWord_3429319) baseStart_3429319 baseEnd_3429319 := by
    simpa [prefixWord, tailWord_3429319, baseEnd_3429319] using wordTrace_append hprefix tailTrace_3429319
  have hstable : (prefixWord ++ tailWord_3429319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429319).length < 2 ^ (prefixWord ++ tailWord_3429319).sum := by decide
  have hdescent : baseEnd_3429319 < baseStart_3429319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429320 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_3429320 : Nat := 118140960795 + 3429320 * 2 ^ 59
def prefixEnd_3429320 : Nat := 4983230072969 + 3 ^ 40 * 3429320 * 2
def baseEnd_3429320 : Nat := 1760889478076628003428851

theorem tailTrace_3429320 : CollatzResearch.WordTrace tailWord_3429320 prefixEnd_3429320 1760889478076628003428851 := by
  unfold tailWord_3429320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62538787968083398036322707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83385050624111197381763609 62538787968083398036322707)
  ·
    refine ⟨93808181952125097054484061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62538787968083398036322707 93808181952125097054484061)
    ·
      refine ⟨35178068232046911395431523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93808181952125097054484061 35178068232046911395431523)
      ·
        refine ⟨52767102348070367093147285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35178068232046911395431523 52767102348070367093147285)
        ·
          refine ⟨2473457922565798457491279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52767102348070367093147285 2473457922565798457491279)
          ·
            refine ⟨3710186883848697686236919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473457922565798457491279 3710186883848697686236919)
            ·
              refine ⟨5565280325773046529355379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710186883848697686236919 5565280325773046529355379)
              ·
                refine ⟨8347920488659569794033069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565280325773046529355379 8347920488659569794033069)
                ·
                  refine ⟨3130470183247338672762401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8347920488659569794033069 3130470183247338672762401)
                  ·
                    refine ⟨2347852637435504004571801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130470183247338672762401 2347852637435504004571801)
                    ·
                      refine ⟨1760889478076628003428851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347852637435504004571801 1760889478076628003428851)
                      ·
                        rfl

theorem cell23_3429320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_3429320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429320 prefixEnd_3429320 := by exact prefixLift 3429320
  have htrace : WordTrace (prefixWord ++ tailWord_3429320) baseStart_3429320 baseEnd_3429320 := by
    simpa [prefixWord, tailWord_3429320, baseEnd_3429320] using wordTrace_append hprefix tailTrace_3429320
  have hstable : (prefixWord ++ tailWord_3429320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429320).length < 2 ^ (prefixWord ++ tailWord_3429320).sum := by decide
  have hdescent : baseEnd_3429320 < baseStart_3429320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429329 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_3429329 : Nat := 118140960795 + 3429329 * 2 ^ 59
def prefixEnd_3429329 : Nat := 4983230072969 + 3 ^ 40 * 3429329 * 2
def baseEnd_3429329 : Nat := 1760894099402518468216309

theorem tailTrace_3429329 : CollatzResearch.WordTrace tailWord_3429329 prefixEnd_3429329 1760894099402518468216309 := by
  unfold tailWord_3429329
  simp only [CollatzResearch.WordTrace]
  refine ⟨125077904193134190609723041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83385269462089460406482027 125077904193134190609723041)
  ·
    refine ⟨93808428144850642957292281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125077904193134190609723041 93808428144850642957292281)
    ·
      refine ⟨70356321108637982217969211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93808428144850642957292281 70356321108637982217969211)
      ·
        refine ⟨105534481662956973326953817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70356321108637982217969211 105534481662956973326953817)
        ·
          refine ⟨79150861247217729995215363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105534481662956973326953817 79150861247217729995215363)
          ·
            refine ⟨118726291870826594992823045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79150861247217729995215363 118726291870826594992823045)
            ·
              refine ⟨22261179725779986561154321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118726291870826594992823045 22261179725779986561154321)
              ·
                refine ⟨16695884794334989920865741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22261179725779986561154321 16695884794334989920865741)
                ·
                  refine ⟨6260956797875621220324653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16695884794334989920865741 6260956797875621220324653)
                  ·
                    refine ⟨2347858799203357957621745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6260956797875621220324653 2347858799203357957621745)
                    ·
                      refine ⟨1760894099402518468216309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347858799203357957621745 1760894099402518468216309)
                      ·
                        rfl

theorem cell23_3429329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_3429329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429329 prefixEnd_3429329 := by exact prefixLift 3429329
  have htrace : WordTrace (prefixWord ++ tailWord_3429329) baseStart_3429329 baseEnd_3429329 := by
    simpa [prefixWord, tailWord_3429329, baseEnd_3429329] using wordTrace_append hprefix tailTrace_3429329
  have hstable : (prefixWord ++ tailWord_3429329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429329).length < 2 ^ (prefixWord ++ tailWord_3429329).sum := by decide
  have hdescent : baseEnd_3429329 < baseStart_3429329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429336 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3429336 : Nat := 118140960795 + 3429336 * 2 ^ 59
def prefixEnd_3429336 : Nat := 4983230072969 + 3 ^ 40 * 3429336 * 2
def baseEnd_3429336 : Nat := 1760897693767099940828777

theorem tailTrace_3429336 : CollatzResearch.WordTrace tailWord_3429336 prefixEnd_3429336 1760897693767099940828777 := by
  unfold tailWord_3429336
  simp only [CollatzResearch.WordTrace]
  refine ⟨62539079752054415402613931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83385439669405887203485241 62539079752054415402613931)
  ·
    refine ⟨93808619628081623103920897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62539079752054415402613931 93808619628081623103920897)
    ·
      refine ⟨70356464721061217327940673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93808619628081623103920897 70356464721061217327940673)
      ·
        refine ⟨52767348540795912995955505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70356464721061217327940673 52767348540795912995955505)
        ·
          refine ⟨39575511405596934746966629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52767348540795912995955505 39575511405596934746966629)
          ·
            refine ⟨7420408388549425265056243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39575511405596934746966629 7420408388549425265056243)
            ·
              refine ⟨11130612582824137897584365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420408388549425265056243 11130612582824137897584365)
              ·
                refine ⟨4173979718559051711594137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11130612582824137897584365 4173979718559051711594137)
                ·
                  refine ⟨3130484788919288783695603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173979718559051711594137 3130484788919288783695603)
                  ·
                    refine ⟨4695727183378933175543405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130484788919288783695603 4695727183378933175543405)
                    ·
                      refine ⟨1760897693767099940828777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695727183378933175543405 1760897693767099940828777)
                      ·
                        rfl

theorem cell23_3429336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3429336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429336 prefixEnd_3429336 := by exact prefixLift 3429336
  have htrace : WordTrace (prefixWord ++ tailWord_3429336) baseStart_3429336 baseEnd_3429336 := by
    simpa [prefixWord, tailWord_3429336, baseEnd_3429336] using wordTrace_append hprefix tailTrace_3429336
  have hstable : (prefixWord ++ tailWord_3429336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429336).length < 2 ^ (prefixWord ++ tailWord_3429336).sum := by decide
  have hdescent : baseEnd_3429336 < baseStart_3429336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429359 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 3, 4, 2]
def baseStart_3429359 : Nat := 118140960795 + 3429359 * 2 ^ 59
def prefixEnd_3429359 : Nat := 4983230072969 + 3 ^ 40 * 3429359 * 2
def baseEnd_3429359 : Nat := 1760909503822153350841171

theorem tailTrace_3429359 : CollatzResearch.WordTrace tailWord_3429359 prefixEnd_3429359 1760909503822153350841171 := by
  unfold tailWord_3429359
  simp only [CollatzResearch.WordTrace]
  refine ⟨125078998383025505733315131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83385998922017003822210087 125078998383025505733315131)
  ·
    refine ⟨187618497574538258599972697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125078998383025505733315131 187618497574538258599972697)
    ·
      refine ⟨140713873180903693949979523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187618497574538258599972697 140713873180903693949979523)
      ·
        refine ⟨211070809771355540924969285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140713873180903693949979523 211070809771355540924969285)
        ·
          refine ⟨39575776832129163923431741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211070809771355540924969285 39575776832129163923431741)
          ·
            refine ⟨14840916312048436471286903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39575776832129163923431741 14840916312048436471286903)
            ·
              refine ⟨22261374468072654706930355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14840916312048436471286903 22261374468072654706930355)
              ·
                refine ⟨33392061702108982060395533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22261374468072654706930355 33392061702108982060395533)
                ·
                  refine ⟨12522023138290868272648325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33392061702108982060395533 12522023138290868272648325)
                  ·
                    refine ⟨2347879338429537801121561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12522023138290868272648325 2347879338429537801121561)
                    ·
                      refine ⟨1760909503822153350841171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347879338429537801121561 1760909503822153350841171)
                      ·
                        rfl

theorem cell23_3429359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4, 2].length) (baseStart_3429359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429359 prefixEnd_3429359 := by exact prefixLift 3429359
  have htrace : WordTrace (prefixWord ++ tailWord_3429359) baseStart_3429359 baseEnd_3429359 := by
    simpa [prefixWord, tailWord_3429359, baseEnd_3429359] using wordTrace_append hprefix tailTrace_3429359
  have hstable : (prefixWord ++ tailWord_3429359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429359).length < 2 ^ (prefixWord ++ tailWord_3429359).sum := by decide
  have hdescent : baseEnd_3429359 < baseStart_3429359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429399 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 7]
def baseStart_3429399 : Nat := 118140960795 + 3429399 * 2 ^ 59
def prefixEnd_3429399 : Nat := 4983230072969 + 3 ^ 40 * 3429399 * 2
def baseEnd_3429399 : Nat := 195658893672037021593443

theorem tailTrace_3429399 : CollatzResearch.WordTrace tailWord_3429399 prefixEnd_3429399 195658893672037021593443 := by
  unfold tailWord_3429399
  simp only [CollatzResearch.WordTrace]
  refine ⟨125080457302880592564771251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83386971535253728376514167 125080457302880592564771251)
  ·
    refine ⟨187620685954320888847156877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125080457302880592564771251 187620685954320888847156877)
    ·
      refine ⟨70357757232870333317683829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187620685954320888847156877 70357757232870333317683829)
      ·
        refine ⟨6596039740581593748532859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70357757232870333317683829 6596039740581593748532859)
        ·
          refine ⟨9894059610872390622799289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596039740581593748532859 9894059610872390622799289)
          ·
            refine ⟨7420544708154292967099467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9894059610872390622799289 7420544708154292967099467)
            ·
              refine ⟨11130817062231439450649201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420544708154292967099467 11130817062231439450649201)
              ·
                refine ⟨8348112796673579587986901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11130817062231439450649201 8348112796673579587986901)
                ·
                  refine ⟨195658893672037021593443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8348112796673579587986901 195658893672037021593443)
                  ·
                    rfl

theorem cell23_3429399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 7].length) (baseStart_3429399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429399 prefixEnd_3429399 := by exact prefixLift 3429399
  have htrace : WordTrace (prefixWord ++ tailWord_3429399) baseStart_3429399 baseEnd_3429399 := by
    simpa [prefixWord, tailWord_3429399, baseEnd_3429399] using wordTrace_append hprefix tailTrace_3429399
  have hstable : (prefixWord ++ tailWord_3429399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429399).length < 2 ^ (prefixWord ++ tailWord_3429399).sum := by decide
  have hdescent : baseEnd_3429399 < baseStart_3429399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429446 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_3429446 : Nat := 118140960795 + 3429446 * 2 ^ 59
def prefixEnd_3429446 : Nat := 4983230072969 + 3 ^ 40 * 3429446 * 2
def baseEnd_3429446 : Nat := 586984725546364836817757

theorem tailTrace_3429446 : CollatzResearch.WordTrace tailWord_3429446 prefixEnd_3429446 586984725546364836817757 := by
  unfold tailWord_3429446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908817860428447487241631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83388114355806879727821461 3908817860428447487241631)
  ·
    refine ⟨5863226790642671230862447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3908817860428447487241631 5863226790642671230862447)
    ·
      refine ⟨8794840185964006846293671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863226790642671230862447 8794840185964006846293671)
      ·
        refine ⟨13192260278946010269440507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8794840185964006846293671 13192260278946010269440507)
        ·
          refine ⟨19788390418419015404160761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192260278946010269440507 19788390418419015404160761)
          ·
            refine ⟨14841292813814261553120571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19788390418419015404160761 14841292813814261553120571)
            ·
              refine ⟨22261939220721392329680857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841292813814261553120571 22261939220721392329680857)
              ·
                refine ⟨16696454415541044247260643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22261939220721392329680857 16696454415541044247260643)
                ·
                  refine ⟨25044681623311566370890965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16696454415541044247260643 25044681623311566370890965)
                  ·
                    refine ⟨586984725546364836817757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25044681623311566370890965 586984725546364836817757)
                    ·
                      rfl

theorem cell23_3429446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_3429446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429446 prefixEnd_3429446 := by exact prefixLift 3429446
  have htrace : WordTrace (prefixWord ++ tailWord_3429446) baseStart_3429446 baseEnd_3429446 := by
    simpa [prefixWord, tailWord_3429446, baseEnd_3429446] using wordTrace_append hprefix tailTrace_3429446
  have hstable : (prefixWord ++ tailWord_3429446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429446).length < 2 ^ (prefixWord ++ tailWord_3429446).sum := by decide
  have hdescent : baseEnd_3429446 < baseStart_3429446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429449 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 6, 2]
def baseStart_3429449 : Nat := 118140960795 + 3429449 * 2 ^ 59
def prefixEnd_3429449 : Nat := 4983230072969 + 3 ^ 40 * 3429449 * 2
def baseEnd_3429449 : Nat := 1760955717081057998715757

theorem tailTrace_3429449 : CollatzResearch.WordTrace tailWord_3429449 prefixEnd_3429449 1760955717081057998715757 := by
  unfold tailWord_3429449
  simp only [CollatzResearch.WordTrace]
  refine ⟨125082280952699451104091401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83388187301799634069394267 125082280952699451104091401)
  ·
    refine ⟨93811710714524588328068551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125082280952699451104091401 93811710714524588328068551)
    ·
      refine ⟨140717566071786882492102827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93811710714524588328068551 140717566071786882492102827)
      ·
        refine ⟨211076349107680323738154241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140717566071786882492102827 211076349107680323738154241)
        ·
          refine ⟨158307261830760242803615681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211076349107680323738154241 158307261830760242803615681)
          ·
            refine ⟨118730446373070182102711761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158307261830760242803615681 118730446373070182102711761)
            ·
              refine ⟨89047834779802636577033821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118730446373070182102711761 89047834779802636577033821)
              ·
                refine ⟨33392938042425988716387683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89047834779802636577033821 33392938042425988716387683)
                ·
                  refine ⟨50089407063638983074581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33392938042425988716387683 50089407063638983074581525)
                  ·
                    refine ⟨2347940956108077331621009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50089407063638983074581525 2347940956108077331621009)
                    ·
                      refine ⟨1760955717081057998715757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2347940956108077331621009 1760955717081057998715757)
                      ·
                        rfl

theorem cell23_3429449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6, 2].length) (baseStart_3429449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429449 prefixEnd_3429449 := by exact prefixLift 3429449
  have htrace : WordTrace (prefixWord ++ tailWord_3429449) baseStart_3429449 baseEnd_3429449 := by
    simpa [prefixWord, tailWord_3429449, baseEnd_3429449] using wordTrace_append hprefix tailTrace_3429449
  have hstable : (prefixWord ++ tailWord_3429449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429449).length < 2 ^ (prefixWord ++ tailWord_3429449).sum := by decide
  have hdescent : baseEnd_3429449 < baseStart_3429449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429472 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 10]
def baseStart_3429472 : Nat := 118140960795 + 3429472 * 2 ^ 59
def prefixEnd_3429472 : Nat := 4983230072969 + 3 ^ 40 * 3429472 * 2
def baseEnd_3429472 : Nat := 195663058570679045414239

theorem tailTrace_3429472 : CollatzResearch.WordTrace tailWord_3429472 prefixEnd_3429472 195663058570679045414239 := by
  unfold tailWord_3429472
  simp only [CollatzResearch.WordTrace]
  refine ⟨62541559915808063016089335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83388746554410750688119113 62541559915808063016089335)
  ·
    refine ⟨93812339873712094524134003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62541559915808063016089335 93812339873712094524134003)
    ·
      refine ⟨140718509810568141786201005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93812339873712094524134003 140718509810568141786201005)
      ·
        refine ⟨52769441178963053169825377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140718509810568141786201005 52769441178963053169825377)
        ·
          refine ⟨39577080884222289877369033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52769441178963053169825377 39577080884222289877369033)
          ·
            refine ⟨29682810663166717408026775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39577080884222289877369033 29682810663166717408026775)
            ·
              refine ⟨44524215994750076112040163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29682810663166717408026775 44524215994750076112040163)
              ·
                refine ⟨66786323992125114168060245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44524215994750076112040163 66786323992125114168060245)
                ·
                  refine ⟨195663058570679045414239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66786323992125114168060245 195663058570679045414239)
                  ·
                    rfl

theorem cell23_3429472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_3429472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429472 prefixEnd_3429472 := by exact prefixLift 3429472
  have htrace : WordTrace (prefixWord ++ tailWord_3429472) baseStart_3429472 baseEnd_3429472 := by
    simpa [prefixWord, tailWord_3429472, baseEnd_3429472] using wordTrace_append hprefix tailTrace_3429472
  have hstable : (prefixWord ++ tailWord_3429472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429472).length < 2 ^ (prefixWord ++ tailWord_3429472).sum := by decide
  have hdescent : baseEnd_3429472 < baseStart_3429472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429486 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3429486 : Nat := 118140960795 + 3429486 * 2 ^ 59
def prefixEnd_3429486 : Nat := 4983230072969 + 3 ^ 40 * 3429486 * 2
def baseEnd_3429486 : Nat := 1760974715865274353953087

theorem tailTrace_3429486 : CollatzResearch.WordTrace tailWord_3429486 prefixEnd_3429486 1760974715865274353953087 := by
  unfold tailWord_3429486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15635453806695675802898539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83389086969043604282125541 15635453806695675802898539)
  ·
    refine ⟨23453180710043513704347809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15635453806695675802898539 23453180710043513704347809)
    ·
      refine ⟨17589885532532635278260857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23453180710043513704347809 17589885532532635278260857)
      ·
        refine ⟨13192414149399476458695643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17589885532532635278260857 13192414149399476458695643)
        ·
          refine ⟨19788621224099214688043465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192414149399476458695643 19788621224099214688043465)
          ·
            refine ⟨14841465918074411016032599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19788621224099214688043465 14841465918074411016032599)
            ·
              refine ⟨22262198877111616524048899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841465918074411016032599 22262198877111616524048899)
              ·
                refine ⟨33393298315667424786073349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22262198877111616524048899 33393298315667424786073349)
                ·
                  refine ⟨6261243434187642147388753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33393298315667424786073349 6261243434187642147388753)
                  ·
                    refine ⟨4695932575640731610541565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261243434187642147388753 4695932575640731610541565)
                    ·
                      refine ⟨1760974715865274353953087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695932575640731610541565 1760974715865274353953087)
                      ·
                        rfl

theorem cell23_3429486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3429486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429486 prefixEnd_3429486 := by exact prefixLift 3429486
  have htrace : WordTrace (prefixWord ++ tailWord_3429486) baseStart_3429486 baseEnd_3429486 := by
    simpa [prefixWord, tailWord_3429486, baseEnd_3429486] using wordTrace_append hprefix tailTrace_3429486
  have hstable : (prefixWord ++ tailWord_3429486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429486).length < 2 ^ (prefixWord ++ tailWord_3429486).sum := by decide
  have hdescent : baseEnd_3429486 < baseStart_3429486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429516 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3429516 : Nat := 118140960795 + 3429516 * 2 ^ 59
def prefixEnd_3429516 : Nat := 4983230072969 + 3 ^ 40 * 3429516 * 2
def baseEnd_3429516 : Nat := 1760990120284909236577949

theorem tailTrace_3429516 : CollatzResearch.WordTrace tailWord_3429516 prefixEnd_3429516 1760990120284909236577949 := by
  unfold tailWord_3429516
  simp only [CollatzResearch.WordTrace]
  refine ⟨62542362321728360773390201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83389816428971147697853601 62542362321728360773390201)
  ·
    refine ⟨46906771741296270580042651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62542362321728360773390201 46906771741296270580042651)
    ·
      refine ⟨70360157611944405870063977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46906771741296270580042651 70360157611944405870063977)
      ·
        refine ⟨52770118208958304402547983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70360157611944405870063977 52770118208958304402547983)
        ·
          refine ⟨79155177313437456603821975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52770118208958304402547983 79155177313437456603821975)
          ·
            refine ⟨118732765970156184905732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79155177313437456603821975 118732765970156184905732963)
            ·
              refine ⟨178099148955234277358599445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118732765970156184905732963 178099148955234277358599445)
              ·
                refine ⟨8348397607276606751184349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178099148955234277358599445 8348397607276606751184349)
                ·
                  refine ⟨3130649102728727531694131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8348397607276606751184349 3130649102728727531694131)
                  ·
                    refine ⟨4695973654093091297541197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130649102728727531694131 4695973654093091297541197)
                    ·
                      refine ⟨1760990120284909236577949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4695973654093091297541197 1760990120284909236577949)
                      ·
                        rfl

theorem cell23_3429516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3429516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429516 prefixEnd_3429516 := by exact prefixLift 3429516
  have htrace : WordTrace (prefixWord ++ tailWord_3429516) baseStart_3429516 baseEnd_3429516 := by
    simpa [prefixWord, tailWord_3429516, baseEnd_3429516] using wordTrace_append hprefix tailTrace_3429516
  have hstable : (prefixWord ++ tailWord_3429516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429516).length < 2 ^ (prefixWord ++ tailWord_3429516).sum := by decide
  have hdescent : baseEnd_3429516 < baseStart_3429516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429559 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_3429559 : Nat := 118140960795 + 3429559 * 2 ^ 59
def prefixEnd_3429559 : Nat := 4983230072969 + 3 ^ 40 * 3429559 * 2
def baseEnd_3429559 : Nat := 1761012199953052568340251

theorem tailTrace_3429559 : CollatzResearch.WordTrace tailWord_3429559 prefixEnd_3429559 1761012199953052568340251 := by
  unfold tailWord_3429559
  simp only [CollatzResearch.WordTrace]
  refine ⟨125086292982300939890595731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83390861988200626593730487 125086292982300939890595731)
  ·
    refine ⟨187629439473451409835893597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125086292982300939890595731 187629439473451409835893597)
    ·
      refine ⟨70361039802544278688460099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187629439473451409835893597 70361039802544278688460099)
      ·
        refine ⟨105541559703816418032690149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70361039802544278688460099 105541559703816418032690149)
        ·
          refine ⟨19789042444465578381129403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105541559703816418032690149 19789042444465578381129403)
          ·
            refine ⟨29683563666698367571694105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789042444465578381129403 29683563666698367571694105)
            ·
              refine ⟨22262672750023775678770579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29683563666698367571694105 22262672750023775678770579)
              ·
                refine ⟨33394009125035663518155869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22262672750023775678770579 33394009125035663518155869)
                ·
                  refine ⟨12522753421888373819308451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33394009125035663518155869 12522753421888373819308451)
                  ·
                    refine ⟨18784130132832560728962677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12522753421888373819308451 18784130132832560728962677)
                    ·
                      refine ⟨1761012199953052568340251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18784130132832560728962677 1761012199953052568340251)
                      ·
                        rfl

theorem cell23_3429559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_3429559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429559 prefixEnd_3429559 := by exact prefixLift 3429559
  have htrace : WordTrace (prefixWord ++ tailWord_3429559) baseStart_3429559 baseEnd_3429559 := by
    simpa [prefixWord, tailWord_3429559, baseEnd_3429559] using wordTrace_append hprefix tailTrace_3429559
  have hstable : (prefixWord ++ tailWord_3429559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429559).length < 2 ^ (prefixWord ++ tailWord_3429559).sum := by decide
  have hdescent : baseEnd_3429559 < baseStart_3429559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429566 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3429566 : Nat := 118140960795 + 3429566 * 2 ^ 59
def prefixEnd_3429566 : Nat := 4983230072969 + 3 ^ 40 * 3429566 * 2
def baseEnd_3429566 : Nat := 587005264772544680317573

theorem tailTrace_3429566 : CollatzResearch.WordTrace tailWord_3429566 prefixEnd_3429566 587005264772544680317573 := by
  unfold tailWord_3429566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15635818536659447510762569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83391032195517053390733701 15635818536659447510762569)
  ·
    refine ⟨11726863902494585633071927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15635818536659447510762569 11726863902494585633071927)
    ·
      refine ⟨17590295853741878449607891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726863902494585633071927 17590295853741878449607891)
      ·
        refine ⟨26385443780612817674411837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17590295853741878449607891 26385443780612817674411837)
        ·
          refine ⟨9894541417729806627904439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26385443780612817674411837 9894541417729806627904439)
          ·
            refine ⟨14841812126594709941856659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894541417729806627904439 14841812126594709941856659)
            ·
              refine ⟨22262718189892064912784989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841812126594709941856659 22262718189892064912784989)
              ·
                refine ⟨8348519321209524342294371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22262718189892064912784989 8348519321209524342294371)
                ·
                  refine ⟨12522778981814286513441557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348519321209524342294371 12522778981814286513441557)
                  ·
                    refine ⟨587005264772544680317573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12522778981814286513441557 587005264772544680317573)
                    ·
                      rfl

theorem cell23_3429566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3429566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429566 prefixEnd_3429566 := by exact prefixLift 3429566
  have htrace : WordTrace (prefixWord ++ tailWord_3429566) baseStart_3429566 baseEnd_3429566 := by
    simpa [prefixWord, tailWord_3429566, baseEnd_3429566] using wordTrace_append hprefix tailTrace_3429566
  have hstable : (prefixWord ++ tailWord_3429566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429566).length < 2 ^ (prefixWord ++ tailWord_3429566).sum := by decide
  have hdescent : baseEnd_3429566 < baseStart_3429566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429576 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_3429576 : Nat := 118140960795 + 3429576 * 2 ^ 59
def prefixEnd_3429576 : Nat := 4983230072969 + 3 ^ 40 * 3429576 * 2
def baseEnd_3429576 : Nat := 1761020929124179001827673

theorem tailTrace_3429576 : CollatzResearch.WordTrace tailWord_3429576 prefixEnd_3429576 1761020929124179001827673 := by
  unfold tailWord_3429576
  simp only [CollatzResearch.WordTrace]
  refine ⟨62543456511619675896982291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83391275348826234529309721 62543456511619675896982291)
  ·
    refine ⟨93815184767429513845473437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62543456511619675896982291 93815184767429513845473437)
    ·
      refine ⟨35180694287786067692052539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93815184767429513845473437 35180694287786067692052539)
      ·
        refine ⟨52771041431679101538078809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35180694287786067692052539 52771041431679101538078809)
        ·
          refine ⟨39578281073759326153559107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52771041431679101538078809 39578281073759326153559107)
          ·
            refine ⟨59367421610638989230338661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39578281073759326153559107 59367421610638989230338661)
            ·
              refine ⟨11131391551994810480688499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59367421610638989230338661 11131391551994810480688499)
              ·
                refine ⟨16697087327992215721032749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11131391551994810480688499 16697087327992215721032749)
                ·
                  refine ⟨6261407747997080895387281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16697087327992215721032749 6261407747997080895387281)
                  ·
                    refine ⟨4696055810997810671540461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6261407747997080895387281 4696055810997810671540461)
                    ·
                      refine ⟨1761020929124179001827673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696055810997810671540461 1761020929124179001827673)
                      ·
                        rfl

theorem cell23_3429576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_3429576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429576 prefixEnd_3429576 := by exact prefixLift 3429576
  have htrace : WordTrace (prefixWord ++ tailWord_3429576) baseStart_3429576 baseEnd_3429576 := by
    simpa [prefixWord, tailWord_3429576, baseEnd_3429576] using wordTrace_append hprefix tailTrace_3429576
  have hstable : (prefixWord ++ tailWord_3429576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429576).length < 2 ^ (prefixWord ++ tailWord_3429576).sum := by decide
  have hdescent : baseEnd_3429576 < baseStart_3429576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429586 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3429586 : Nat := 118140960795 + 3429586 * 2 ^ 59
def prefixEnd_3429586 : Nat := 4983230072969 + 3 ^ 40 * 3429586 * 2
def baseEnd_3429586 : Nat := 1761026063930723962702627

theorem tailTrace_3429586 : CollatzResearch.WordTrace tailWord_3429586 prefixEnd_3429586 1761026063930723962702627 := by
  unfold tailWord_3429586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31271819438300780875457153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83391518502135415667885741 31271819438300780875457153)
  ·
    refine ⟨23453864578725585656592865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31271819438300780875457153 23453864578725585656592865)
    ·
      refine ⟨17590398434044189242444649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23453864578725585656592865 17590398434044189242444649)
      ·
        refine ⟨13192798825533141931833487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17590398434044189242444649 13192798825533141931833487)
        ·
          refine ⟨19789198238299712897750231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192798825533141931833487 19789198238299712897750231)
          ·
            refine ⟨29683797357449569346625347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789198238299712897750231 29683797357449569346625347)
            ·
              refine ⟨44525696036174354019938021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29683797357449569346625347 44525696036174354019938021)
              ·
                refine ⟨8348568006782691378738379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44525696036174354019938021 8348568006782691378738379)
                ·
                  refine ⟨12522852010174037068107569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8348568006782691378738379 12522852010174037068107569)
                  ·
                    refine ⟨9392139007630527801080677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12522852010174037068107569 9392139007630527801080677)
                    ·
                      refine ⟨1761026063930723962702627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9392139007630527801080677 1761026063930723962702627)
                      ·
                        rfl

theorem cell23_3429586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3429586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429586 prefixEnd_3429586 := by exact prefixLift 3429586
  have htrace : WordTrace (prefixWord ++ tailWord_3429586) baseStart_3429586 baseEnd_3429586 := by
    simpa [prefixWord, tailWord_3429586, baseEnd_3429586] using wordTrace_append hprefix tailTrace_3429586
  have hstable : (prefixWord ++ tailWord_3429586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429586).length < 2 ^ (prefixWord ++ tailWord_3429586).sum := by decide
  have hdescent : baseEnd_3429586 < baseStart_3429586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429607 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3429607 : Nat := 118140960795 + 3429607 * 2 ^ 59
def prefixEnd_3429607 : Nat := 4983230072969 + 3 ^ 40 * 3429607 * 2
def baseEnd_3429607 : Nat := 1761036847024468380540031

theorem tailTrace_3429607 : CollatzResearch.WordTrace tailWord_3429607 prefixEnd_3429607 1761036847024468380540031 := by
  unfold tailWord_3429607
  simp only [CollatzResearch.WordTrace]
  refine ⟨125088043686127044088343075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83392029124084696058895383 125088043686127044088343075)
  ·
    refine ⟨187632065529190566132514613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125088043686127044088343075 187632065529190566132514613)
    ·
      refine ⟨17590506143361615574923245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187632065529190566132514613 17590506143361615574923245)
      ·
        refine ⟨6596439803760605840596217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17590506143361615574923245 6596439803760605840596217)
        ·
          refine ⟨4947329852820454380447163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596439803760605840596217 4947329852820454380447163)
          ·
            refine ⟨7420994779230681570670745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947329852820454380447163 7420994779230681570670745)
            ·
              refine ⟨5565746084423011178003059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420994779230681570670745 5565746084423011178003059)
              ·
                refine ⟨8348619126634516767004589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565746084423011178003059 8348619126634516767004589)
                ·
                  refine ⟨3130732172487943787626721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8348619126634516767004589 3130732172487943787626721)
                  ·
                    refine ⟨2348049129365957840720041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130732172487943787626721 2348049129365957840720041)
                    ·
                      refine ⟨1761036847024468380540031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348049129365957840720041 1761036847024468380540031)
                      ·
                        rfl

theorem cell23_3429607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3429607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429607 prefixEnd_3429607 := by exact prefixLift 3429607
  have htrace : WordTrace (prefixWord ++ tailWord_3429607) baseStart_3429607 baseEnd_3429607 := by
    simpa [prefixWord, tailWord_3429607, baseEnd_3429607] using wordTrace_append hprefix tailTrace_3429607
  have hstable : (prefixWord ++ tailWord_3429607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429607).length < 2 ^ (prefixWord ++ tailWord_3429607).sum := by decide
  have hdescent : baseEnd_3429607 < baseStart_3429607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429636 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_3429636 : Nat := 118140960795 + 3429636 * 2 ^ 59
def prefixEnd_3429636 : Nat := 4983230072969 + 3 ^ 40 * 3429636 * 2
def baseEnd_3429636 : Nat := 1761051737963448767077397

theorem tailTrace_3429636 : CollatzResearch.WordTrace tailWord_3429636 prefixEnd_3429636 1761051737963448767077397 := by
  unfold tailWord_3429636
  simp only [CollatzResearch.WordTrace]
  refine ⟨62544550701510991020574381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83392734268681321360765841 62544550701510991020574381)
  ·
    refine ⟨23454206513066621632715393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62544550701510991020574381 23454206513066621632715393)
    ·
      refine ⟨17590654884799966224536545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23454206513066621632715393 17590654884799966224536545)
      ·
        refine ⟨13192991163599974668402409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17590654884799966224536545 13192991163599974668402409)
        ·
          refine ⟨9894743372699981001301807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13192991163599974668402409 9894743372699981001301807)
          ·
            refine ⟨14842115059049971501952711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894743372699981001301807 14842115059049971501952711)
            ·
              refine ⟨22263172588574957252929067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14842115059049971501952711 22263172588574957252929067)
              ·
                refine ⟨33394758882862435879393601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22263172588574957252929067 33394758882862435879393601)
                ·
                  refine ⟨25046069162146826909545201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33394758882862435879393601 25046069162146826909545201)
                  ·
                    refine ⟨18784551871610120182158901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25046069162146826909545201 18784551871610120182158901)
                    ·
                      refine ⟨1761051737963448767077397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18784551871610120182158901 1761051737963448767077397)
                      ·
                        rfl

theorem cell23_3429636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_3429636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429636 prefixEnd_3429636 := by exact prefixLift 3429636
  have htrace : WordTrace (prefixWord ++ tailWord_3429636) baseStart_3429636 baseEnd_3429636 := by
    simpa [prefixWord, tailWord_3429636, baseEnd_3429636] using wordTrace_append hprefix tailTrace_3429636
  have hstable : (prefixWord ++ tailWord_3429636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429636).length < 2 ^ (prefixWord ++ tailWord_3429636).sum := by decide
  have hdescent : baseEnd_3429636 < baseStart_3429636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429674 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3429674 : Nat := 118140960795 + 3429674 * 2 ^ 59
def prefixEnd_3429674 : Nat := 4983230072969 + 3 ^ 40 * 3429674 * 2
def baseEnd_3429674 : Nat := 1761071250228319618402223

theorem tailTrace_3429674 : CollatzResearch.WordTrace tailWord_3429674 prefixEnd_3429674 1761071250228319618402223 := by
  unfold tailWord_3429674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31272621844221078632758019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83393658251256209687354717 31272621844221078632758019)
  ·
    refine ⟨46908932766331617949137029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31272621844221078632758019 46908932766331617949137029)
    ·
      refine ⟨8795424893687178365463193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46908932766331617949137029 8795424893687178365463193)
      ·
        refine ⟨6596568670265383774097395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8795424893687178365463193 6596568670265383774097395)
        ·
          refine ⟨9894853005398075661146093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596568670265383774097395 9894853005398075661146093)
          ·
            refine ⟨3710569877024278372929785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9894853005398075661146093 3710569877024278372929785)
            ·
              refine ⟨2782927407768208779697339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710569877024278372929785 2782927407768208779697339)
              ·
                refine ⟨4174391111652313169546009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782927407768208779697339 4174391111652313169546009)
                ·
                  refine ⟨3130793333739234877159507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4174391111652313169546009 3130793333739234877159507)
                  ·
                    refine ⟨4696190000608852315739261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130793333739234877159507 4696190000608852315739261)
                    ·
                      refine ⟨1761071250228319618402223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696190000608852315739261 1761071250228319618402223)
                      ·
                        rfl

theorem cell23_3429674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3429674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429674 prefixEnd_3429674 := by exact prefixLift 3429674
  have htrace : WordTrace (prefixWord ++ tailWord_3429674) baseStart_3429674 baseEnd_3429674 := by
    simpa [prefixWord, tailWord_3429674, baseEnd_3429674] using wordTrace_append hprefix tailTrace_3429674
  have hstable : (prefixWord ++ tailWord_3429674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429674).length < 2 ^ (prefixWord ++ tailWord_3429674).sum := by decide
  have hdescent : baseEnd_3429674 < baseStart_3429674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429680 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2]
def baseStart_3429680 : Nat := 118140960795 + 3429680 * 2 ^ 59
def prefixEnd_3429680 : Nat := 4983230072969 + 3 ^ 40 * 3429680 * 2
def baseEnd_3429680 : Nat := 1761074331112246594927195

theorem tailTrace_3429680 : CollatzResearch.WordTrace tailWord_3429680 prefixEnd_3429680 1761074331112246594927195 := by
  unfold tailWord_3429680
  simp only [CollatzResearch.WordTrace]
  refine ⟨62545353107431288777875247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83393804143241718370500329 62545353107431288777875247)
  ·
    refine ⟨93818029661146933166812871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62545353107431288777875247 93818029661146933166812871)
    ·
      refine ⟨140727044491720399750219307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93818029661146933166812871 140727044491720399750219307)
      ·
        refine ⟨211090566737580599625328961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140727044491720399750219307 211090566737580599625328961)
        ·
          refine ⟨158317925053185449718996721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211090566737580599625328961 158317925053185449718996721)
          ·
            refine ⟨118738443789889087289247541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158317925053185449718996721 118738443789889087289247541)
            ·
              refine ⟨11131729105302101933366957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118738443789889087289247541 11131729105302101933366957)
              ·
                refine ⟨4174398414488288225012609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11131729105302101933366957 4174398414488288225012609)
                ·
                  refine ⟨3130798810866216168759457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4174398414488288225012609 3130798810866216168759457)
                  ·
                    refine ⟨2348099108149662126569593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130798810866216168759457 2348099108149662126569593)
                    ·
                      refine ⟨1761074331112246594927195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348099108149662126569593 1761074331112246594927195)
                      ·
                        rfl

theorem cell23_3429680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2, 2, 2].length) (baseStart_3429680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429680 prefixEnd_3429680 := by exact prefixLift 3429680
  have htrace : WordTrace (prefixWord ++ tailWord_3429680) baseStart_3429680 baseEnd_3429680 := by
    simpa [prefixWord, tailWord_3429680, baseEnd_3429680] using wordTrace_append hprefix tailTrace_3429680
  have hstable : (prefixWord ++ tailWord_3429680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429680).length < 2 ^ (prefixWord ++ tailWord_3429680).sum := by decide
  have hdescent : baseEnd_3429680 < baseStart_3429680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429753 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3429753 : Nat := 118140960795 + 3429753 * 2 ^ 59
def prefixEnd_3429753 : Nat := 4983230072969 + 3 ^ 40 * 3429753 * 2
def baseEnd_3429753 : Nat := 1761111815200024809314359

theorem tailTrace_3429753 : CollatzResearch.WordTrace tailWord_3429753 prefixEnd_3429753 1761111815200024809314359 := by
  unfold tailWord_3429753
  simp only [CollatzResearch.WordTrace]
  refine ⟨125093368743598111023157913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83395579162398740682105275 125093368743598111023157913)
  ·
    refine ⟨93820026557698583267368435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125093368743598111023157913 93820026557698583267368435)
    ·
      refine ⟨140730039836547874901052653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93820026557698583267368435 140730039836547874901052653)
      ·
        refine ⟨52773764938705453087894745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140730039836547874901052653 52773764938705453087894745)
        ·
          refine ⟨39580323704029089815921059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52773764938705453087894745 39580323704029089815921059)
          ·
            refine ⟨59370485556043634723881589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39580323704029089815921059 59370485556043634723881589)
            ·
              refine ⟨5565983020879090755363899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59370485556043634723881589 5565983020879090755363899)
              ·
                refine ⟨8348974531318636133045849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565983020879090755363899 8348974531318636133045849)
                ·
                  refine ⟨6261730898488977099784387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8348974531318636133045849 6261730898488977099784387)
                  ·
                    refine ⟨9392596347733465649676581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6261730898488977099784387 9392596347733465649676581)
                    ·
                      refine ⟨1761111815200024809314359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9392596347733465649676581 1761111815200024809314359)
                      ·
                        rfl

theorem cell23_3429753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3429753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429753 prefixEnd_3429753 := by exact prefixLift 3429753
  have htrace : WordTrace (prefixWord ++ tailWord_3429753) baseStart_3429753 baseEnd_3429753 := by
    simpa [prefixWord, tailWord_3429753, baseEnd_3429753] using wordTrace_append hprefix tailTrace_3429753
  have hstable : (prefixWord ++ tailWord_3429753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429753).length < 2 ^ (prefixWord ++ tailWord_3429753).sum := by decide
  have hdescent : baseEnd_3429753 < baseStart_3429753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429780 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3429780 : Nat := 118140960795 + 3429780 * 2 ^ 59
def prefixEnd_3429780 : Nat := 4983230072969 + 3 ^ 40 * 3429780 * 2
def baseEnd_3429780 : Nat := 587041893059232067892245

theorem tailTrace_3429780 : CollatzResearch.WordTrace tailWord_3429780 prefixEnd_3429780 587041893059232067892245 := by
  unfold tailWord_3429780
  simp only [CollatzResearch.WordTrace]
  refine ⟨62547176757250147317195397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83396235676333529756260529 62547176757250147317195397)
  ·
    refine ⟨11727595641984402621974137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62547176757250147317195397 11727595641984402621974137)
    ·
      refine ⟨8795696731488301966480603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11727595641984402621974137 8795696731488301966480603)
      ·
        refine ⟨13193545097232452949720905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795696731488301966480603 13193545097232452949720905)
        ·
          refine ⟨9895158822924339712290679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13193545097232452949720905 9895158822924339712290679)
          ·
            refine ⟨14842738234386509568436019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9895158822924339712290679 14842738234386509568436019)
            ·
              refine ⟨22264107351579764352654029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14842738234386509568436019 22264107351579764352654029)
              ·
                refine ⟨8349040256842411632245261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22264107351579764352654029 8349040256842411632245261)
                ·
                  refine ⟨3130890096315904362091973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8349040256842411632245261 3130890096315904362091973)
                  ·
                    refine ⟨587041893059232067892245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3130890096315904362091973 587041893059232067892245)
                    ·
                      rfl

theorem cell23_3429780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3429780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429780 prefixEnd_3429780 := by exact prefixLift 3429780
  have htrace : WordTrace (prefixWord ++ tailWord_3429780) baseStart_3429780 baseEnd_3429780 := by
    simpa [prefixWord, tailWord_3429780, baseEnd_3429780] using wordTrace_append hprefix tailTrace_3429780
  have hstable : (prefixWord ++ tailWord_3429780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429780).length < 2 ^ (prefixWord ++ tailWord_3429780).sum := by decide
  have hdescent : baseEnd_3429780 < baseStart_3429780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429796 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_3429796 : Nat := 118140960795 + 3429796 * 2 ^ 59
def prefixEnd_3429796 : Nat := 4983230072969 + 3 ^ 40 * 3429796 * 2
def baseEnd_3429796 : Nat := 1761133894868168141076661

theorem tailTrace_3429796 : CollatzResearch.WordTrace tailWord_3429796 prefixEnd_3429796 1761133894868168141076661 := by
  unfold tailWord_3429796
  simp only [CollatzResearch.WordTrace]
  refine ⟨62547468541221164683486621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83396624721628219577982161 62547468541221164683486621)
  ·
    refine ⟨23455300702957936756307483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62547468541221164683486621 23455300702957936756307483)
    ·
      refine ⟨35182951054436905134461225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23455300702957936756307483 35182951054436905134461225)
      ·
        refine ⟨26387213290827678850845919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35182951054436905134461225 26387213290827678850845919)
        ·
          refine ⟨39580819936241518276268879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26387213290827678850845919 39580819936241518276268879)
          ·
            refine ⟨59371229904362277414403319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39580819936241518276268879 59371229904362277414403319)
            ·
              refine ⟨89056844856543416121604979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59371229904362277414403319 89056844856543416121604979)
              ·
                refine ⟨133585267284815124182407469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89056844856543416121604979 133585267284815124182407469)
                ·
                  refine ⟨50094475231805671568402801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133585267284815124182407469 50094475231805671568402801)
                  ·
                    refine ⟨37570856423854253676302101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50094475231805671568402801 37570856423854253676302101)
                    ·
                      refine ⟨1761133894868168141076661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37570856423854253676302101 1761133894868168141076661)
                      ·
                        rfl

theorem cell23_3429796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_3429796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429796 prefixEnd_3429796 := by exact prefixLift 3429796
  have htrace : WordTrace (prefixWord ++ tailWord_3429796) baseStart_3429796 baseEnd_3429796 := by
    simpa [prefixWord, tailWord_3429796, baseEnd_3429796] using wordTrace_append hprefix tailTrace_3429796
  have hstable : (prefixWord ++ tailWord_3429796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429796).length < 2 ^ (prefixWord ++ tailWord_3429796).sum := by decide
  have hdescent : baseEnd_3429796 < baseStart_3429796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429803 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 3]
def baseStart_3429803 : Nat := 118140960795 + 3429803 * 2 ^ 59
def prefixEnd_3429803 : Nat := 4983230072969 + 3 ^ 40 * 3429803 * 2
def baseEnd_3429803 : Nat := 1761137489232749613689129

theorem tailTrace_3429803 : CollatzResearch.WordTrace tailWord_3429803 prefixEnd_3429803 1761137489232749613689129 := by
  unfold tailWord_3429803
  simp only [CollatzResearch.WordTrace]
  refine ⟨125095192393416969562478063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83396794928944646374985375 125095192393416969562478063)
  ·
    refine ⟨187642788590125454343717095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125095192393416969562478063 187642788590125454343717095)
    ·
      refine ⟨281464182885188181515575643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187642788590125454343717095 281464182885188181515575643)
      ·
        refine ⟨422196274327782272273363465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281464182885188181515575643 422196274327782272273363465)
        ·
          refine ⟨316647205745836704205022599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422196274327782272273363465 316647205745836704205022599)
          ·
            refine ⟨474970808618755056307533899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316647205745836704205022599 474970808618755056307533899)
            ·
              refine ⟨712456212928132584461300849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474970808618755056307533899 712456212928132584461300849)
              ·
                refine ⟨534342159696099438345975637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712456212928132584461300849 534342159696099438345975637)
                ·
                  refine ⟨3130911091969332646558451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 534342159696099438345975637 3130911091969332646558451)
                  ·
                    refine ⟨4696366637953998969837677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130911091969332646558451 4696366637953998969837677)
                    ·
                      refine ⟨1761137489232749613689129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696366637953998969837677 1761137489232749613689129)
                      ·
                        rfl

theorem cell23_3429803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 9, 1, 3].length) (baseStart_3429803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429803 prefixEnd_3429803 := by exact prefixLift 3429803
  have htrace : WordTrace (prefixWord ++ tailWord_3429803) baseStart_3429803 baseEnd_3429803 := by
    simpa [prefixWord, tailWord_3429803, baseEnd_3429803] using wordTrace_append hprefix tailTrace_3429803
  have hstable : (prefixWord ++ tailWord_3429803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429803).length < 2 ^ (prefixWord ++ tailWord_3429803).sum := by decide
  have hdescent : baseEnd_3429803 < baseStart_3429803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429844 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 6]
def baseStart_3429844 : Nat := 118140960795 + 3429844 * 2 ^ 59
def prefixEnd_3429844 : Nat := 4983230072969 + 3 ^ 40 * 3429844 * 2
def baseEnd_3429844 : Nat := 195684282437731550364049

theorem tailTrace_3429844 : CollatzResearch.WordTrace tailWord_3429844 prefixEnd_3429844 195684282437731550364049 := by
  unfold tailWord_3429844
  simp only [CollatzResearch.WordTrace]
  refine ⟨62548343893134216782360293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83397791857512289043147057 62548343893134216782360293)
  ·
    refine ⟨11727814479962665646692555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62548343893134216782360293 11727814479962665646692555)
    ·
      refine ⟨17591721719943998470038833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11727814479962665646692555 17591721719943998470038833)
      ·
        refine ⟨13193791289957998852529125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17591721719943998470038833 13193791289957998852529125)
        ·
          refine ⟨2473835866867124784849211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13193791289957998852529125 2473835866867124784849211)
          ·
            refine ⟨3710753800300687177273817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473835866867124784849211 3710753800300687177273817)
            ·
              refine ⟨2783065350225515382955363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710753800300687177273817 2783065350225515382955363)
              ·
                refine ⟨4174598025338273074433045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783065350225515382955363 4174598025338273074433045)
                ·
                  refine ⟨195684282437731550364049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4174598025338273074433045 195684282437731550364049)
                  ·
                    rfl

theorem cell23_3429844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_3429844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429844 prefixEnd_3429844 := by exact prefixLift 3429844
  have htrace : WordTrace (prefixWord ++ tailWord_3429844) baseStart_3429844 baseEnd_3429844 := by
    simpa [prefixWord, tailWord_3429844, baseEnd_3429844] using wordTrace_append hprefix tailTrace_3429844
  have hstable : (prefixWord ++ tailWord_3429844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429844).length < 2 ^ (prefixWord ++ tailWord_3429844).sum := by decide
  have hdescent : baseEnd_3429844 < baseStart_3429844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429873 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3429873 : Nat := 118140960795 + 3429873 * 2 ^ 59
def prefixEnd_3429873 : Nat := 4983230072969 + 3 ^ 40 * 3429873 * 2
def baseEnd_3429873 : Nat := 1761173432878564339813807

theorem tailTrace_3429873 : CollatzResearch.WordTrace tailWord_3429873 prefixEnd_3429873 1761173432878564339813807 := by
  unfold tailWord_3429873
  simp only [CollatzResearch.WordTrace]
  refine ⟨125097745503163371517526273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83398497002108914345017515 125097745503163371517526273)
  ·
    refine ⟨93823309127372528638144705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125097745503163371517526273 93823309127372528638144705)
    ·
      refine ⟨70367481845529396478608529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93823309127372528638144705 70367481845529396478608529)
      ·
        refine ⟨52775611384147047358956397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70367481845529396478608529 52775611384147047358956397)
        ·
          refine ⟨19790854269055142759608649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52775611384147047358956397 19790854269055142759608649)
          ·
            refine ⟨14843140701791357069706487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19790854269055142759608649 14843140701791357069706487)
            ·
              refine ⟨22264711052687035604559731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14843140701791357069706487 22264711052687035604559731)
              ·
                refine ⟨33397066579030553406839597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22264711052687035604559731 33397066579030553406839597)
                ·
                  refine ⟨12523899967136457527564849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33397066579030553406839597 12523899967136457527564849)
                  ·
                    refine ⟨9392924975352343145673637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12523899967136457527564849 9392924975352343145673637)
                    ·
                      refine ⟨1761173432878564339813807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9392924975352343145673637 1761173432878564339813807)
                      ·
                        rfl

theorem cell23_3429873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3429873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429873 prefixEnd_3429873 := by exact prefixLift 3429873
  have htrace : WordTrace (prefixWord ++ tailWord_3429873) baseStart_3429873 baseEnd_3429873 := by
    simpa [prefixWord, tailWord_3429873, baseEnd_3429873] using wordTrace_append hprefix tailTrace_3429873
  have hstable : (prefixWord ++ tailWord_3429873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429873).length < 2 ^ (prefixWord ++ tailWord_3429873).sum := by decide
  have hdescent : baseEnd_3429873 < baseStart_3429873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429880 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_3429880 : Nat := 118140960795 + 3429880 * 2 ^ 59
def prefixEnd_3429880 : Nat := 4983230072969 + 3 ^ 40 * 3429880 * 2
def baseEnd_3429880 : Nat := 1761177027243145812426275

theorem tailTrace_3429880 : CollatzResearch.WordTrace tailWord_3429880 prefixEnd_3429880 1761177027243145812426275 := by
  unfold tailWord_3429880
  simp only [CollatzResearch.WordTrace]
  refine ⟨62549000407069005856515547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83398667209425341142020729 62549000407069005856515547)
  ·
    refine ⟨93823500610603508784773321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62549000407069005856515547 93823500610603508784773321)
    ·
      refine ⟨70367625457952631588579991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93823500610603508784773321 70367625457952631588579991)
      ·
        refine ⟨105551438186928947382869987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70367625457952631588579991 105551438186928947382869987)
        ·
          refine ⟨158327157280393421074304981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105551438186928947382869987 158327157280393421074304981)
          ·
            refine ⟨3710792748759220806429023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 158327157280393421074304981 3710792748759220806429023)
            ·
              refine ⟨5566189123138831209643535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710792748759220806429023 5566189123138831209643535)
              ·
                refine ⟨8349283684708246814465303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566189123138831209643535 8349283684708246814465303)
                ·
                  refine ⟨12523925527062370221697955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8349283684708246814465303 12523925527062370221697955)
                  ·
                    refine ⟨18785888290593555332546933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12523925527062370221697955 18785888290593555332546933)
                    ·
                      refine ⟨1761177027243145812426275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18785888290593555332546933 1761177027243145812426275)
                      ·
                        rfl

theorem cell23_3429880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_3429880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429880 prefixEnd_3429880 := by exact prefixLift 3429880
  have htrace : WordTrace (prefixWord ++ tailWord_3429880) baseStart_3429880 baseEnd_3429880 := by
    simpa [prefixWord, tailWord_3429880, baseEnd_3429880] using wordTrace_append hprefix tailTrace_3429880
  have hstable : (prefixWord ++ tailWord_3429880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429880).length < 2 ^ (prefixWord ++ tailWord_3429880).sum := by decide
  have hdescent : baseEnd_3429880 < baseStart_3429880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429893 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_3429893 : Nat := 118140960795 + 3429893 * 2 ^ 59
def prefixEnd_3429893 : Nat := 4983230072969 + 3 ^ 40 * 3429893 * 2
def baseEnd_3429893 : Nat := 1761183702491654261563715

theorem tailTrace_3429893 : CollatzResearch.WordTrace tailWord_3429893 prefixEnd_3429893 1761183702491654261563715 := by
  unfold tailWord_3429893
  simp only [CollatzResearch.WordTrace]
  refine ⟨125098474963090914933254333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83398983308727276622169555 125098474963090914933254333)
  ·
    refine ⟨46911928111159093099970375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125098474963090914933254333 46911928111159093099970375)
    ·
      refine ⟨70367892166738639649955563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46911928111159093099970375 70367892166738639649955563)
      ·
        refine ⟨105551838250107959474933345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70367892166738639649955563 105551838250107959474933345)
        ·
          refine ⟨79163878687580969606200009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105551838250107959474933345 79163878687580969606200009)
          ·
            refine ⟨59372909015685727204650007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79163878687580969606200009 59372909015685727204650007)
            ·
              refine ⟨89059363523528590806975011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59372909015685727204650007 89059363523528590806975011)
              ·
                refine ⟨133589045285292886210462517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89059363523528590806975011 133589045285292886210462517)
                ·
                  refine ⟨12523972995496208082230861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133589045285292886210462517 12523972995496208082230861)
                  ·
                    refine ⟨4696489873311078030836573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12523972995496208082230861 4696489873311078030836573)
                    ·
                      refine ⟨1761183702491654261563715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696489873311078030836573 1761183702491654261563715)
                      ·
                        rfl

theorem cell23_3429893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_3429893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429893 prefixEnd_3429893 := by exact prefixLift 3429893
  have htrace : WordTrace (prefixWord ++ tailWord_3429893) baseStart_3429893 baseEnd_3429893 := by
    simpa [prefixWord, tailWord_3429893, baseEnd_3429893] using wordTrace_append hprefix tailTrace_3429893
  have hstable : (prefixWord ++ tailWord_3429893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429893).length < 2 ^ (prefixWord ++ tailWord_3429893).sum := by decide
  have hdescent : baseEnd_3429893 < baseStart_3429893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429900 : List Nat := [2, 2, 1, 2, 5, 2, 1, 8]
def baseStart_3429900 : Nat := 118140960795 + 3429900 * 2 ^ 59
def prefixEnd_3429900 : Nat := 4983230072969 + 3 ^ 40 * 3429900 * 2
def baseEnd_3429900 : Nat := 65229159142823545710229

theorem tailTrace_3429900 : CollatzResearch.WordTrace tailWord_3429900 prefixEnd_3429900 65229159142823545710229 := by
  unfold tailWord_3429900
  simp only [CollatzResearch.WordTrace]
  refine ⟨62549365137032777564379577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83399153516043703419172769 62549365137032777564379577)
  ·
    refine ⟨46912023852774583173284683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62549365137032777564379577 46912023852774583173284683)
    ·
      refine ⟨70368035779161874759927025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46912023852774583173284683 70368035779161874759927025)
      ·
        refine ⟨52776026834371406069945269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70368035779161874759927025 52776026834371406069945269)
        ·
          refine ⟨4947752515722319319057369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52776026834371406069945269 4947752515722319319057369)
          ·
            refine ⟨3710814386791739489293027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4947752515722319319057369 3710814386791739489293027)
            ·
              refine ⟨5566221580187609233939541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710814386791739489293027 5566221580187609233939541)
              ·
                refine ⟨65229159142823545710229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5566221580187609233939541 65229159142823545710229)
                ·
                  rfl

theorem cell23_3429900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 8].length) (baseStart_3429900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429900 prefixEnd_3429900 := by exact prefixLift 3429900
  have htrace : WordTrace (prefixWord ++ tailWord_3429900) baseStart_3429900 baseEnd_3429900 := by
    simpa [prefixWord, tailWord_3429900, baseEnd_3429900] using wordTrace_append hprefix tailTrace_3429900
  have hstable : (prefixWord ++ tailWord_3429900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429900).length < 2 ^ (prefixWord ++ tailWord_3429900).sum := by decide
  have hdescent : baseEnd_3429900 < baseStart_3429900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429928 : List Nat := [2, 1, 5, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3429928 : Nat := 118140960795 + 3429928 * 2 ^ 59
def prefixEnd_3429928 : Nat := 4983230072969 + 3 ^ 40 * 3429928 * 2
def baseEnd_3429928 : Nat := 1761201674314561624626055

theorem tailTrace_3429928 : CollatzResearch.WordTrace tailWord_3429928 prefixEnd_3429928 1761201674314561624626055 := by
  unfold tailWord_3429928
  simp only [CollatzResearch.WordTrace]
  refine ⟨62549875758982057955389219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83399834345309410607185625 62549875758982057955389219)
  ·
    refine ⟨93824813638473086933083829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62549875758982057955389219 93824813638473086933083829)
    ·
      refine ⟨8796076278606851899976609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93824813638473086933083829 8796076278606851899976609)
      ·
        refine ⟨6597057208955138924982457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796076278606851899976609 6597057208955138924982457)
        ·
          refine ⟨4947792906716354193736843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597057208955138924982457 4947792906716354193736843)
          ·
            refine ⟨7421689360074531290605265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947792906716354193736843 7421689360074531290605265)
            ·
              refine ⟨5566267020055898467953949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7421689360074531290605265 5566267020055898467953949)
              ·
                refine ⟨2087350132520961925482731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5566267020055898467953949 2087350132520961925482731)
                ·
                  refine ⟨3131025198781442888224097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087350132520961925482731 3131025198781442888224097)
                  ·
                    refine ⟨2348268899086082166168073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3131025198781442888224097 2348268899086082166168073)
                    ·
                      refine ⟨1761201674314561624626055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2348268899086082166168073 1761201674314561624626055)
                      ·
                        rfl

theorem cell23_3429928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3429928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429928 prefixEnd_3429928 := by exact prefixLift 3429928
  have htrace : WordTrace (prefixWord ++ tailWord_3429928) baseStart_3429928 baseEnd_3429928 := by
    simpa [prefixWord, tailWord_3429928, baseEnd_3429928] using wordTrace_append hprefix tailTrace_3429928
  have hstable : (prefixWord ++ tailWord_3429928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429928).length < 2 ^ (prefixWord ++ tailWord_3429928).sum := by decide
  have hdescent : baseEnd_3429928 < baseStart_3429928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429943 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 2, 6]
def baseStart_3429943 : Nat := 118140960795 + 3429943 * 2 ^ 59
def prefixEnd_3429943 : Nat := 4983230072969 + 3 ^ 40 * 3429943 * 2
def baseEnd_3429943 : Nat := 587069792174793021979495

theorem tailTrace_3429943 : CollatzResearch.WordTrace tailWord_3429943 prefixEnd_3429943 587069792174793021979495 := by
  unfold tailWord_3429943
  simp only [CollatzResearch.WordTrace]
  refine ⟨125100298612909773472574483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83400199075273182315049655 125100298612909773472574483)
  ·
    refine ⟨187650447919364660208861725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125100298612909773472574483 187650447919364660208861725)
    ·
      refine ⟨70368917969761747578323147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187650447919364660208861725 70368917969761747578323147)
      ·
        refine ⟨105553376954642621367484721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70368917969761747578323147 105553376954642621367484721)
        ·
          refine ⟨79165032715981966025613541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105553376954642621367484721 79165032715981966025613541)
          ·
            refine ⟨14843443634246618629802539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79165032715981966025613541 14843443634246618629802539)
            ·
              refine ⟨22265165451369927944703809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14843443634246618629802539 22265165451369927944703809)
              ·
                refine ⟨16698874088527445958527857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22265165451369927944703809 16698874088527445958527857)
                ·
                  refine ⟨12524155566395584468895893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16698874088527445958527857 12524155566395584468895893)
                  ·
                    refine ⟨587069792174793021979495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12524155566395584468895893 587069792174793021979495)
                    ·
                      rfl

theorem cell23_3429943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_3429943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429943 prefixEnd_3429943 := by exact prefixLift 3429943
  have htrace : WordTrace (prefixWord ++ tailWord_3429943) baseStart_3429943 baseEnd_3429943 := by
    simpa [prefixWord, tailWord_3429943, baseEnd_3429943] using wordTrace_append hprefix tailTrace_3429943
  have hstable : (prefixWord ++ tailWord_3429943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429943).length < 2 ^ (prefixWord ++ tailWord_3429943).sum := by decide
  have hdescent : baseEnd_3429943 < baseStart_3429943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3429944 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_3429944 : Nat := 118140960795 + 3429944 * 2 ^ 59
def prefixEnd_3429944 : Nat := 4983230072969 + 3 ^ 40 * 3429944 * 2
def baseEnd_3429944 : Nat := 1761209890005033562025981

theorem tailTrace_3429944 : CollatzResearch.WordTrace tailWord_3429944 prefixEnd_3429944 1761209890005033562025981 := by
  unfold tailWord_3429944
  simp only [CollatzResearch.WordTrace]
  refine ⟨62550167542953075321680443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83400223390604100428907257 62550167542953075321680443)
  ·
    refine ⟨93825251314429612982520665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62550167542953075321680443 93825251314429612982520665)
    ·
      refine ⟨70368938485822209736890499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93825251314429612982520665 70368938485822209736890499)
      ·
        refine ⟨105553407728733314605335749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70368938485822209736890499 105553407728733314605335749)
        ·
          refine ⟨19791263949137496488500453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105553407728733314605335749 19791263949137496488500453)
          ·
            refine ⟨3710861990463280591593835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19791263949137496488500453 3710861990463280591593835)
            ·
              refine ⟨5566292985694920887390753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3710861990463280591593835 5566292985694920887390753)
              ·
                refine ⟨4174719739271190665543065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5566292985694920887390753 4174719739271190665543065)
                ·
                  refine ⟨3131039804453392999157299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4174719739271190665543065 3131039804453392999157299)
                  ·
                    refine ⟨4696559706680089498735949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3131039804453392999157299 4696559706680089498735949)
                    ·
                      refine ⟨1761209890005033562025981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4696559706680089498735949 1761209890005033562025981)
                      ·
                        rfl

theorem cell23_3429944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_3429944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3429944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3429944 prefixEnd_3429944 := by exact prefixLift 3429944
  have htrace : WordTrace (prefixWord ++ tailWord_3429944) baseStart_3429944 baseEnd_3429944 := by
    simpa [prefixWord, tailWord_3429944, baseEnd_3429944] using wordTrace_append hprefix tailTrace_3429944
  have hstable : (prefixWord ++ tailWord_3429944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3429944).length < 2 ^ (prefixWord ++ tailWord_3429944).sum := by decide
  have hdescent : baseEnd_3429944 < baseStart_3429944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3429944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
