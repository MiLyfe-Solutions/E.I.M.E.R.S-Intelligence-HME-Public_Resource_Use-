import V185TrunkScan22Chunk276

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2468841 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2468841 : Nat := 118140960795 + 2468841 * 2 ^ 59
def prefixEnd_2468841 : Nat := 4983230072969 + 3 ^ 40 * 2468841 * 2
def baseEnd_2468841 : Nat := 845134728351253587955675

theorem tailTrace_2468841 : CollatzResearch.WordTrace tailWord_2468841 prefixEnd_2468841 845134728351253587955675 := by
  unfold tailWord_2468841
  simp only [CollatzResearch.WordTrace]
  refine ⟨90046028848818176319078377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60030685899212117546052251 90046028848818176319078377)
  ·
    refine ⟨67534521636613632239308783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90046028848818176319078377 67534521636613632239308783)
    ·
      refine ⟨101301782454920448358963175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67534521636613632239308783 101301782454920448358963175)
      ·
        refine ⟨151952673682380672538444763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101301782454920448358963175 151952673682380672538444763)
        ·
          refine ⟨227929010523571008807667145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151952673682380672538444763 227929010523571008807667145)
          ·
            refine ⟨170946757892678256605750359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227929010523571008807667145 170946757892678256605750359)
            ·
              refine ⟨256420136839017384908625539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170946757892678256605750359 256420136839017384908625539)
              ·
                refine ⟨384630205258526077362938309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256420136839017384908625539 384630205258526077362938309)
                ·
                  refine ⟨72118163485973639505550933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 384630205258526077362938309 72118163485973639505550933)
                  ·
                    refine ⟨845134728351253587955675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72118163485973639505550933 845134728351253587955675)
                    ·
                      rfl

theorem cell22_2468841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2468841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468841 prefixEnd_2468841 := by exact prefixLift 2468841
  have htrace : WordTrace (prefixWord ++ tailWord_2468841) baseStart_2468841 baseEnd_2468841 := by
    simpa [prefixWord, tailWord_2468841, baseEnd_2468841] using wordTrace_append hprefix tailTrace_2468841
  have hstable : (prefixWord ++ tailWord_2468841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468841).length < 2 ^ (prefixWord ++ tailWord_2468841).sum := by decide
  have hdescent : baseEnd_2468841 < baseStart_2468841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468849 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 1, 3]
def baseStart_2468849 : Nat := 118140960795 + 2468849 * 2 ^ 59
def prefixEnd_2468849 : Nat := 4983230072969 + 3 ^ 40 * 2468849 * 2
def baseEnd_2468849 : Nat := 845137466914744233755651

theorem tailTrace_2468849 : CollatzResearch.WordTrace tailWord_2468849 prefixEnd_2468849 845137466914744233755651 := by
  unfold tailWord_2468849
  simp only [CollatzResearch.WordTrace]
  refine ⟨90046320632789193685369601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60030880421859462456913067 90046320632789193685369601)
  ·
    refine ⟨67534740474591895264027201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90046320632789193685369601 67534740474591895264027201)
    ·
      refine ⟨50651055355943921448020401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67534740474591895264027201 50651055355943921448020401)
      ·
        refine ⟨37988291516957941086015301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50651055355943921448020401 37988291516957941086015301)
        ·
          refine ⟨7122804659429613953627869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37988291516957941086015301 7122804659429613953627869)
          ·
            refine ⟨2671051747286105232610451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7122804659429613953627869 2671051747286105232610451)
            ·
              refine ⟨4006577620929157848915677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671051747286105232610451 4006577620929157848915677)
              ·
                refine ⟨1502466607848434193343379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4006577620929157848915677 1502466607848434193343379)
                ·
                  refine ⟨2253699911772651290015069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502466607848434193343379 2253699911772651290015069)
                  ·
                    refine ⟨845137466914744233755651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253699911772651290015069 845137466914744233755651)
                    ·
                      rfl

theorem cell22_2468849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_2468849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468849 prefixEnd_2468849 := by exact prefixLift 2468849
  have htrace : WordTrace (prefixWord ++ tailWord_2468849) baseStart_2468849 baseEnd_2468849 := by
    simpa [prefixWord, tailWord_2468849, baseEnd_2468849] using wordTrace_append hprefix tailTrace_2468849
  have hstable : (prefixWord ++ tailWord_2468849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468849).length < 2 ^ (prefixWord ++ tailWord_2468849).sum := by decide
  have hdescent : baseEnd_2468849 < baseStart_2468849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468866 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2468866 : Nat := 118140960795 + 2468866 * 2 ^ 59
def prefixEnd_2468866 : Nat := 4983230072969 + 3 ^ 40 * 2468866 * 2
def baseEnd_2468866 : Nat := 845143286362161856080599

theorem tailTrace_2468866 : CollatzResearch.WordTrace tailWord_2468866 prefixEnd_2468866 845143286362161856080599 := by
  unfold tailWord_2468866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22511735168431901397184613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60031293782485070392492301 22511735168431901397184613)
  ·
    refine ⟨4220950344080981511972115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22511735168431901397184613 4220950344080981511972115)
    ·
      refine ⟨6331425516121472267958173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4220950344080981511972115 6331425516121472267958173)
      ·
        refine ⟨2374284568545552100484315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6331425516121472267958173 2374284568545552100484315)
        ·
          refine ⟨3561426852818328150726473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374284568545552100484315 3561426852818328150726473)
          ·
            refine ⟨2671070139613746113044855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561426852818328150726473 2671070139613746113044855)
            ·
              refine ⟨4006605209420619169567283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671070139613746113044855 4006605209420619169567283)
              ·
                refine ⟨6009907814130928754350925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006605209420619169567283 6009907814130928754350925)
                ·
                  refine ⟨2253715430299098282881597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6009907814130928754350925 2253715430299098282881597)
                  ·
                    refine ⟨845143286362161856080599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253715430299098282881597 845143286362161856080599)
                    ·
                      rfl

theorem cell22_2468866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2468866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468866 prefixEnd_2468866 := by exact prefixLift 2468866
  have htrace : WordTrace (prefixWord ++ tailWord_2468866) baseStart_2468866 baseEnd_2468866 := by
    simpa [prefixWord, tailWord_2468866, baseEnd_2468866] using wordTrace_append hprefix tailTrace_2468866
  have hstable : (prefixWord ++ tailWord_2468866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468866).length < 2 ^ (prefixWord ++ tailWord_2468866).sum := by decide
  have hdescent : baseEnd_2468866 < baseStart_2468866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468920 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_2468920 : Nat := 118140960795 + 2468920 * 2 ^ 59
def prefixEnd_2468920 : Nat := 4983230072969 + 3 ^ 40 * 2468920 * 2
def baseEnd_2468920 : Nat := 845161771665723715230433

theorem tailTrace_2468920 : CollatzResearch.WordTrace tailWord_2468920 prefixEnd_2468920 845161771665723715230433 := by
  unfold tailWord_2468920
  simp only [CollatzResearch.WordTrace]
  refine ⟨45024455107765986405602107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60032606810354648540802809 45024455107765986405602107)
  ·
    refine ⟨67536682661648979608403161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45024455107765986405602107 67536682661648979608403161)
    ·
      refine ⟨50652511996236734706302371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67536682661648979608403161 50652511996236734706302371)
      ·
        refine ⟨75978767994355102059453557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50652511996236734706302371 75978767994355102059453557)
        ·
          refine ⟨7123009499470790818073771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75978767994355102059453557 7123009499470790818073771)
          ·
            refine ⟨10684514249206186227110657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7123009499470790818073771 10684514249206186227110657)
            ·
              refine ⟨8013385686904639670332993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10684514249206186227110657 8013385686904639670332993)
              ·
                refine ⟨6010039265178479752749745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8013385686904639670332993 6010039265178479752749745)
                ·
                  refine ⟨4507529448883859814562309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6010039265178479752749745 4507529448883859814562309)
                  ·
                    refine ⟨845161771665723715230433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4507529448883859814562309 845161771665723715230433)
                    ·
                      rfl

theorem cell22_2468920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_2468920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468920 prefixEnd_2468920 := by exact prefixLift 2468920
  have htrace : WordTrace (prefixWord ++ tailWord_2468920) baseStart_2468920 baseEnd_2468920 := by
    simpa [prefixWord, tailWord_2468920, baseEnd_2468920] using wordTrace_append hprefix tailTrace_2468920
  have hstable : (prefixWord ++ tailWord_2468920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468920).length < 2 ^ (prefixWord ++ tailWord_2468920).sum := by decide
  have hdescent : baseEnd_2468920 < baseStart_2468920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468924 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 4]
def baseStart_2468924 : Nat := 118140960795 + 2468924 * 2 ^ 59
def prefixEnd_2468924 : Nat := 4983230072969 + 3 ^ 40 * 2468924 * 2
def baseEnd_2468924 : Nat := 281721046982489679376807

theorem tailTrace_2468924 : CollatzResearch.WordTrace tailWord_2468924 prefixEnd_2468924 281721046982489679376807 := by
  unfold tailWord_2468924
  simp only [CollatzResearch.WordTrace]
  refine ⟨45024528053758740747174913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60032704071678320996233217 45024528053758740747174913)
  ·
    refine ⟨33768396040319055560381185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45024528053758740747174913 33768396040319055560381185)
    ·
      refine ⟨25326297030239291670285889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33768396040319055560381185 25326297030239291670285889)
      ·
        refine ⟨18994722772679468752714417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25326297030239291670285889 18994722772679468752714417)
        ·
          refine ⟨14246042079509601564535813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18994722772679468752714417 14246042079509601564535813)
          ·
            refine ⟨2671132889908050293350465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14246042079509601564535813 2671132889908050293350465)
            ·
              refine ⟨2003349667431037720012849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671132889908050293350465 2003349667431037720012849)
              ·
                refine ⟨1502512250573278290009637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003349667431037720012849 1502512250573278290009637)
                ·
                  refine ⟨281721046982489679376807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502512250573278290009637 281721046982489679376807)
                  ·
                    rfl

theorem cell22_2468924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_2468924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468924 prefixEnd_2468924 := by exact prefixLift 2468924
  have htrace : WordTrace (prefixWord ++ tailWord_2468924) baseStart_2468924 baseEnd_2468924 := by
    simpa [prefixWord, tailWord_2468924, baseEnd_2468924] using wordTrace_append hprefix tailTrace_2468924
  have hstable : (prefixWord ++ tailWord_2468924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468924).length < 2 ^ (prefixWord ++ tailWord_2468924).sum := by decide
  have hdescent : baseEnd_2468924 < baseStart_2468924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468935 : List Nat := [1, 1, 4, 1, 3, 4, 1, 7]
def baseStart_2468935 : Nat := 118140960795 + 2468935 * 2 ^ 59
def prefixEnd_2468935 : Nat := 4983230072969 + 3 ^ 40 * 2468935 * 2
def baseEnd_2468935 : Nat := 93907434052474297345043

theorem tailTrace_2468935 : CollatzResearch.WordTrace tailWord_2468935 prefixEnd_2468935 93907434052474297345043 := by
  unfold tailWord_2468935
  simp only [CollatzResearch.WordTrace]
  refine ⟨90049457310477630373000259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60032971540318420248666839 90049457310477630373000259)
  ·
    refine ⟨135074185965716445559500389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90049457310477630373000259 135074185965716445559500389)
    ·
      refine ⟨25326409868571833542406323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135074185965716445559500389 25326409868571833542406323)
      ·
        refine ⟨37989614802857750313609485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25326409868571833542406323 37989614802857750313609485)
        ·
          refine ⟨14246105551071656367603557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37989614802857750313609485 14246105551071656367603557)
          ·
            refine ⟨2671144790825935568925667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14246105551071656367603557 2671144790825935568925667)
            ·
              refine ⟨4006717186238903353388501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671144790825935568925667 4006717186238903353388501)
              ·
                refine ⟨93907434052474297345043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4006717186238903353388501 93907434052474297345043)
                ·
                  rfl

theorem cell22_2468935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 7].length) (baseStart_2468935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468935 prefixEnd_2468935 := by exact prefixLift 2468935
  have htrace : WordTrace (prefixWord ++ tailWord_2468935) baseStart_2468935 baseEnd_2468935 := by
    simpa [prefixWord, tailWord_2468935, baseEnd_2468935] using wordTrace_append hprefix tailTrace_2468935
  have hstable : (prefixWord ++ tailWord_2468935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468935).length < 2 ^ (prefixWord ++ tailWord_2468935).sum := by decide
  have hdescent : baseEnd_2468935 < baseStart_2468935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468963 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 7]
def baseStart_2468963 : Nat := 118140960795 + 2468963 * 2 ^ 59
def prefixEnd_2468963 : Nat := 4983230072969 + 3 ^ 40 * 2468963 * 2
def baseEnd_2468963 : Nat := 281725497148161978801767

theorem tailTrace_2468963 : CollatzResearch.WordTrace tailWord_2468963 prefixEnd_2468963 281725497148161978801767 := by
  unfold tailWord_2468963
  simp only [CollatzResearch.WordTrace]
  refine ⟨90050478554376191155019543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60033652369584127436679695 90050478554376191155019543)
  ·
    refine ⟨135075717831564286732529315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90050478554376191155019543 135075717831564286732529315)
    ·
      refine ⟨202613576747346430098793973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135075717831564286732529315 202613576747346430098793973)
      ·
        refine ⟨18995022820063727821761935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202613576747346430098793973 18995022820063727821761935)
        ·
          refine ⟨28492534230095591732642903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18995022820063727821761935 28492534230095591732642903)
          ·
            refine ⟨42738801345143387598964355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28492534230095591732642903 42738801345143387598964355)
            ·
              refine ⟨64108202017715081398446533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42738801345143387598964355 64108202017715081398446533)
              ·
                refine ⟨12020287878321577762208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64108202017715081398446533 12020287878321577762208725)
                ·
                  refine ⟨281725497148161978801767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12020287878321577762208725 281725497148161978801767)
                  ·
                    rfl

theorem cell22_2468963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_2468963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468963 prefixEnd_2468963 := by exact prefixLift 2468963
  have htrace : WordTrace (prefixWord ++ tailWord_2468963) baseStart_2468963 baseEnd_2468963 := by
    simpa [prefixWord, tailWord_2468963, baseEnd_2468963] using wordTrace_append hprefix tailTrace_2468963
  have hstable : (prefixWord ++ tailWord_2468963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468963).length < 2 ^ (prefixWord ++ tailWord_2468963).sum := by decide
  have hdescent : baseEnd_2468963 < baseStart_2468963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2468990 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2468990 : Nat := 118140960795 + 2468990 * 2 ^ 59
def prefixEnd_2468990 : Nat := 4983230072969 + 3 ^ 40 * 2468990 * 2
def baseEnd_2468990 : Nat := 845185734096266865980219

theorem tailTrace_2468990 : CollatzResearch.WordTrace tailWord_2468990 prefixEnd_2468990 845185734096266865980219 := by
  unfold tailWord_2468990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256432915659796845781553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60034308883518916510834949 11256432915659796845781553)
  ·
    refine ⟨8442324686744847634336165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11256432915659796845781553 8442324686744847634336165)
    ·
      refine ⟨1582935878764658931438031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8442324686744847634336165 1582935878764658931438031)
      ·
        refine ⟨2374403818146988397157047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582935878764658931438031 2374403818146988397157047)
        ·
          refine ⟨3561605727220482595735571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374403818146988397157047 3561605727220482595735571)
          ·
            refine ⟨5342408590830723893603357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561605727220482595735571 5342408590830723893603357)
            ·
              refine ⟨2003403221561521460101259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342408590830723893603357 2003403221561521460101259)
              ·
                refine ⟨3005104832342282190151889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003403221561521460101259 3005104832342282190151889)
                ·
                  refine ⟨2253828624256711642613917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3005104832342282190151889 2253828624256711642613917)
                  ·
                    refine ⟨845185734096266865980219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2253828624256711642613917 845185734096266865980219)
                    ·
                      rfl

theorem cell22_2468990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2468990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2468990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2468990 prefixEnd_2468990 := by exact prefixLift 2468990
  have htrace : WordTrace (prefixWord ++ tailWord_2468990) baseStart_2468990 baseEnd_2468990 := by
    simpa [prefixWord, tailWord_2468990, baseEnd_2468990] using wordTrace_append hprefix tailTrace_2468990
  have hstable : (prefixWord ++ tailWord_2468990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2468990).length < 2 ^ (prefixWord ++ tailWord_2468990).sum := by decide
  have hdescent : baseEnd_2468990 < baseStart_2468990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2468990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469008 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_2469008 : Nat := 118140960795 + 2469008 * 2 ^ 59
def prefixEnd_2469008 : Nat := 4983230072969 + 3 ^ 40 * 2469008 * 2
def baseEnd_2469008 : Nat := 281730631954706939676721

theorem tailTrace_2469008 : CollatzResearch.WordTrace tailWord_2469008 prefixEnd_2469008 281730631954706939676721 := by
  unfold tailWord_2469008
  simp only [CollatzResearch.WordTrace]
  refine ⟨45026059919606581920203839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60034746559475442560271785 45026059919606581920203839)
  ·
    refine ⟨67539089879409872880305759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45026059919606581920203839 67539089879409872880305759)
    ·
      refine ⟨101308634819114809320458639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67539089879409872880305759 101308634819114809320458639)
      ·
        refine ⟨151962952228672213980687959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101308634819114809320458639 151962952228672213980687959)
        ·
          refine ⟨227944428343008320971031939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151962952228672213980687959 227944428343008320971031939)
          ·
            refine ⟨341916642514512481456547909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227944428343008320971031939 341916642514512481456547909)
            ·
              refine ⟨64109370471471090273102733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341916642514512481456547909 64109370471471090273102733)
              ·
                refine ⟨24041013926801658852413525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64109370471471090273102733 24041013926801658852413525)
                ·
                  refine ⟨281730631954706939676721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24041013926801658852413525 281730631954706939676721)
                  ·
                    rfl

theorem cell22_2469008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_2469008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469008 prefixEnd_2469008 := by exact prefixLift 2469008
  have htrace : WordTrace (prefixWord ++ tailWord_2469008) baseStart_2469008 baseEnd_2469008 := by
    simpa [prefixWord, tailWord_2469008, baseEnd_2469008] using wordTrace_append hprefix tailTrace_2469008
  have hstable : (prefixWord ++ tailWord_2469008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469008).length < 2 ^ (prefixWord ++ tailWord_2469008).sum := by decide
  have hdescent : baseEnd_2469008 < baseStart_2469008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469042 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_2469042 : Nat := 118140960795 + 2469042 * 2 ^ 59
def prefixEnd_2469042 : Nat := 4983230072969 + 3 ^ 40 * 2469042 * 2
def baseEnd_2469042 : Nat := 281734511586318687893353

theorem tailTrace_2469042 : CollatzResearch.WordTrace tailWord_2469042 prefixEnd_2469042 281734511586318687893353 := by
  unfold tailWord_2469042
  simp only [CollatzResearch.WordTrace]
  refine ⟨22513339980272496911786345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60035573280726658431430253 22513339980272496911786345)
  ·
    refine ⟨16885004985204372683839759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22513339980272496911786345 16885004985204372683839759)
    ·
      refine ⟨25327507477806559025759639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16885004985204372683839759 25327507477806559025759639)
      ·
        refine ⟨37991261216709838538639459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25327507477806559025759639 37991261216709838538639459)
        ·
          refine ⟨56986891825064757807959189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37991261216709838538639459 56986891825064757807959189)
          ·
            refine ⟨2671260554299910522248087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56986891825064757807959189 2671260554299910522248087)
            ·
              refine ⟨4006890831449865783372131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671260554299910522248087 4006890831449865783372131)
              ·
                refine ⟨6010336247174798675058197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006890831449865783372131 6010336247174798675058197)
                ·
                  refine ⟨281734511586318687893353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6010336247174798675058197 281734511586318687893353)
                  ·
                    rfl

theorem cell22_2469042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_2469042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469042 prefixEnd_2469042 := by exact prefixLift 2469042
  have htrace : WordTrace (prefixWord ++ tailWord_2469042) baseStart_2469042 baseEnd_2469042 := by
    simpa [prefixWord, tailWord_2469042, baseEnd_2469042] using wordTrace_append hprefix tailTrace_2469042
  have hstable : (prefixWord ++ tailWord_2469042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469042).length < 2 ^ (prefixWord ++ tailWord_2469042).sum := by decide
  have hdescent : baseEnd_2469042 < baseStart_2469042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469078 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2469078 : Nat := 118140960795 + 2469078 * 2 ^ 59
def prefixEnd_2469078 : Nat := 4983230072969 + 3 ^ 40 * 2469078 * 2
def baseEnd_2469078 : Nat := 845215858294663969779949

theorem tailTrace_2469078 : CollatzResearch.WordTrace tailWord_2469078 prefixEnd_2469078 845215858294663969779949 := by
  unfold tailWord_2469078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628417059309972862215993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60036448632639710530303925 5628417059309972862215993)
  ·
    refine ⟨4221312794482479646661995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5628417059309972862215993 4221312794482479646661995)
    ·
      refine ⟨6331969191723719469992993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4221312794482479646661995 6331969191723719469992993)
      ·
        refine ⟨4748976893792789602494745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6331969191723719469992993 4748976893792789602494745)
        ·
          refine ⟨3561732670344592201871059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4748976893792789602494745 3561732670344592201871059)
          ·
            refine ⟨5342599005516888302806589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561732670344592201871059 5342599005516888302806589)
            ·
              refine ⟨2003474627068833113552471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5342599005516888302806589 2003474627068833113552471)
              ·
                refine ⟨3005211940603249670328707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003474627068833113552471 3005211940603249670328707)
                ·
                  refine ⟨4507817910904874505493061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005211940603249670328707 4507817910904874505493061)
                  ·
                    refine ⟨845215858294663969779949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4507817910904874505493061 845215858294663969779949)
                    ·
                      rfl

theorem cell22_2469078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2469078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469078 prefixEnd_2469078 := by exact prefixLift 2469078
  have htrace : WordTrace (prefixWord ++ tailWord_2469078) baseStart_2469078 baseEnd_2469078 := by
    simpa [prefixWord, tailWord_2469078, baseEnd_2469078] using wordTrace_append hprefix tailTrace_2469078
  have hstable : (prefixWord ++ tailWord_2469078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469078).length < 2 ^ (prefixWord ++ tailWord_2469078).sum := by decide
  have hdescent : baseEnd_2469078 < baseStart_2469078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469093 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 4]
def baseStart_2469093 : Nat := 118140960795 + 2469093 * 2 ^ 59
def prefixEnd_2469093 : Nat := 4983230072969 + 3 ^ 40 * 2469093 * 2
def baseEnd_2469093 : Nat := 281740331033736310218301

theorem tailTrace_2469093 : CollatzResearch.WordTrace tailWord_2469093 prefixEnd_2469093 281740331033736310218301 := by
  unfold tailWord_2469093
  simp only [CollatzResearch.WordTrace]
  refine ⟨90055220043905223357251933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60036813362603482238167955 90055220043905223357251933)
  ·
    refine ⟨33770707516464458758969475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90055220043905223357251933 33770707516464458758969475)
    ·
      refine ⟨50656061274696688138454213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33770707516464458758969475 50656061274696688138454213)
      ·
        refine ⟨9498011489005629025960165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50656061274696688138454213 9498011489005629025960165)
        ·
          refine ⟨1780877154188555442367531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9498011489005629025960165 1780877154188555442367531)
          ·
            refine ⟨2671315731282833163551297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780877154188555442367531 2671315731282833163551297)
            ·
              refine ⟨2003486798462124872663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671315731282833163551297 2003486798462124872663473)
              ·
                refine ⟨1502615098846593654497605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003486798462124872663473 1502615098846593654497605)
                ·
                  refine ⟨281740331033736310218301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502615098846593654497605 281740331033736310218301)
                  ·
                    rfl

theorem cell22_2469093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_2469093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469093 prefixEnd_2469093 := by exact prefixLift 2469093
  have htrace : WordTrace (prefixWord ++ tailWord_2469093) baseStart_2469093 baseEnd_2469093 := by
    simpa [prefixWord, tailWord_2469093, baseEnd_2469093] using wordTrace_append hprefix tailTrace_2469093
  have hstable : (prefixWord ++ tailWord_2469093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469093).length < 2 ^ (prefixWord ++ tailWord_2469093).sum := by decide
  have hdescent : baseEnd_2469093 < baseStart_2469093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469100 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2469100 : Nat := 118140960795 + 2469100 * 2 ^ 59
def prefixEnd_2469100 : Nat := 4983230072969 + 3 ^ 40 * 2469100 * 2
def baseEnd_2469100 : Nat := 845223389344263245729881

theorem tailTrace_2469100 : CollatzResearch.WordTrace tailWord_2469100 prefixEnd_2469100 845223389344263245729881 := by
  unfold tailWord_2469100
  simp only [CollatzResearch.WordTrace]
  refine ⟨45027737677439931776378377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60036983569919909035171169 45027737677439931776378377)
  ·
    refine ⟨33770803258079948832283783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45027737677439931776378377 33770803258079948832283783)
    ·
      refine ⟨50656204887119923248425675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33770803258079948832283783 50656204887119923248425675)
      ·
        refine ⟨75984307330679884872638513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50656204887119923248425675 75984307330679884872638513)
        ·
          refine ⟨56988230498009913654478885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75984307330679884872638513 56988230498009913654478885)
          ·
            refine ⟨10685293218376858810214791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56988230498009913654478885 10685293218376858810214791)
            ·
              refine ⟨16027939827565288215322187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10685293218376858810214791 16027939827565288215322187)
              ·
                refine ⟨24041909741347932322983281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16027939827565288215322187 24041909741347932322983281)
                ·
                  refine ⟨18031432306010949242237461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24041909741347932322983281 18031432306010949242237461)
                  ·
                    refine ⟨845223389344263245729881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18031432306010949242237461 845223389344263245729881)
                    ·
                      rfl

theorem cell22_2469100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2469100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469100 prefixEnd_2469100 := by exact prefixLift 2469100
  have htrace : WordTrace (prefixWord ++ tailWord_2469100) baseStart_2469100 baseEnd_2469100 := by
    simpa [prefixWord, tailWord_2469100, baseEnd_2469100] using wordTrace_append hprefix tailTrace_2469100
  have hstable : (prefixWord ++ tailWord_2469100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469100).length < 2 ^ (prefixWord ++ tailWord_2469100).sum := by decide
  have hdescent : baseEnd_2469100 < baseStart_2469100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469108 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_2469108 : Nat := 118140960795 + 2469108 * 2 ^ 59
def prefixEnd_2469108 : Nat := 4983230072969 + 3 ^ 40 * 2469108 * 2
def baseEnd_2469108 : Nat := 845226127907753891529857

theorem tailTrace_2469108 : CollatzResearch.WordTrace tailWord_2469108 prefixEnd_2469108 845226127907753891529857 := by
  unfold tailWord_2469108
  simp only [CollatzResearch.WordTrace]
  refine ⟨45027883569425440459523989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60037178092567253946031985 45027883569425440459523989)
  ·
    refine ⟨2110682042316817521540187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45027883569425440459523989 2110682042316817521540187)
    ·
      refine ⟨3166023063475226282310281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110682042316817521540187 3166023063475226282310281)
      ·
        refine ⟨2374517297606419711732711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3166023063475226282310281 2374517297606419711732711)
        ·
          refine ⟨3561775946409629567599067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374517297606419711732711 3561775946409629567599067)
          ·
            refine ⟨5342663919614444351398601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3561775946409629567599067 5342663919614444351398601)
            ·
              refine ⟨4006997939710833263548951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5342663919614444351398601 4006997939710833263548951)
              ·
                refine ⟨6010496909566249895323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4006997939710833263548951 6010496909566249895323427)
                ·
                  refine ⟨9015745364349374842985141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6010496909566249895323427 9015745364349374842985141)
                  ·
                    refine ⟨845226127907753891529857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9015745364349374842985141 845226127907753891529857)
                    ·
                      rfl

theorem cell22_2469108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_2469108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469108 prefixEnd_2469108 := by exact prefixLift 2469108
  have htrace : WordTrace (prefixWord ++ tailWord_2469108) baseStart_2469108 baseEnd_2469108 := by
    simpa [prefixWord, tailWord_2469108, baseEnd_2469108] using wordTrace_append hprefix tailTrace_2469108
  have hstable : (prefixWord ++ tailWord_2469108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469108).length < 2 ^ (prefixWord ++ tailWord_2469108).sum := by decide
  have hdescent : baseEnd_2469108 < baseStart_2469108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469130 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2469130 : Nat := 118140960795 + 2469130 * 2 ^ 59
def prefixEnd_2469130 : Nat := 4983230072969 + 3 ^ 40 * 2469130 * 2
def baseEnd_2469130 : Nat := 845233658957353167479789

theorem tailTrace_2469130 : CollatzResearch.WordTrace tailWord_2469130 prefixEnd_2469130 845233658957353167479789 := by
  unfold tailWord_2469130
  simp only [CollatzResearch.WordTrace]
  refine ⟨22514142386192794669087211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60037713029847452450899229 22514142386192794669087211)
  ·
    refine ⟨33771213579289192003630817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22514142386192794669087211 33771213579289192003630817)
    ·
      refine ⟨25328410184466894002723113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33771213579289192003630817 25328410184466894002723113)
      ·
        refine ⟨18996307638350170502042335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25328410184466894002723113 18996307638350170502042335)
        ·
          refine ⟨28494461457525255753063503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18996307638350170502042335 28494461457525255753063503)
          ·
            refine ⟨42741692186287883629595255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28494461457525255753063503 42741692186287883629595255)
            ·
              refine ⟨64112538279431825444392883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42741692186287883629595255 64112538279431825444392883)
              ·
                refine ⟨96168807419147738166589325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64112538279431825444392883 96168807419147738166589325)
                ·
                  refine ⟨36063302782180401812470997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96168807419147738166589325 36063302782180401812470997)
                  ·
                    refine ⟨845233658957353167479789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36063302782180401812470997 845233658957353167479789)
                    ·
                      rfl

theorem cell22_2469130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2469130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469130 prefixEnd_2469130 := by exact prefixLift 2469130
  have htrace : WordTrace (prefixWord ++ tailWord_2469130) baseStart_2469130 baseEnd_2469130 := by
    simpa [prefixWord, tailWord_2469130, baseEnd_2469130] using wordTrace_append hprefix tailTrace_2469130
  have hstable : (prefixWord ++ tailWord_2469130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469130).length < 2 ^ (prefixWord ++ tailWord_2469130).sum := by decide
  have hdescent : baseEnd_2469130 < baseStart_2469130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469149 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 5]
def baseStart_2469149 : Nat := 118140960795 + 2469149 * 2 ^ 59
def prefixEnd_2469149 : Nat := 4983230072969 + 3 ^ 40 * 2469149 * 2
def baseEnd_2469149 : Nat := 281746721015214483751577

theorem tailTrace_2469149 : CollatzResearch.WordTrace tailWord_2469149 prefixEnd_2469149 281746721015214483751577 := by
  unfold tailWord_2469149
  simp only [CollatzResearch.WordTrace]
  refine ⟨90057262531702344921290501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60038175021134896614193667 90057262531702344921290501)
  ·
    refine ⟨16885736724694189672741969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90057262531702344921290501 16885736724694189672741969)
    ·
      refine ⟨12664302543520642254556477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16885736724694189672741969 12664302543520642254556477)
      ·
        refine ⟨4749113453820240845458679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12664302543520642254556477 4749113453820240845458679)
        ·
          refine ⟨7123670180730361268188019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4749113453820240845458679 7123670180730361268188019)
          ·
            refine ⟨10685505271095541902282029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7123670180730361268188019 10685505271095541902282029)
            ·
              refine ⟨4007064476660828213355761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10685505271095541902282029 4007064476660828213355761)
              ·
                refine ⟨3005298357495621160016821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007064476660828213355761 3005298357495621160016821)
                ·
                  refine ⟨281746721015214483751577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3005298357495621160016821 281746721015214483751577)
                  ·
                    rfl

theorem cell22_2469149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_2469149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469149 prefixEnd_2469149 := by exact prefixLift 2469149
  have htrace : WordTrace (prefixWord ++ tailWord_2469149) baseStart_2469149 baseEnd_2469149 := by
    simpa [prefixWord, tailWord_2469149, baseEnd_2469149] using wordTrace_append hprefix tailTrace_2469149
  have hstable : (prefixWord ++ tailWord_2469149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469149).length < 2 ^ (prefixWord ++ tailWord_2469149).sum := by decide
  have hdescent : baseEnd_2469149 < baseStart_2469149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469207 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2469207 : Nat := 118140960795 + 2469207 * 2 ^ 59
def prefixEnd_2469207 : Nat := 4983230072969 + 3 ^ 40 * 2469207 * 2
def baseEnd_2469207 : Nat := 845260017630950633304553

theorem tailTrace_2469207 : CollatzResearch.WordTrace tailWord_2469207 prefixEnd_2469207 845260017630950633304553 := by
  unfold tailWord_2469207
  simp only [CollatzResearch.WordTrace]
  refine ⟨90059377965492220826901875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60039585310328147217934583 90059377965492220826901875)
  ·
    refine ⟨135089066948238331240352813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90059377965492220826901875 135089066948238331240352813)
    ·
      refine ⟨50658400105589374215132305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135089066948238331240352813 50658400105589374215132305)
      ·
        refine ⟨37993800079192030661349229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50658400105589374215132305 37993800079192030661349229)
        ·
          refine ⟨14247675029697011498005961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37993800079192030661349229 14247675029697011498005961)
          ·
            refine ⟨10685756272272758623504471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14247675029697011498005961 10685756272272758623504471)
            ·
              refine ⟨16028634408409137935256707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10685756272272758623504471 16028634408409137935256707)
              ·
                refine ⟨24042951612613706902885061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16028634408409137935256707 24042951612613706902885061)
                ·
                  refine ⟨4508053427365070044290949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24042951612613706902885061 4508053427365070044290949)
                  ·
                    refine ⟨845260017630950633304553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4508053427365070044290949 845260017630950633304553)
                    ·
                      rfl

theorem cell22_2469207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2469207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469207 prefixEnd_2469207 := by exact prefixLift 2469207
  have htrace : WordTrace (prefixWord ++ tailWord_2469207) baseStart_2469207 baseEnd_2469207 := by
    simpa [prefixWord, tailWord_2469207, baseEnd_2469207] using wordTrace_append hprefix tailTrace_2469207
  have hstable : (prefixWord ++ tailWord_2469207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469207).length < 2 ^ (prefixWord ++ tailWord_2469207).sum := by decide
  have hdescent : baseEnd_2469207 < baseStart_2469207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469230 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2469230 : Nat := 118140960795 + 2469230 * 2 ^ 59
def prefixEnd_2469230 : Nat := 4983230072969 + 3 ^ 40 * 2469230 * 2
def baseEnd_2469230 : Nat := 845267891000986239979483

theorem tailTrace_2469230 : CollatzResearch.WordTrace tailWord_2469230 prefixEnd_2469230 845267891000986239979483 := by
  unfold tailWord_2469230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257527105551111969373643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60040144562939263836659429 11257527105551111969373643)
  ·
    refine ⟨16886290658326667954060465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11257527105551111969373643 16886290658326667954060465)
    ·
      refine ⟨12664717993745000965545349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16886290658326667954060465 12664717993745000965545349)
      ·
        refine ⟨2374634623827187681039753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12664717993745000965545349 2374634623827187681039753)
        ·
          refine ⟨1780975967870390760779815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2374634623827187681039753 1780975967870390760779815)
          ·
            refine ⟨2671463951805586141169723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780975967870390760779815 2671463951805586141169723)
            ·
              refine ⟨4007195927708379211754585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671463951805586141169723 4007195927708379211754585)
              ·
                refine ⟨3005396945781284408815939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007195927708379211754585 3005396945781284408815939)
                ·
                  refine ⟨4508095418671926613223909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3005396945781284408815939 4508095418671926613223909)
                  ·
                    refine ⟨845267891000986239979483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4508095418671926613223909 845267891000986239979483)
                    ·
                      rfl

theorem cell22_2469230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2469230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469230 prefixEnd_2469230 := by exact prefixLift 2469230
  have htrace : WordTrace (prefixWord ++ tailWord_2469230) baseStart_2469230 baseEnd_2469230 := by
    simpa [prefixWord, tailWord_2469230, baseEnd_2469230] using wordTrace_append hprefix tailTrace_2469230
  have hstable : (prefixWord ++ tailWord_2469230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469230).length < 2 ^ (prefixWord ++ tailWord_2469230).sum := by decide
  have hdescent : baseEnd_2469230 < baseStart_2469230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469288 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2469288 : Nat := 118140960795 + 2469288 * 2 ^ 59
def prefixEnd_2469288 : Nat := 4983230072969 + 3 ^ 40 * 2469288 * 2
def baseEnd_2469288 : Nat := 845287745586293422029305

theorem tailTrace_2469288 : CollatzResearch.WordTrace tailWord_2469288 prefixEnd_2469288 845287745586293422029305 := by
  unfold tailWord_2469288
  simp only [CollatzResearch.WordTrace]
  refine ⟨45031166139099385830300259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60041554852132514440400345 45031166139099385830300259)
  ·
    refine ⟨67546749208649078745450389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45031166139099385830300259 67546749208649078745450389)
    ·
      refine ⟨3166253869155425566192987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67546749208649078745450389 3166253869155425566192987)
      ·
        refine ⟨4749380803733138349289481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166253869155425566192987 4749380803733138349289481)
        ·
          refine ⟨3562035602799853761967111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749380803733138349289481 3562035602799853761967111)
          ·
            refine ⟨5343053404199780642950667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562035602799853761967111 5343053404199780642950667)
            ·
              refine ⟨8014580106299670964426001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5343053404199780642950667 8014580106299670964426001)
              ·
                refine ⟨6010935079724753223319501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8014580106299670964426001 6010935079724753223319501)
                ·
                  refine ⟨2254100654896782458744813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6010935079724753223319501 2254100654896782458744813)
                  ·
                    refine ⟨845287745586293422029305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254100654896782458744813 845287745586293422029305)
                    ·
                      rfl

theorem cell22_2469288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2469288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469288 prefixEnd_2469288 := by exact prefixLift 2469288
  have htrace : WordTrace (prefixWord ++ tailWord_2469288) baseStart_2469288 baseEnd_2469288 := by
    simpa [prefixWord, tailWord_2469288, baseEnd_2469288] using wordTrace_append hprefix tailTrace_2469288
  have hstable : (prefixWord ++ tailWord_2469288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469288).length < 2 ^ (prefixWord ++ tailWord_2469288).sum := by decide
  have hdescent : baseEnd_2469288 < baseStart_2469288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469327 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_2469327 : Nat := 118140960795 + 2469327 * 2 ^ 59
def prefixEnd_2469327 : Nat := 4983230072969 + 3 ^ 40 * 2469327 * 2
def baseEnd_2469327 : Nat := 845301096083310320304185

theorem tailTrace_2469327 : CollatzResearch.WordTrace tailWord_2469327 prefixEnd_2469327 845301096083310320304185 := by
  unfold tailWord_2469327
  simp only [CollatzResearch.WordTrace]
  refine ⟨90063754725057481321270235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60042503150038320880846823 90063754725057481321270235)
  ·
    refine ⟨135095632087586221981905353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90063754725057481321270235 135095632087586221981905353)
    ·
      refine ⟨101321724065689666486429015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135095632087586221981905353 101321724065689666486429015)
      ·
        refine ⟨151982586098534499729643523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101321724065689666486429015 151982586098534499729643523)
        ·
          refine ⟨227973879147801749594465285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151982586098534499729643523 227973879147801749594465285)
          ·
            refine ⟨42745102340212828048962241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227973879147801749594465285 42745102340212828048962241)
            ·
              refine ⟨32058826755159621036721681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42745102340212828048962241 32058826755159621036721681)
              ·
                refine ⟨24044120066369715777541261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32058826755159621036721681 24044120066369715777541261)
                ·
                  refine ⟨9016545024888643416577973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24044120066369715777541261 9016545024888643416577973)
                  ·
                    refine ⟨845301096083310320304185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9016545024888643416577973 845301096083310320304185)
                    ·
                      rfl

theorem cell22_2469327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_2469327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469327 prefixEnd_2469327 := by exact prefixLift 2469327
  have htrace : WordTrace (prefixWord ++ tailWord_2469327) baseStart_2469327 baseEnd_2469327 := by
    simpa [prefixWord, tailWord_2469327, baseEnd_2469327] using wordTrace_append hprefix tailTrace_2469327
  have hstable : (prefixWord ++ tailWord_2469327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469327).length < 2 ^ (prefixWord ++ tailWord_2469327).sum := by decide
  have hdescent : baseEnd_2469327 < baseStart_2469327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469378 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2469378 : Nat := 118140960795 + 2469378 * 2 ^ 59
def prefixEnd_2469378 : Nat := 4983230072969 + 3 ^ 40 * 2469378 * 2
def baseEnd_2469378 : Nat := 845318554425563187279029

theorem tailTrace_2469378 : CollatzResearch.WordTrace tailWord_2469378 prefixEnd_2469378 845318554425563187279029 := by
  unfold tailWord_2469378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516403711968179257844197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60043743231915144687584525 22516403711968179257844197)
  ·
    refine ⟨4221825695994033610845787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22516403711968179257844197 4221825695994033610845787)
    ·
      refine ⟨6332738543991050416268681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4221825695994033610845787 6332738543991050416268681)
      ·
        refine ⟨4749553907993287812201511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6332738543991050416268681 4749553907993287812201511)
        ·
          refine ⟨7124330861989931718302267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4749553907993287812201511 7124330861989931718302267)
          ·
            refine ⟨10686496292984897577453401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124330861989931718302267 10686496292984897577453401)
            ·
              refine ⟨8014872219738673183090051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10686496292984897577453401 8014872219738673183090051)
              ·
                refine ⟨12022308329608009774635077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8014872219738673183090051 12022308329608009774635077)
                ·
                  refine ⟨2254182811801501832744077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12022308329608009774635077 2254182811801501832744077)
                  ·
                    refine ⟨845318554425563187279029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254182811801501832744077 845318554425563187279029)
                    ·
                      rfl

theorem cell22_2469378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2469378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469378 prefixEnd_2469378 := by exact prefixLift 2469378
  have htrace : WordTrace (prefixWord ++ tailWord_2469378) baseStart_2469378 baseEnd_2469378 := by
    simpa [prefixWord, tailWord_2469378, baseEnd_2469378] using wordTrace_append hprefix tailTrace_2469378
  have hstable : (prefixWord ++ tailWord_2469378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469378).length < 2 ^ (prefixWord ++ tailWord_2469378).sum := by decide
  have hdescent : baseEnd_2469378 < baseStart_2469378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469380 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 4]
def baseStart_2469380 : Nat := 118140960795 + 2469380 * 2 ^ 59
def prefixEnd_2469380 : Nat := 4983230072969 + 3 ^ 40 * 2469380 * 2
def baseEnd_2469380 : Nat := 281773079688811949576341

theorem tailTrace_2469380 : CollatzResearch.WordTrace tailWord_2469380 prefixEnd_2469380 281773079688811949576341 := by
  unfold tailWord_2469380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45032843896932735686474797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60043791862576980915299729 45032843896932735686474797)
  ·
    refine ⟨16887316461349775882428049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45032843896932735686474797 16887316461349775882428049)
    ·
      refine ⟨12665487346012331911821037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16887316461349775882428049 12665487346012331911821037)
      ·
        refine ⟨4749557754754624466932889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12665487346012331911821037 4749557754754624466932889)
        ·
          refine ⟨3562168316065968350199667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749557754754624466932889 3562168316065968350199667)
          ·
            refine ⟨5343252474098952525299501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562168316065968350199667 5343252474098952525299501)
            ·
              refine ⟨2003719677787107196987313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5343252474098952525299501 2003719677787107196987313)
              ·
                refine ⟨1502789758340330397740485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2003719677787107196987313 1502789758340330397740485)
                ·
                  refine ⟨281773079688811949576341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502789758340330397740485 281773079688811949576341)
                  ·
                    rfl

theorem cell22_2469380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_2469380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469380 prefixEnd_2469380 := by exact prefixLift 2469380
  have htrace : WordTrace (prefixWord ++ tailWord_2469380) baseStart_2469380 baseEnd_2469380 := by
    simpa [prefixWord, tailWord_2469380, baseEnd_2469380] using wordTrace_append hprefix tailTrace_2469380
  have hstable : (prefixWord ++ tailWord_2469380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469380).length < 2 ^ (prefixWord ++ tailWord_2469380).sum := by decide
  have hdescent : baseEnd_2469380 < baseStart_2469380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469434 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_2469434 : Nat := 118140960795 + 2469434 * 2 ^ 59
def prefixEnd_2469434 : Nat := 4983230072969 + 3 ^ 40 * 2469434 * 2
def baseEnd_2469434 : Nat := 845337724369997707878857

theorem tailTrace_2469434 : CollatzResearch.WordTrace tailWord_2469434 prefixEnd_2469434 845337724369997707878857 := by
  unfold tailWord_2469434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516914333917459648853839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60045104890446559063610237 22516914333917459648853839)
  ·
    refine ⟨33775371500876189473280759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22516914333917459648853839 33775371500876189473280759)
    ·
      refine ⟨50663057251314284209921139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33775371500876189473280759 50663057251314284209921139)
      ·
        refine ⟨75994585876971426314881709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50663057251314284209921139 75994585876971426314881709)
        ·
          refine ⟨28497969703864284868080641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75994585876971426314881709 28497969703864284868080641)
          ·
            refine ⟨21373477277898213651060481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28497969703864284868080641 21373477277898213651060481)
            ·
              refine ⟨16030107958423660238295361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21373477277898213651060481 16030107958423660238295361)
              ·
                refine ⟨12022580968817745178721521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16030107958423660238295361 12022580968817745178721521)
                ·
                  refine ⟨9016935726613308884041141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12022580968817745178721521 9016935726613308884041141)
                  ·
                    refine ⟨845337724369997707878857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9016935726613308884041141 845337724369997707878857)
                    ·
                      rfl

theorem cell22_2469434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_2469434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469434 prefixEnd_2469434 := by exact prefixLift 2469434
  have htrace : WordTrace (prefixWord ++ tailWord_2469434) baseStart_2469434 baseEnd_2469434 := by
    simpa [prefixWord, tailWord_2469434, baseEnd_2469434] using wordTrace_append hprefix tailTrace_2469434
  have hstable : (prefixWord ++ tailWord_2469434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469434).length < 2 ^ (prefixWord ++ tailWord_2469434).sum := by decide
  have hdescent : baseEnd_2469434 < baseStart_2469434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469481 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 4]
def baseStart_2469481 : Nat := 118140960795 + 2469481 * 2 ^ 59
def prefixEnd_2469481 : Nat := 4983230072969 + 3 ^ 40 * 2469481 * 2
def baseEnd_2469481 : Nat := 281784604476835083984571

theorem tailTrace_2469481 : CollatzResearch.WordTrace tailWord_2469481 prefixEnd_2469481 281784604476835083984571 := by
  unfold tailWord_2469481
  simp only [CollatzResearch.WordTrace]
  refine ⟨90069371566499565622376297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60046247710999710414917531 90069371566499565622376297)
  ·
    refine ⟨67552028674874674216782223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90069371566499565622376297 67552028674874674216782223)
    ·
      refine ⟨101328043012312011325173335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67552028674874674216782223 101328043012312011325173335)
      ·
        refine ⟨151992064518468016987760003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101328043012312011325173335 151992064518468016987760003)
        ·
          refine ⟨227988096777702025481640005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151992064518468016987760003 227988096777702025481640005)
          ·
            refine ⟨42747768145819129777807501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 227988096777702025481640005 42747768145819129777807501)
            ·
              refine ⟨16030413054682173666677813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42747768145819129777807501 16030413054682173666677813)
              ·
                refine ⟨1502851223876453781251045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16030413054682173666677813 1502851223876453781251045)
                ·
                  refine ⟨281784604476835083984571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502851223876453781251045 281784604476835083984571)
                  ·
                    rfl

theorem cell22_2469481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_2469481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469481 prefixEnd_2469481 := by exact prefixLift 2469481
  have htrace : WordTrace (prefixWord ++ tailWord_2469481) baseStart_2469481 baseEnd_2469481 := by
    simpa [prefixWord, tailWord_2469481, baseEnd_2469481] using wordTrace_append hprefix tailTrace_2469481
  have hstable : (prefixWord ++ tailWord_2469481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469481).length < 2 ^ (prefixWord ++ tailWord_2469481).sum := by decide
  have hdescent : baseEnd_2469481 < baseStart_2469481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469509 : List Nat := [1, 3, 1, 1, 4, 1, 2, 9]
def baseStart_2469509 : Nat := 118140960795 + 2469509 * 2 ^ 59
def prefixEnd_2469509 : Nat := 4983230072969 + 3 ^ 40 * 2469509 * 2
def baseEnd_2469509 : Nat := 93929266489191390250403

theorem tailTrace_2469509 : CollatzResearch.WordTrace tailWord_2469509 prefixEnd_2469509 93929266489191390250403 := by
  unfold tailWord_2469509
  simp only [CollatzResearch.WordTrace]
  refine ⟨90070392810398126404395581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60046928540265417602930387 90070392810398126404395581)
  ·
    refine ⟨33776397303899297401648343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90070392810398126404395581 33776397303899297401648343)
    ·
      refine ⟨50664595955848946102472515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33776397303899297401648343 50664595955848946102472515)
      ·
        refine ⟨75996893933773419153708773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50664595955848946102472515 75996893933773419153708773)
        ·
          refine ⟨14249417612582516091320395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75996893933773419153708773 14249417612582516091320395)
          ·
            refine ⟨21374126418873774136980593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14249417612582516091320395 21374126418873774136980593)
            ·
              refine ⟨16030594814155330602735445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21374126418873774136980593 16030594814155330602735445)
              ·
                refine ⟨93929266489191390250403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16030594814155330602735445 93929266489191390250403)
                ·
                  rfl

theorem cell22_2469509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 9].length) (baseStart_2469509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469509 prefixEnd_2469509 := by exact prefixLift 2469509
  have htrace : WordTrace (prefixWord ++ tailWord_2469509) baseStart_2469509 baseEnd_2469509 := by
    simpa [prefixWord, tailWord_2469509, baseEnd_2469509] using wordTrace_append hprefix tailTrace_2469509
  have hstable : (prefixWord ++ tailWord_2469509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469509).length < 2 ^ (prefixWord ++ tailWord_2469509).sum := by decide
  have hdescent : baseEnd_2469509 < baseStart_2469509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469532 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 4]
def baseStart_2469532 : Nat := 118140960795 + 2469532 * 2 ^ 59
def prefixEnd_2469532 : Nat := 4983230072969 + 3 ^ 40 * 2469532 * 2
def baseEnd_2469532 : Nat := 281790423924252706309519

theorem tailTrace_2469532 : CollatzResearch.WordTrace tailWord_2469532 prefixEnd_2469532 281790423924252706309519 := by
  unfold tailWord_2469532
  simp only [CollatzResearch.WordTrace]
  refine ⟨45035615844657400666241425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60047487792876534221655233 45035615844657400666241425)
  ·
    refine ⟨33776711883493050499681069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45035615844657400666241425 33776711883493050499681069)
    ·
      refine ⟨12666266956309893937380401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33776711883493050499681069 12666266956309893937380401)
      ·
        refine ⟨9499700217232420453035301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12666266956309893937380401 9499700217232420453035301)
        ·
          refine ⟨1781193790731078834944119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9499700217232420453035301 1781193790731078834944119)
          ·
            refine ⟨2671790686096618252416179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781193790731078834944119 2671790686096618252416179)
            ·
              refine ⟨4007686029144927378624269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2671790686096618252416179 4007686029144927378624269)
              ·
                refine ⟨1502882260929347766984101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4007686029144927378624269 1502882260929347766984101)
                ·
                  refine ⟨281790423924252706309519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1502882260929347766984101 281790423924252706309519)
                  ·
                    rfl

theorem cell22_2469532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_2469532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469532 prefixEnd_2469532 := by exact prefixLift 2469532
  have htrace : WordTrace (prefixWord ++ tailWord_2469532) baseStart_2469532 baseEnd_2469532 := by
    simpa [prefixWord, tailWord_2469532, baseEnd_2469532] using wordTrace_append hprefix tailTrace_2469532
  have hstable : (prefixWord ++ tailWord_2469532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469532).length < 2 ^ (prefixWord ++ tailWord_2469532).sum := by decide
  have hdescent : baseEnd_2469532 < baseStart_2469532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469541 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_2469541 : Nat := 118140960795 + 2469541 * 2 ^ 59
def prefixEnd_2469541 : Nat := 4983230072969 + 3 ^ 40 * 2469541 * 2
def baseEnd_2469541 : Nat := 845374352656685095453529

theorem tailTrace_2469541 : CollatzResearch.WordTrace tailWord_2469541 prefixEnd_2469541 845374352656685095453529 := by
  unfold tailWord_2469541
  simp only [CollatzResearch.WordTrace]
  refine ⟨90071559946282195869560477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60047706630854797246373651 90071559946282195869560477)
  ·
    refine ⟨33776834979855823451085179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90071559946282195869560477 33776834979855823451085179)
    ·
      refine ⟨50665252469783735176627769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33776834979855823451085179 50665252469783735176627769)
      ·
        refine ⟨37998939352337801382470827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50665252469783735176627769 37998939352337801382470827)
        ·
          refine ⟨56998409028506702073706241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37998939352337801382470827 56998409028506702073706241)
          ·
            refine ⟨42748806771380026555279681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56998409028506702073706241 42748806771380026555279681)
            ·
              refine ⟨32061605078535019916459761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42748806771380026555279681 32061605078535019916459761)
              ·
                refine ⟨24046203808901264937344821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32061605078535019916459761 24046203808901264937344821)
                ·
                  refine ⟨2254331607084493587876077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24046203808901264937344821 2254331607084493587876077)
                  ·
                    refine ⟨845374352656685095453529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254331607084493587876077 845374352656685095453529)
                    ·
                      rfl

theorem cell22_2469541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_2469541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469541 prefixEnd_2469541 := by exact prefixLift 2469541
  have htrace : WordTrace (prefixWord ++ tailWord_2469541) baseStart_2469541 baseEnd_2469541 := by
    simpa [prefixWord, tailWord_2469541, baseEnd_2469541] using wordTrace_append hprefix tailTrace_2469541
  have hstable : (prefixWord ++ tailWord_2469541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469541).length < 2 ^ (prefixWord ++ tailWord_2469541).sum := by decide
  have hdescent : baseEnd_2469541 < baseStart_2469541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469620 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2469620 : Nat := 118140960795 + 2469620 * 2 ^ 59
def prefixEnd_2469620 : Nat := 4983230072969 + 3 ^ 40 * 2469620 * 2
def baseEnd_2469620 : Nat := 845401395971155222728287

theorem tailTrace_2469620 : CollatzResearch.WordTrace tailWord_2469620 prefixEnd_2469620 845401395971155222728287 := by
  unfold tailWord_2469620
  simp only [CollatzResearch.WordTrace]
  refine ⟨45037220656497996180843157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60049627541997328241124209 45037220656497996180843157)
  ·
    refine ⟨2111119718273343570977023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45037220656497996180843157 2111119718273343570977023)
    ·
      refine ⟨3166679577410015356465535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2111119718273343570977023 3166679577410015356465535)
      ·
        refine ⟨4750019366115023034698303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166679577410015356465535 4750019366115023034698303)
        ·
          refine ⟨7125029049172534552047455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750019366115023034698303 7125029049172534552047455)
          ·
            refine ⟨10687543573758801828071183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7125029049172534552047455 10687543573758801828071183)
            ·
              refine ⟨16031315360638202742106775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10687543573758801828071183 16031315360638202742106775)
              ·
                refine ⟨24046973040957304113160163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16031315360638202742106775 24046973040957304113160163)
                ·
                  refine ⟨36070459561435956169740245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24046973040957304113160163 36070459561435956169740245)
                  ·
                    refine ⟨845401395971155222728287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36070459561435956169740245 845401395971155222728287)
                    ·
                      rfl

theorem cell22_2469620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2469620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469620 prefixEnd_2469620 := by exact prefixLift 2469620
  have htrace : WordTrace (prefixWord ++ tailWord_2469620) baseStart_2469620 baseEnd_2469620 := by
    simpa [prefixWord, tailWord_2469620, baseEnd_2469620] using wordTrace_append hprefix tailTrace_2469620
  have hstable : (prefixWord ++ tailWord_2469620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469620).length < 2 ^ (prefixWord ++ tailWord_2469620).sum := by decide
  have hdescent : baseEnd_2469620 < baseStart_2469620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469631 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 1, 5]
def baseStart_2469631 : Nat := 118140960795 + 2469631 * 2 ^ 59
def prefixEnd_2469631 : Nat := 4983230072969 + 3 ^ 40 * 2469631 * 2
def baseEnd_2469631 : Nat := 845405161495954860703253

theorem tailTrace_2469631 : CollatzResearch.WordTrace tailWord_2469631 prefixEnd_2469631 845405161495954860703253 := by
  unfold tailWord_2469631
  simp only [CollatzResearch.WordTrace]
  refine ⟨90074842515956141240336747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60049895010637427493557831 90074842515956141240336747)
  ·
    refine ⟨135112263773934211860505121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90074842515956141240336747 135112263773934211860505121)
    ·
      refine ⟨101334197830450658895378841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135112263773934211860505121 101334197830450658895378841)
      ·
        refine ⟨76000648372837994171534131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101334197830450658895378841 76000648372837994171534131)
        ·
          refine ⟨114000972559256991257301197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76000648372837994171534131 114000972559256991257301197)
          ·
            refine ⟨42750364709721371721487949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114000972559256991257301197 42750364709721371721487949)
            ·
              refine ⟨16031386766145514395557981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42750364709721371721487949 16031386766145514395557981)
              ·
                refine ⟨6011770037304567898334243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16031386766145514395557981 6011770037304567898334243)
                ·
                  refine ⟨9017655055956851847501365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6011770037304567898334243 9017655055956851847501365)
                  ·
                    refine ⟨845405161495954860703253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9017655055956851847501365 845405161495954860703253)
                    ·
                      rfl

theorem cell22_2469631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_2469631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469631 prefixEnd_2469631 := by exact prefixLift 2469631
  have htrace : WordTrace (prefixWord ++ tailWord_2469631) baseStart_2469631 baseEnd_2469631 := by
    simpa [prefixWord, tailWord_2469631, baseEnd_2469631] using wordTrace_append hprefix tailTrace_2469631
  have hstable : (prefixWord ++ tailWord_2469631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469631).length < 2 ^ (prefixWord ++ tailWord_2469631).sum := by decide
  have hdescent : baseEnd_2469631 < baseStart_2469631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469665 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_2469665 : Nat := 118140960795 + 2469665 * 2 ^ 59
def prefixEnd_2469665 : Nat := 4983230072969 + 3 ^ 40 * 2469665 * 2
def baseEnd_2469665 : Nat := 845416800390790105353149

theorem tailTrace_2469665 : CollatzResearch.WordTrace tailWord_2469665 prefixEnd_2469665 845416800390790105353149 := by
  unfold tailWord_2469665
  simp only [CollatzResearch.WordTrace]
  refine ⟨90076082597832965047074449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60050721731888643364716299 90076082597832965047074449)
  ·
    refine ⟨67557061948374723785305837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90076082597832965047074449 67557061948374723785305837)
    ·
      refine ⟨25333898230640521419489689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67557061948374723785305837 25333898230640521419489689)
      ·
        refine ⟨19000423672980391064617267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25333898230640521419489689 19000423672980391064617267)
        ·
          refine ⟨28500635509470586596925901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19000423672980391064617267 28500635509470586596925901)
          ·
            refine ⟨10687738316051469973847213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28500635509470586596925901 10687738316051469973847213)
            ·
              refine ⟨4007901868519301240192705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10687738316051469973847213 4007901868519301240192705)
              ·
                refine ⟨3005926401389475930144529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007901868519301240192705 3005926401389475930144529)
                ·
                  refine ⟨2254444801042106947608397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3005926401389475930144529 2254444801042106947608397)
                  ·
                    refine ⟨845416800390790105353149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254444801042106947608397 845416800390790105353149)
                    ·
                      rfl

theorem cell22_2469665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_2469665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469665 prefixEnd_2469665 := by exact prefixLift 2469665
  have htrace : WordTrace (prefixWord ++ tailWord_2469665) baseStart_2469665 baseEnd_2469665 := by
    simpa [prefixWord, tailWord_2469665, baseEnd_2469665] using wordTrace_append hprefix tailTrace_2469665
  have hstable : (prefixWord ++ tailWord_2469665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469665).length < 2 ^ (prefixWord ++ tailWord_2469665).sum := by decide
  have hdescent : baseEnd_2469665 < baseStart_2469665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469682 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_2469682 : Nat := 118140960795 + 2469682 * 2 ^ 59
def prefixEnd_2469682 : Nat := 4983230072969 + 3 ^ 40 * 2469682 * 2
def baseEnd_2469682 : Nat := 845422619838207727678097

theorem tailTrace_2469682 : CollatzResearch.WordTrace tailWord_2469682 prefixEnd_2469682 845422619838207727678097 := by
  unfold tailWord_2469682
  simp only [CollatzResearch.WordTrace]
  refine ⟨22519175659692844237610825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60051135092514251300295533 22519175659692844237610825)
  ·
    refine ⟨16889381744769633178208119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22519175659692844237610825 16889381744769633178208119)
    ·
      refine ⟨25334072617154449767312179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16889381744769633178208119 25334072617154449767312179)
      ·
        refine ⟨38001108925731674650968269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25334072617154449767312179 38001108925731674650968269)
        ·
          refine ⟨14250415847149377994113101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38001108925731674650968269 14250415847149377994113101)
          ·
            refine ⟨5343905942681016747792413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14250415847149377994113101 5343905942681016747792413)
            ·
              refine ⟨2003964728505381280422155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5343905942681016747792413 2003964728505381280422155)
              ·
                refine ⟨3005947092758071920633233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003964728505381280422155 3005947092758071920633233)
                ·
                  refine ⟨2254460319568553940474925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3005947092758071920633233 2254460319568553940474925)
                  ·
                    refine ⟨845422619838207727678097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254460319568553940474925 845422619838207727678097)
                    ·
                      rfl

theorem cell22_2469682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_2469682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469682 prefixEnd_2469682 := by exact prefixLift 2469682
  have htrace : WordTrace (prefixWord ++ tailWord_2469682) baseStart_2469682 baseEnd_2469682 := by
    simpa [prefixWord, tailWord_2469682, baseEnd_2469682] using wordTrace_append hprefix tailTrace_2469682
  have hstable : (prefixWord ++ tailWord_2469682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469682).length < 2 ^ (prefixWord ++ tailWord_2469682).sum := by decide
  have hdescent : baseEnd_2469682 < baseStart_2469682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469695 : List Nat := [1, 1, 2, 2, 6, 2, 2, 6]
def baseStart_2469695 : Nat := 118140960795 + 2469695 * 2 ^ 59
def prefixEnd_2469695 : Nat := 4983230072969 + 3 ^ 40 * 2469695 * 2
def baseEnd_2469695 : Nat := 93936341111542225233673

theorem tailTrace_2469695 : CollatzResearch.WordTrace tailWord_2469695 prefixEnd_2469695 93936341111542225233673 := by
  unfold tailWord_2469695
  simp only [CollatzResearch.WordTrace]
  refine ⟨90077176787724280170666539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60051451191816186780444359 90077176787724280170666539)
  ·
    refine ⟨135115765181586420255999809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90077176787724280170666539 135115765181586420255999809)
    ·
      refine ⟨101336823886189815191999857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135115765181586420255999809 101336823886189815191999857)
      ·
        refine ⟨76002617914642361393999893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101336823886189815191999857 76002617914642361393999893)
        ·
          refine ⟨3562622714748860690343745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76002617914642361393999893 3562622714748860690343745)
          ·
            refine ⟨2671967036061645517757809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3562622714748860690343745 2671967036061645517757809)
            ·
              refine ⟨2003975277046234138318357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2671967036061645517757809 2003975277046234138318357)
              ·
                refine ⟨93936341111542225233673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2003975277046234138318357 93936341111542225233673)
                ·
                  rfl

theorem cell22_2469695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 6].length) (baseStart_2469695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469695 prefixEnd_2469695 := by exact prefixLift 2469695
  have htrace : WordTrace (prefixWord ++ tailWord_2469695) baseStart_2469695 baseEnd_2469695 := by
    simpa [prefixWord, tailWord_2469695, baseEnd_2469695] using wordTrace_append hprefix tailTrace_2469695
  have hstable : (prefixWord ++ tailWord_2469695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469695).length < 2 ^ (prefixWord ++ tailWord_2469695).sum := by decide
  have hdescent : baseEnd_2469695 < baseStart_2469695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469706 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 9]
def baseStart_2469706 : Nat := 118140960795 + 2469706 * 2 ^ 59
def prefixEnd_2469706 : Nat := 4983230072969 + 3 ^ 40 * 2469706 * 2
def baseEnd_2469706 : Nat := 281810278509559888359341

theorem tailTrace_2469706 : CollatzResearch.WordTrace tailWord_2469706 prefixEnd_2469706 281810278509559888359341 := by
  unfold tailWord_2469706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22519394497671107262329243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60051718660456286032877981 22519394497671107262329243)
  ·
    refine ⟨33779091746506660893493865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22519394497671107262329243 33779091746506660893493865)
    ·
      refine ⟨25334318809879995670120399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33779091746506660893493865 25334318809879995670120399)
      ·
        refine ⟨38001478214819993505180599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25334318809879995670120399 38001478214819993505180599)
        ·
          refine ⟨57002217322229990257770899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38001478214819993505180599 57002217322229990257770899)
          ·
            refine ⟨85503325983344985386656349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57002217322229990257770899 85503325983344985386656349)
            ·
              refine ⟨32063747243754369519996131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85503325983344985386656349 32063747243754369519996131)
              ·
                refine ⟨48095620865631554279994197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32063747243754369519996131 48095620865631554279994197)
                ·
                  refine ⟨281810278509559888359341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48095620865631554279994197 281810278509559888359341)
                  ·
                    rfl

theorem cell22_2469706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_2469706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469706 prefixEnd_2469706 := by exact prefixLift 2469706
  have htrace : WordTrace (prefixWord ++ tailWord_2469706) baseStart_2469706 baseEnd_2469706 := by
    simpa [prefixWord, tailWord_2469706, baseEnd_2469706] using wordTrace_append hprefix tailTrace_2469706
  have hstable : (prefixWord ++ tailWord_2469706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469706).length < 2 ^ (prefixWord ++ tailWord_2469706).sum := by decide
  have hdescent : baseEnd_2469706 < baseStart_2469706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469740 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 5]
def baseStart_2469740 : Nat := 118140960795 + 2469740 * 2 ^ 59
def prefixEnd_2469740 : Nat := 4983230072969 + 3 ^ 40 * 2469740 * 2
def baseEnd_2469740 : Nat := 281814158141171636575973

theorem tailTrace_2469740 : CollatzResearch.WordTrace tailWord_2469740 prefixEnd_2469740 281814158141171636575973 := by
  unfold tailWord_2469740
  simp only [CollatzResearch.WordTrace]
  refine ⟨45039409036280626428027337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60052545381707501904036449 45039409036280626428027337)
  ·
    refine ⟨33779556777210469821020503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45039409036280626428027337 33779556777210469821020503)
    ·
      refine ⟨50669335165815704731530755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33779556777210469821020503 50669335165815704731530755)
      ·
        refine ⟨76004002748723557097296133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50669335165815704731530755 76004002748723557097296133)
        ·
          refine ⟨14250750515385666955743025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76004002748723557097296133 14250750515385666955743025)
          ·
            refine ⟨10688062886539250216807269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14250750515385666955743025 10688062886539250216807269)
            ·
              refine ⟨2004011791226109415651363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10688062886539250216807269 2004011791226109415651363)
              ·
                refine ⟨3006017686839164123477045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004011791226109415651363 3006017686839164123477045)
                ·
                  refine ⟨281814158141171636575973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006017686839164123477045 281814158141171636575973)
                  ·
                    rfl

theorem cell22_2469740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_2469740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469740 prefixEnd_2469740 := by exact prefixLift 2469740
  have htrace : WordTrace (prefixWord ++ tailWord_2469740) baseStart_2469740 baseEnd_2469740 := by
    simpa [prefixWord, tailWord_2469740, baseEnd_2469740] using wordTrace_append hprefix tailTrace_2469740
  have hstable : (prefixWord ++ tailWord_2469740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469740).length < 2 ^ (prefixWord ++ tailWord_2469740).sum := by decide
  have hdescent : baseEnd_2469740 < baseStart_2469740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469753 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_2469753 : Nat := 118140960795 + 2469753 * 2 ^ 59
def prefixEnd_2469753 : Nat := 4983230072969 + 3 ^ 40 * 2469753 * 2
def baseEnd_2469753 : Nat := 845446924589187209152879

theorem tailTrace_2469753 : CollatzResearch.WordTrace tailWord_2469753 prefixEnd_2469753 845446924589187209152879 := by
  unfold tailWord_2469753
  simp only [CollatzResearch.WordTrace]
  refine ⟨90079292221514156076277913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60052861481009437384185275 90079292221514156076277913)
  ·
    refine ⟨67559469166135617057208435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90079292221514156076277913 67559469166135617057208435)
    ·
      refine ⟨101339203749203425585812653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67559469166135617057208435 101339203749203425585812653)
      ·
        refine ⟨38002201405951284594679745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101339203749203425585812653 38002201405951284594679745)
        ·
          refine ⟨28501651054463463446009809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38002201405951284594679745 28501651054463463446009809)
          ·
            refine ⟨21376238290847597584507357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28501651054463463446009809 21376238290847597584507357)
            ·
              refine ⟨8016089359067849094190259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21376238290847597584507357 8016089359067849094190259)
              ·
                refine ⟨12024134038601773641285389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8016089359067849094190259 12024134038601773641285389)
                ·
                  refine ⟨4509050264475665115482021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12024134038601773641285389 4509050264475665115482021)
                  ·
                    refine ⟨845446924589187209152879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509050264475665115482021 845446924589187209152879)
                    ·
                      rfl

theorem cell22_2469753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_2469753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469753 prefixEnd_2469753 := by exact prefixLift 2469753
  have htrace : WordTrace (prefixWord ++ tailWord_2469753) baseStart_2469753 baseEnd_2469753 := by
    simpa [prefixWord, tailWord_2469753, baseEnd_2469753] using wordTrace_append hprefix tailTrace_2469753
  have hstable : (prefixWord ++ tailWord_2469753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469753).length < 2 ^ (prefixWord ++ tailWord_2469753).sum := by decide
  have hdescent : baseEnd_2469753 < baseStart_2469753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469909 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 5]
def baseStart_2469909 : Nat := 118140960795 + 2469909 * 2 ^ 59
def prefixEnd_2469909 : Nat := 4983230072969 + 3 ^ 40 * 2469909 * 2
def baseEnd_2469909 : Nat := 281833442192418267417467

theorem tailTrace_2469909 : CollatzResearch.WordTrace tailWord_2469909 prefixEnd_2469909 281833442192418267417467 := by
  unfold tailWord_2469909
  simp only [CollatzResearch.WordTrace]
  refine ⟨90084982008948994718956781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60056654672632663145971187 90084982008948994718956781)
  ·
    refine ⟨33781868253355873019608793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90084982008948994718956781 33781868253355873019608793)
    ·
      refine ⟨25336401190016904764706595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33781868253355873019608793 25336401190016904764706595)
      ·
        refine ⟨38004601785025357147059893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25336401190016904764706595 38004601785025357147059893)
        ·
          refine ⟨3562931417346127232536865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38004601785025357147059893 3562931417346127232536865)
          ·
            refine ⟨2672198563009595424402649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3562931417346127232536865 2672198563009595424402649)
            ·
              refine ⟨2004148922257196568301987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672198563009595424402649 2004148922257196568301987)
              ·
                refine ⟨3006223383385794852452981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004148922257196568301987 3006223383385794852452981)
                ·
                  refine ⟨281833442192418267417467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006223383385794852452981 281833442192418267417467)
                  ·
                    rfl

theorem cell22_2469909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_2469909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469909 prefixEnd_2469909 := by exact prefixLift 2469909
  have htrace : WordTrace (prefixWord ++ tailWord_2469909) baseStart_2469909 baseEnd_2469909 := by
    simpa [prefixWord, tailWord_2469909, baseEnd_2469909] using wordTrace_append hprefix tailTrace_2469909
  have hstable : (prefixWord ++ tailWord_2469909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469909).length < 2 ^ (prefixWord ++ tailWord_2469909).sum := by decide
  have hdescent : baseEnd_2469909 < baseStart_2469909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469935 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 4, 3]
def baseStart_2469935 : Nat := 118140960795 + 2469935 * 2 ^ 59
def prefixEnd_2469935 : Nat := 4983230072969 + 3 ^ 40 * 2469935 * 2
def baseEnd_2469935 : Nat := 845509226908599401102321

theorem tailTrace_2469935 : CollatzResearch.WordTrace tailWord_2469935 prefixEnd_2469935 845509226908599401102321 := by
  unfold tailWord_2469935
  simp only [CollatzResearch.WordTrace]
  refine ⟨90085930306854801159403259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60057286871236534106268839 90085930306854801159403259)
  ·
    refine ⟨135128895460282201739104889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90085930306854801159403259 135128895460282201739104889)
    ·
      refine ⟨101346671595211651304328667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135128895460282201739104889 101346671595211651304328667)
      ·
        refine ⟨152020007392817476956493001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101346671595211651304328667 152020007392817476956493001)
        ·
          refine ⟨114015005544613107717369751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152020007392817476956493001 114015005544613107717369751)
          ·
            refine ⟨171022508316919661576054627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114015005544613107717369751 171022508316919661576054627)
            ·
              refine ⟨256533762475379492364081941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171022508316919661576054627 256533762475379492364081941)
              ·
                refine ⟨12025020116033413704566341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256533762475379492364081941 12025020116033413704566341)
                ·
                  refine ⟨2254691271756265069606189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12025020116033413704566341 2254691271756265069606189)
                  ·
                    refine ⟨845509226908599401102321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254691271756265069606189 845509226908599401102321)
                    ·
                      rfl

theorem cell22_2469935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_2469935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469935 prefixEnd_2469935 := by exact prefixLift 2469935
  have htrace : WordTrace (prefixWord ++ tailWord_2469935) baseStart_2469935 baseEnd_2469935 := by
    simpa [prefixWord, tailWord_2469935, baseEnd_2469935] using wordTrace_append hprefix tailTrace_2469935
  have hstable : (prefixWord ++ tailWord_2469935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469935).length < 2 ^ (prefixWord ++ tailWord_2469935).sum := by decide
  have hdescent : baseEnd_2469935 < baseStart_2469935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469952 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 2, 3]
def baseStart_2469952 : Nat := 118140960795 + 2469952 * 2 ^ 59
def prefixEnd_2469952 : Nat := 4983230072969 + 3 ^ 40 * 2469952 * 2
def baseEnd_2469952 : Nat := 845515046356017023427269

theorem tailTrace_2469952 : CollatzResearch.WordTrace tailWord_2469952 prefixEnd_2469952 845515046356017023427269 := by
  unfold tailWord_2469952
  simp only [CollatzResearch.WordTrace]
  refine ⟨45043275173896606531386055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60057700231862142041848073 45043275173896606531386055)
  ·
    refine ⟨67564912760844909797079083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45043275173896606531386055 67564912760844909797079083)
    ·
      refine ⟨101347369141267364695618625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67564912760844909797079083 101347369141267364695618625)
      ·
        refine ⟨76010526855950523521713969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101347369141267364695618625 76010526855950523521713969)
        ·
          refine ⟨57007895141962892641285477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76010526855950523521713969 57007895141962892641285477)
          ·
            refine ⟨10688980339118042370241027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57007895141962892641285477 10688980339118042370241027)
            ·
              refine ⟨16033470508677063555361541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10688980339118042370241027 16033470508677063555361541)
              ·
                refine ⟨3006275720376949416630289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16033470508677063555361541 3006275720376949416630289)
                ·
                  refine ⟨2254706790282712062472717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006275720376949416630289 2254706790282712062472717)
                  ·
                    refine ⟨845515046356017023427269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254706790282712062472717 845515046356017023427269)
                    ·
                      rfl

theorem cell22_2469952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 2, 3].length) (baseStart_2469952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469952 prefixEnd_2469952 := by exact prefixLift 2469952
  have htrace : WordTrace (prefixWord ++ tailWord_2469952) baseStart_2469952 baseEnd_2469952 := by
    simpa [prefixWord, tailWord_2469952, baseEnd_2469952] using wordTrace_append hprefix tailTrace_2469952
  have hstable : (prefixWord ++ tailWord_2469952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469952).length < 2 ^ (prefixWord ++ tailWord_2469952).sum := by decide
  have hdescent : baseEnd_2469952 < baseStart_2469952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2469997 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2469997 : Nat := 118140960795 + 2469997 * 2 ^ 59
def prefixEnd_2469997 : Nat := 4983230072969 + 3 ^ 40 * 2469997 * 2
def baseEnd_2469997 : Nat := 845530450775651906052131

theorem tailTrace_2469997 : CollatzResearch.WordTrace tailWord_2469997 prefixEnd_2469997 845530450775651906052131 := by
  unfold tailWord_2469997
  simp only [CollatzResearch.WordTrace]
  refine ⟨90088191632630185748160245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60058794421753457165440163 90088191632630185748160245)
  ·
    refine ⟨8445767965559079913890023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90088191632630185748160245 8445767965559079913890023)
    ·
      refine ⟨12668651948338619870835035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8445767965559079913890023 12668651948338619870835035)
      ·
        refine ⟨19002977922507929806252553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12668651948338619870835035 19002977922507929806252553)
        ·
          refine ⟨14252233441880947354689415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19002977922507929806252553 14252233441880947354689415)
          ·
            refine ⟨21378350162821421032034123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14252233441880947354689415 21378350162821421032034123)
            ·
              refine ⟨32067525244232131548051185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21378350162821421032034123 32067525244232131548051185)
              ·
                refine ⟨24050643933174098661038389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32067525244232131548051185 24050643933174098661038389)
                ·
                  refine ⟨2254747868735071749472349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24050643933174098661038389 2254747868735071749472349)
                  ·
                    refine ⟨845530450775651906052131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254747868735071749472349 845530450775651906052131)
                    ·
                      rfl

theorem cell22_2469997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2469997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2469997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2469997 prefixEnd_2469997 := by exact prefixLift 2469997
  have htrace : WordTrace (prefixWord ++ tailWord_2469997) baseStart_2469997 baseEnd_2469997 := by
    simpa [prefixWord, tailWord_2469997, baseEnd_2469997] using wordTrace_append hprefix tailTrace_2469997
  have hstable : (prefixWord ++ tailWord_2469997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2469997).length < 2 ^ (prefixWord ++ tailWord_2469997).sum := by decide
  have hdescent : baseEnd_2469997 < baseStart_2469997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2469997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470025 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_2470025 : Nat := 118140960795 + 2470025 * 2 ^ 59
def prefixEnd_2470025 : Nat := 4983230072969 + 3 ^ 40 * 2470025 * 2
def baseEnd_2470025 : Nat := 845540035747869166352045

theorem tailTrace_2470025 : CollatzResearch.WordTrace tailWord_2470025 prefixEnd_2470025 845540035747869166352045 := by
  unfold tailWord_2470025
  simp only [CollatzResearch.WordTrace]
  refine ⟨90089212876528746530179529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60059475251019164353453019 90089212876528746530179529)
  ·
    refine ⟨67566909657396559897634647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90089212876528746530179529 67566909657396559897634647)
    ·
      refine ⟨101350364486094839846451971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67566909657396559897634647 101350364486094839846451971)
      ·
        refine ⟨152025546729142259769677957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101350364486094839846451971 152025546729142259769677957)
        ·
          refine ⟨28504790011714173706814617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152025546729142259769677957 28504790011714173706814617)
          ·
            refine ⟨21378592508785630280110963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28504790011714173706814617 21378592508785630280110963)
            ·
              refine ⟨32067888763178445420166445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21378592508785630280110963 32067888763178445420166445)
              ·
                refine ⟨12025458286191917032562417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32067888763178445420166445 12025458286191917032562417)
                ·
                  refine ⟨9019093714643937774421813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12025458286191917032562417 9019093714643937774421813)
                  ·
                    refine ⟨845540035747869166352045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9019093714643937774421813 845540035747869166352045)
                    ·
                      rfl

theorem cell22_2470025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_2470025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470025 prefixEnd_2470025 := by exact prefixLift 2470025
  have htrace : WordTrace (prefixWord ++ tailWord_2470025) baseStart_2470025 baseEnd_2470025 := by
    simpa [prefixWord, tailWord_2470025, baseEnd_2470025] using wordTrace_append hprefix tailTrace_2470025
  have hstable : (prefixWord ++ tailWord_2470025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470025).length < 2 ^ (prefixWord ++ tailWord_2470025).sum := by decide
  have hdescent : baseEnd_2470025 < baseStart_2470025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470078 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_2470078 : Nat := 118140960795 + 2470078 * 2 ^ 59
def prefixEnd_2470078 : Nat := 4983230072969 + 3 ^ 40 * 2470078 * 2
def baseEnd_2470078 : Nat := 281852726243664898258961

theorem tailTrace_2470078 : CollatzResearch.WordTrace tailWord_2470078 prefixEnd_2470078 281852726243664898258961 := by
  unfold tailWord_2470078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11261393243167092072732361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60060763963557824387905925 11261393243167092072732361)
  ·
    refine ⟨8446044932375319054549271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11261393243167092072732361 8446044932375319054549271)
    ·
      refine ⟨12669067398562978581823907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8446044932375319054549271 12669067398562978581823907)
      ·
        refine ⟨19003601097844467872735861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12669067398562978581823907 19003601097844467872735861)
        ·
          refine ⟨1781587602922918863068987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19003601097844467872735861 1781587602922918863068987)
          ·
            refine ⟨2672381404384378294603481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781587602922918863068987 2672381404384378294603481)
            ·
              refine ⟨2004286053288283720952611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672381404384378294603481 2004286053288283720952611)
              ·
                refine ⟨3006429079932425581428917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004286053288283720952611 3006429079932425581428917)
                ·
                  refine ⟨281852726243664898258961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006429079932425581428917 281852726243664898258961)
                  ·
                    rfl

theorem cell22_2470078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_2470078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470078 prefixEnd_2470078 := by exact prefixLift 2470078
  have htrace : WordTrace (prefixWord ++ tailWord_2470078) baseStart_2470078 baseEnd_2470078 := by
    simpa [prefixWord, tailWord_2470078, baseEnd_2470078] using wordTrace_append hprefix tailTrace_2470078
  have hstable : (prefixWord ++ tailWord_2470078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470078).length < 2 ^ (prefixWord ++ tailWord_2470078).sum := by decide
  have hdescent : baseEnd_2470078 < baseStart_2470078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470085 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_2470085 : Nat := 118140960795 + 2470085 * 2 ^ 59
def prefixEnd_2470085 : Nat := 4983230072969 + 3 ^ 40 * 2470085 * 2
def baseEnd_2470085 : Nat := 845560574974049009851861

theorem tailTrace_2470085 : CollatzResearch.WordTrace tailWord_2470085 prefixEnd_2470085 845560574974049009851861 := by
  unfold tailWord_2470085
  simp only [CollatzResearch.WordTrace]
  refine ⟨90091401256311376777363709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60060934170874251184909139 90091401256311376777363709)
  ·
    refine ⟨33784275471116766291511391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90091401256311376777363709 33784275471116766291511391)
    ·
      refine ⟨50676413206675149437267087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33784275471116766291511391 50676413206675149437267087)
      ·
        refine ⟨76014619810012724155900631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50676413206675149437267087 76014619810012724155900631)
        ·
          refine ⟨114021929715019086233850947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76014619810012724155900631 114021929715019086233850947)
          ·
            refine ⟨171032894572528629350776421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114021929715019086233850947 171032894572528629350776421)
            ·
              refine ⟨32068667732349118003270579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171032894572528629350776421 32068667732349118003270579)
              ·
                refine ⟨48103001598523677004905869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32068667732349118003270579 48103001598523677004905869)
                ·
                  refine ⟨18038625599446378876839701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48103001598523677004905869 18038625599446378876839701)
                  ·
                    refine ⟨845560574974049009851861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18038625599446378876839701 845560574974049009851861)
                    ·
                      rfl

theorem cell22_2470085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_2470085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470085 prefixEnd_2470085 := by exact prefixLift 2470085
  have htrace : WordTrace (prefixWord ++ tailWord_2470085) baseStart_2470085 baseEnd_2470085 := by
    simpa [prefixWord, tailWord_2470085, baseEnd_2470085] using wordTrace_append hprefix tailTrace_2470085
  have hstable : (prefixWord ++ tailWord_2470085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470085).length < 2 ^ (prefixWord ++ tailWord_2470085).sum := by decide
  have hdescent : baseEnd_2470085 < baseStart_2470085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470119 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2470119 : Nat := 118140960795 + 2470119 * 2 ^ 59
def prefixEnd_2470119 : Nat := 4983230072969 + 3 ^ 40 * 2470119 * 2
def baseEnd_2470119 : Nat := 845572213868884254501757

theorem tailTrace_2470119 : CollatzResearch.WordTrace tailWord_2470119 prefixEnd_2470119 845572213868884254501757 := by
  unfold tailWord_2470119
  simp only [CollatzResearch.WordTrace]
  refine ⟨90092641338188200584101411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60061760892125467056067607 90092641338188200584101411)
  ·
    refine ⟨135138962007282300876152117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90092641338188200584101411 135138962007282300876152117)
    ·
      refine ⟨12669277688182715707139261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135138962007282300876152117 12669277688182715707139261)
      ·
        refine ⟨4750979133068518390177223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12669277688182715707139261 4750979133068518390177223)
        ·
          refine ⟨7126468699602777585265835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4750979133068518390177223 7126468699602777585265835)
          ·
            refine ⟨10689703049404166377898753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7126468699602777585265835 10689703049404166377898753)
            ·
              refine ⟨8017277287053124783424065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10689703049404166377898753 8017277287053124783424065)
              ·
                refine ⟨6012957965289843587568049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8017277287053124783424065 6012957965289843587568049)
                ·
                  refine ⟨4509718473967382690676037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6012957965289843587568049 4509718473967382690676037)
                  ·
                    refine ⟨845572213868884254501757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509718473967382690676037 845572213868884254501757)
                    ·
                      rfl

theorem cell22_2470119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2470119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470119 prefixEnd_2470119 := by exact prefixLift 2470119
  have htrace : WordTrace (prefixWord ++ tailWord_2470119) baseStart_2470119 baseEnd_2470119 := by
    simpa [prefixWord, tailWord_2470119, baseEnd_2470119] using wordTrace_append hprefix tailTrace_2470119
  have hstable : (prefixWord ++ tailWord_2470119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470119).length < 2 ^ (prefixWord ++ tailWord_2470119).sum := by decide
  have hdescent : baseEnd_2470119 < baseStart_2470119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470151 : List Nat := [1, 1, 4, 5, 1, 1, 3, 6]
def baseStart_2470151 : Nat := 118140960795 + 2470151 * 2 ^ 59
def prefixEnd_2470151 : Nat := 4983230072969 + 3 ^ 40 * 2470151 * 2
def baseEnd_2470151 : Nat := 93953685346982981966851

theorem tailTrace_2470151 : CollatzResearch.WordTrace tailWord_2470151 prefixEnd_2470151 93953685346982981966851 := by
  unfold tailWord_2470151
  simp only [CollatzResearch.WordTrace]
  refine ⟨90093808474072270049266307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60062538982714846699510871 90093808474072270049266307)
  ·
    refine ⟨135140712711108405073899461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90093808474072270049266307 135140712711108405073899461)
    ·
      refine ⟨25338883633332825951356149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135140712711108405073899461 25338883633332825951356149)
      ·
        refine ⟨2375520340624952432939639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25338883633332825951356149 2375520340624952432939639)
        ·
          refine ⟨3563280510937428649409459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375520340624952432939639 3563280510937428649409459)
          ·
            refine ⟨5344920766406142974114189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563280510937428649409459 5344920766406142974114189)
            ·
              refine ⟨2004345287402303615292821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5344920766406142974114189 2004345287402303615292821)
              ·
                refine ⟨93953685346982981966851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2004345287402303615292821 93953685346982981966851)
                ·
                  rfl

theorem cell22_2470151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 6].length) (baseStart_2470151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470151 prefixEnd_2470151 := by exact prefixLift 2470151
  have htrace : WordTrace (prefixWord ++ tailWord_2470151) baseStart_2470151 baseEnd_2470151 := by
    simpa [prefixWord, tailWord_2470151, baseEnd_2470151] using wordTrace_append hprefix tailTrace_2470151
  have hstable : (prefixWord ++ tailWord_2470151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470151).length < 2 ^ (prefixWord ++ tailWord_2470151).sum := by decide
  have hdescent : baseEnd_2470151 < baseStart_2470151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470177 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2470177 : Nat := 118140960795 + 2470177 * 2 ^ 59
def prefixEnd_2470177 : Nat := 4983230072969 + 3 ^ 40 * 2470177 * 2
def baseEnd_2470177 : Nat := 845592068454191436551579

theorem tailTrace_2470177 : CollatzResearch.WordTrace tailWord_2470177 prefixEnd_2470177 845592068454191436551579 := by
  unfold tailWord_2470177
  simp only [CollatzResearch.WordTrace]
  refine ⟨90094756771978076489712785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60063171181318717659808523 90094756771978076489712785)
  ·
    refine ⟨67571067578983557367284589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90094756771978076489712785 67571067578983557367284589)
    ·
      refine ⟨25339150342118834012731721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67571067578983557367284589 25339150342118834012731721)
      ·
        refine ⟨19004362756589125509548791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25339150342118834012731721 19004362756589125509548791)
        ·
          refine ⟨28506544134883688264323187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19004362756589125509548791 28506544134883688264323187)
          ·
            refine ⟨42759816202325532396484781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28506544134883688264323187 42759816202325532396484781)
            ·
              refine ⟨16034931075872074648681793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42759816202325532396484781 16034931075872074648681793)
              ·
                refine ⟨12026198306904055986511345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16034931075872074648681793 12026198306904055986511345)
                ·
                  refine ⟨9019648730178041989883509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12026198306904055986511345 9019648730178041989883509)
                  ·
                    refine ⟨845592068454191436551579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9019648730178041989883509 845592068454191436551579)
                    ·
                      rfl

theorem cell22_2470177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2470177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470177 prefixEnd_2470177 := by exact prefixLift 2470177
  have htrace : WordTrace (prefixWord ++ tailWord_2470177) baseStart_2470177 baseEnd_2470177 := by
    simpa [prefixWord, tailWord_2470177, baseEnd_2470177] using wordTrace_append hprefix tailTrace_2470177
  have hstable : (prefixWord ++ tailWord_2470177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470177).length < 2 ^ (prefixWord ++ tailWord_2470177).sum := by decide
  have hdescent : baseEnd_2470177 < baseStart_2470177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470192 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_2470192 : Nat := 118140960795 + 2470192 * 2 ^ 59
def prefixEnd_2470192 : Nat := 4983230072969 + 3 ^ 40 * 2470192 * 2
def baseEnd_2470192 : Nat := 845597203260736397426533

theorem tailTrace_2470192 : CollatzResearch.WordTrace tailWord_2470192 prefixEnd_2470192 845597203260736397426533 := by
  unfold tailWord_2470192
  simp only [CollatzResearch.WordTrace]
  refine ⟨45047651933461867025754415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60063535911282489367672553 45047651933461867025754415)
  ·
    refine ⟨67571477900192800538631623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45047651933461867025754415 67571477900192800538631623)
    ·
      refine ⟨101357216850289200807947435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67571477900192800538631623 101357216850289200807947435)
      ·
        refine ⟨152035825275433801211921153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101357216850289200807947435 152035825275433801211921153)
        ·
          refine ⟨114026868956575350908940865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152035825275433801211921153 114026868956575350908940865)
          ·
            refine ⟨85520151717431513181705649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114026868956575350908940865 85520151717431513181705649)
            ·
              refine ⟨64140113788073634886279237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85520151717431513181705649 64140113788073634886279237)
              ·
                refine ⟨12026271335263806541177357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64140113788073634886279237 12026271335263806541177357)
                ·
                  refine ⟨4509851750723927452941509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12026271335263806541177357 4509851750723927452941509)
                  ·
                    refine ⟨845597203260736397426533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4509851750723927452941509 845597203260736397426533)
                    ·
                      rfl

theorem cell22_2470192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_2470192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470192 prefixEnd_2470192 := by exact prefixLift 2470192
  have htrace : WordTrace (prefixWord ++ tailWord_2470192) baseStart_2470192 baseEnd_2470192 := by
    simpa [prefixWord, tailWord_2470192, baseEnd_2470192] using wordTrace_append hprefix tailTrace_2470192
  have hstable : (prefixWord ++ tailWord_2470192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470192).length < 2 ^ (prefixWord ++ tailWord_2470192).sum := by decide
  have hdescent : baseEnd_2470192 < baseStart_2470192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470207 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 6]
def baseStart_2470207 : Nat := 118140960795 + 2470207 * 2 ^ 59
def prefixEnd_2470207 : Nat := 4983230072969 + 3 ^ 40 * 2470207 * 2
def baseEnd_2470207 : Nat := 281867446022427119433829

theorem tailTrace_2470207 : CollatzResearch.WordTrace tailWord_2470207 prefixEnd_2470207 281867446022427119433829 := by
  unfold tailWord_2470207
  simp only [CollatzResearch.WordTrace]
  refine ⟨90095850961869391613304875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60063900641246261075536583 90095850961869391613304875)
  ·
    refine ⟨135143776442804087419957313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90095850961869391613304875 135143776442804087419957313)
    ·
      refine ⟨101357832332103065564967985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135143776442804087419957313 101357832332103065564967985)
      ·
        refine ⟨76018374249077299173725989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101357832332103065564967985 76018374249077299173725989)
        ·
          refine ⟨14253445171701993595073623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76018374249077299173725989 14253445171701993595073623)
          ·
            refine ⟨21380167757552990392610435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14253445171701993595073623 21380167757552990392610435)
            ·
              refine ⟨32070251636329485588915653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21380167757552990392610435 32070251636329485588915653)
              ·
                refine ⟨6013172181811778547921685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32070251636329485588915653 6013172181811778547921685)
                ·
                  refine ⟨281867446022427119433829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6013172181811778547921685 281867446022427119433829)
                  ·
                    rfl

theorem cell22_2470207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_2470207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470207 prefixEnd_2470207 := by exact prefixLift 2470207
  have htrace : WordTrace (prefixWord ++ tailWord_2470207) baseStart_2470207 baseEnd_2470207 := by
    simpa [prefixWord, tailWord_2470207, baseEnd_2470207] using wordTrace_append hprefix tailTrace_2470207
  have hstable : (prefixWord ++ tailWord_2470207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470207).length < 2 ^ (prefixWord ++ tailWord_2470207).sum := by decide
  have hdescent : baseEnd_2470207 < baseStart_2470207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470239 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 4, 3]
def baseStart_2470239 : Nat := 118140960795 + 2470239 * 2 ^ 59
def prefixEnd_2470239 : Nat := 4983230072969 + 3 ^ 40 * 2470239 * 2
def baseEnd_2470239 : Nat := 845613292321243941501389

theorem tailTrace_2470239 : CollatzResearch.WordTrace tailWord_2470239 prefixEnd_2470239 845613292321243941501389 := by
  unfold tailWord_2470239
  simp only [CollatzResearch.WordTrace]
  refine ⟨90097018097753461078469771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60064678731835640718979847 90097018097753461078469771)
  ·
    refine ⟨135145527146630191617704657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90097018097753461078469771 135145527146630191617704657)
    ·
      refine ⟨101359145359972643713278493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135145527146630191617704657 101359145359972643713278493)
      ·
        refine ⟨38009679509989741392479435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101359145359972643713278493 38009679509989741392479435)
        ·
          refine ⟨57014519264984612088719153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38009679509989741392479435 57014519264984612088719153)
          ·
            refine ⟨42760889448738459066539365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57014519264984612088719153 42760889448738459066539365)
            ·
              refine ⟨8017666771638461074976131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42760889448738459066539365 8017666771638461074976131)
              ·
                refine ⟨12026500157457691612464197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8017666771638461074976131 12026500157457691612464197)
                ·
                  refine ⟨2254968779523317177337037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12026500157457691612464197 2254968779523317177337037)
                  ·
                    refine ⟨845613292321243941501389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254968779523317177337037 845613292321243941501389)
                    ·
                      rfl

theorem cell22_2470239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_2470239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470239 prefixEnd_2470239 := by exact prefixLift 2470239
  have htrace : WordTrace (prefixWord ++ tailWord_2470239) baseStart_2470239 baseEnd_2470239 := by
    simpa [prefixWord, tailWord_2470239, baseEnd_2470239] using wordTrace_append hprefix tailTrace_2470239
  have hstable : (prefixWord ++ tailWord_2470239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470239).length < 2 ^ (prefixWord ++ tailWord_2470239).sum := by decide
  have hdescent : baseEnd_2470239 < baseStart_2470239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470256 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 2, 3]
def baseStart_2470256 : Nat := 118140960795 + 2470256 * 2 ^ 59
def prefixEnd_2470256 : Nat := 4983230072969 + 3 ^ 40 * 2470256 * 2
def baseEnd_2470256 : Nat := 845619111768661563826337

theorem tailTrace_2470256 : CollatzResearch.WordTrace tailWord_2470256 prefixEnd_2470256 845619111768661563826337 := by
  unfold tailWord_2470256
  simp only [CollatzResearch.WordTrace]
  refine ⟨45048819069345936490919311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60065092092461248654559081 45048819069345936490919311)
  ·
    refine ⟨67573228604018904736378967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45048819069345936490919311 67573228604018904736378967)
    ·
      refine ⟨101359842906028357104568451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67573228604018904736378967 101359842906028357104568451)
      ·
        refine ⟨152039764359042535656852677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101359842906028357104568451 152039764359042535656852677)
        ·
          refine ⟨28507455817320475435659877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152039764359042535656852677 28507455817320475435659877)
          ·
            refine ⟨5345147965747589144186227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28507455817320475435659877 5345147965747589144186227)
            ·
              refine ⟨8017721948621383716279341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345147965747589144186227 8017721948621383716279341)
              ·
                refine ⟨3006645730733018893604753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8017721948621383716279341 3006645730733018893604753)
                ·
                  refine ⟨2254984298049764170203565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3006645730733018893604753 2254984298049764170203565)
                  ·
                    refine ⟨845619111768661563826337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2254984298049764170203565 845619111768661563826337)
                    ·
                      rfl

theorem cell22_2470256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 2, 3].length) (baseStart_2470256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470256 prefixEnd_2470256 := by exact prefixLift 2470256
  have htrace : WordTrace (prefixWord ++ tailWord_2470256) baseStart_2470256 baseEnd_2470256 := by
    simpa [prefixWord, tailWord_2470256, baseEnd_2470256] using wordTrace_append hprefix tailTrace_2470256
  have hstable : (prefixWord ++ tailWord_2470256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470256).length < 2 ^ (prefixWord ++ tailWord_2470256).sum := by decide
  have hdescent : baseEnd_2470256 < baseStart_2470256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470292 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2470292 : Nat := 118140960795 + 2470292 * 2 ^ 59
def prefixEnd_2470292 : Nat := 4983230072969 + 3 ^ 40 * 2470292 * 2
def baseEnd_2470292 : Nat := 281877145101456489975409

theorem tailTrace_2470292 : CollatzResearch.WordTrace tailWord_2470292 prefixEnd_2470292 281877145101456489975409 := by
  unfold tailWord_2470292
  simp only [CollatzResearch.WordTrace]
  refine ⟨45049475583280725565074565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60065967444374300753432753 45049475583280725565074565)
  ·
    refine ⟨8446776671865136043451481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45049475583280725565074565 8446776671865136043451481)
    ·
      refine ⟨6335082503898852032588611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8446776671865136043451481 6335082503898852032588611)
      ·
        refine ⟨9502623755848278048882917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6335082503898852032588611 9502623755848278048882917)
        ·
          refine ⟨1781741954221552134165547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9502623755848278048882917 1781741954221552134165547)
          ·
            refine ⟨2672612931332328201248321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781741954221552134165547 2672612931332328201248321)
            ·
              refine ⟨2004459698499246150936241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672612931332328201248321 2004459698499246150936241)
              ·
                refine ⟨1503344773874434613202181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004459698499246150936241 1503344773874434613202181)
                ·
                  refine ⟨281877145101456489975409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503344773874434613202181 281877145101456489975409)
                  ·
                    rfl

theorem cell22_2470292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2470292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470292 prefixEnd_2470292 := by exact prefixLift 2470292
  have htrace : WordTrace (prefixWord ++ tailWord_2470292) baseStart_2470292 baseEnd_2470292 := by
    simpa [prefixWord, tailWord_2470292, baseEnd_2470292] using wordTrace_append hprefix tailTrace_2470292
  have hstable : (prefixWord ++ tailWord_2470292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470292).length < 2 ^ (prefixWord ++ tailWord_2470292).sum := by decide
  have hdescent : baseEnd_2470292 < baseStart_2470292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470348 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_2470348 : Nat := 118140960795 + 2470348 * 2 ^ 59
def prefixEnd_2470348 : Nat := 4983230072969 + 3 ^ 40 * 2470348 * 2
def baseEnd_2470348 : Nat := 281883535082934663508685

theorem tailTrace_2470348 : CollatzResearch.WordTrace tailWord_2470348 prefixEnd_2470348 281883535082934663508685 := by
  unfold tailWord_2470348
  simp only [CollatzResearch.WordTrace]
  refine ⟨45050496827179286347093849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60067329102905715129458465 45050496827179286347093849)
  ·
    refine ⟨33787872620384464760320387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45050496827179286347093849 33787872620384464760320387)
    ·
      refine ⟨50681808930576697140480581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33787872620384464760320387 50681808930576697140480581)
      ·
        refine ⟨9502839174483130713840109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50681808930576697140480581 9502839174483130713840109)
        ·
          refine ⟨3563564690431174017690041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9502839174483130713840109 3563564690431174017690041)
          ·
            refine ⟨2672673517823380513267531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3563564690431174017690041 2672673517823380513267531)
            ·
              refine ⟨4009010276735070769901297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672673517823380513267531 4009010276735070769901297)
              ·
                refine ⟨3006757707551303077425973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009010276735070769901297 3006757707551303077425973)
                ·
                  refine ⟨281883535082934663508685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006757707551303077425973 281883535082934663508685)
                  ·
                    rfl

theorem cell22_2470348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_2470348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470348 prefixEnd_2470348 := by exact prefixLift 2470348
  have htrace : WordTrace (prefixWord ++ tailWord_2470348) baseStart_2470348 baseEnd_2470348 := by
    simpa [prefixWord, tailWord_2470348, baseEnd_2470348] using wordTrace_append hprefix tailTrace_2470348
  have hstable : (prefixWord ++ tailWord_2470348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470348).length < 2 ^ (prefixWord ++ tailWord_2470348).sum := by decide
  have hdescent : baseEnd_2470348 < baseStart_2470348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470378 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2470378 : Nat := 118140960795 + 2470378 * 2 ^ 59
def prefixEnd_2470378 : Nat := 4983230072969 + 3 ^ 40 * 2470378 * 2
def baseEnd_2470378 : Nat := 845660874861893912275963

theorem tailTrace_2470378 : CollatzResearch.WordTrace tailWord_2470378 prefixEnd_2470378 845660874861893912275963 := by
  unfold tailWord_2470378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22525521961062471954444947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60068058562833258545186525 22525521961062471954444947)
  ·
    refine ⟨33788282941593707931667421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22525521961062471954444947 33788282941593707931667421)
    ·
      refine ⟨12670606103097640474375283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33788282941593707931667421 12670606103097640474375283)
      ·
        refine ⟨19005909154646460711562925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12670606103097640474375283 19005909154646460711562925)
        ·
          refine ⟨7127215932992422766836097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19005909154646460711562925 7127215932992422766836097)
          ·
            refine ⟨5345411949744317075127073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7127215932992422766836097 5345411949744317075127073)
            ·
              refine ⟨4009058962308237806345305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5345411949744317075127073 4009058962308237806345305)
              ·
                refine ⟨3006794221731178354758979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009058962308237806345305 3006794221731178354758979)
                ·
                  refine ⟨4510191332596767532138469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3006794221731178354758979 4510191332596767532138469)
                  ·
                    refine ⟨845660874861893912275963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4510191332596767532138469 845660874861893912275963)
                    ·
                      rfl

theorem cell22_2470378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2470378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470378 prefixEnd_2470378 := by exact prefixLift 2470378
  have htrace : WordTrace (prefixWord ++ tailWord_2470378) baseStart_2470378 baseEnd_2470378 := by
    simpa [prefixWord, tailWord_2470378, baseEnd_2470378] using wordTrace_append hprefix tailTrace_2470378
  have hstable : (prefixWord ++ tailWord_2470378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470378).length < 2 ^ (prefixWord ++ tailWord_2470378).sum := by decide
  have hdescent : baseEnd_2470378 < baseStart_2470378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470449 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 9]
def baseStart_2470449 : Nat := 118140960795 + 2470449 * 2 ^ 59
def prefixEnd_2470449 : Nat := 4983230072969 + 3 ^ 40 * 2470449 * 2
def baseEnd_2470449 : Nat := 281895059870957797916915

theorem tailTrace_2470449 : CollatzResearch.WordTrace tailWord_2470449 prefixEnd_2470449 281895059870957797916915 := by
  unfold tailWord_2470449
  simp only [CollatzResearch.WordTrace]
  refine ⟨90104677426992666943614401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60069784951328444629076267 90104677426992666943614401)
  ·
    refine ⟨67578508070244500207710801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90104677426992666943614401 67578508070244500207710801)
    ·
      refine ⟨50683881052683375155783101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67578508070244500207710801 50683881052683375155783101)
      ·
        refine ⟨19006455394756265683418663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50683881052683375155783101 19006455394756265683418663)
        ·
          refine ⟨28509683092134398525127995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19006455394756265683418663 28509683092134398525127995)
          ·
            refine ⟨42764524638201597787691993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28509683092134398525127995 42764524638201597787691993)
            ·
              refine ⟨32073393478651198340768995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42764524638201597787691993 32073393478651198340768995)
              ·
                refine ⟨48110090217976797511153493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32073393478651198340768995 48110090217976797511153493)
                ·
                  refine ⟨281895059870957797916915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48110090217976797511153493 281895059870957797916915)
                  ·
                    rfl

theorem cell22_2470449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_2470449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470449 prefixEnd_2470449 := by exact prefixLift 2470449
  have htrace : WordTrace (prefixWord ++ tailWord_2470449) baseStart_2470449 baseEnd_2470449 := by
    simpa [prefixWord, tailWord_2470449, baseEnd_2470449] using wordTrace_append hprefix tailTrace_2470449
  have hstable : (prefixWord ++ tailWord_2470449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470449).length < 2 ^ (prefixWord ++ tailWord_2470449).sum := by decide
  have hdescent : baseEnd_2470449 < baseStart_2470449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470481 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2470481 : Nat := 118140960795 + 2470481 * 2 ^ 59
def prefixEnd_2470481 : Nat := 4983230072969 + 3 ^ 40 * 2470481 * 2
def baseEnd_2470481 : Nat := 845696133866835976950647

theorem tailTrace_2470481 : CollatzResearch.WordTrace tailWord_2470481 prefixEnd_2470481 845696133866835976950647 := by
  unfold tailWord_2470481
  simp only [CollatzResearch.WordTrace]
  refine ⟨90105844562876736408779297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60070563041917824272519531 90105844562876736408779297)
  ·
    refine ⟨67579383422157552306584473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90105844562876736408779297 67579383422157552306584473)
    ·
      refine ⟨50684537566618164229938355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67579383422157552306584473 50684537566618164229938355)
      ·
        refine ⟨76026806349927246344907533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50684537566618164229938355 76026806349927246344907533)
        ·
          refine ⟨28510052381222717379340325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76026806349927246344907533 28510052381222717379340325)
          ·
            refine ⟨5345634821479259508626311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28510052381222717379340325 5345634821479259508626311)
            ·
              refine ⟨8018452232218889262939467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5345634821479259508626311 8018452232218889262939467)
              ·
                refine ⟨12027678348328333894409201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018452232218889262939467 12027678348328333894409201)
                ·
                  refine ⟨9020758761246250420806901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12027678348328333894409201 9020758761246250420806901)
                  ·
                    refine ⟨845696133866835976950647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9020758761246250420806901 845696133866835976950647)
                    ·
                      rfl

theorem cell22_2470481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2470481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470481 prefixEnd_2470481 := by exact prefixLift 2470481
  have htrace : WordTrace (prefixWord ++ tailWord_2470481) baseStart_2470481 baseEnd_2470481 := by
    simpa [prefixWord, tailWord_2470481, baseEnd_2470481] using wordTrace_append hprefix tailTrace_2470481
  have hstable : (prefixWord ++ tailWord_2470481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470481).length < 2 ^ (prefixWord ++ tailWord_2470481).sum := by decide
  have hdescent : baseEnd_2470481 < baseStart_2470481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470496 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_2470496 : Nat := 118140960795 + 2470496 * 2 ^ 59
def prefixEnd_2470496 : Nat := 4983230072969 + 3 ^ 40 * 2470496 * 2
def baseEnd_2470496 : Nat := 845701268673380937825601

theorem tailTrace_2470496 : CollatzResearch.WordTrace tailWord_2470496 prefixEnd_2470496 845701268673380937825601 := by
  unfold tailWord_2470496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45053195828911196985287671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60070927771881595980383561 45053195828911196985287671)
  ·
    refine ⟨67579793743366795477931507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45053195828911196985287671 67579793743366795477931507)
    ·
      refine ⟨101369690615050193216897261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67579793743366795477931507 101369690615050193216897261)
      ·
        refine ⟨38013633980643822456336473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101369690615050193216897261 38013633980643822456336473)
        ·
          refine ⟨28510225485482866842252355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38013633980643822456336473 28510225485482866842252355)
          ·
            refine ⟨42765338228224300263378533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28510225485482866842252355 42765338228224300263378533)
            ·
              refine ⟨8018500917792056299383475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42765338228224300263378533 8018500917792056299383475)
              ·
                refine ⟨12027751376688084449075213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8018500917792056299383475 12027751376688084449075213)
                ·
                  refine ⟨4510406766258031668403205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12027751376688084449075213 4510406766258031668403205)
                  ·
                    refine ⟨845701268673380937825601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4510406766258031668403205 845701268673380937825601)
                    ·
                      rfl

theorem cell22_2470496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_2470496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470496 prefixEnd_2470496 := by exact prefixLift 2470496
  have htrace : WordTrace (prefixWord ++ tailWord_2470496) baseStart_2470496 baseEnd_2470496 := by
    simpa [prefixWord, tailWord_2470496, baseEnd_2470496] using wordTrace_append hprefix tailTrace_2470496
  have hstable : (prefixWord ++ tailWord_2470496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470496).length < 2 ^ (prefixWord ++ tailWord_2470496).sum := by decide
  have hdescent : baseEnd_2470496 < baseStart_2470496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470517 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 5]
def baseStart_2470517 : Nat := 118140960795 + 2470517 * 2 ^ 59
def prefixEnd_2470517 : Nat := 4983230072969 + 3 ^ 40 * 2470517 * 2
def baseEnd_2470517 : Nat := 281902819134181294350179

theorem tailTrace_2470517 : CollatzResearch.WordTrace tailWord_2470517 prefixEnd_2470517 281902819134181294350179 := by
  unfold tailWord_2470517
  simp only [CollatzResearch.WordTrace]
  refine ⟨90107157590746314557089805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60071438393830876371393203 90107157590746314557089805)
  ·
    refine ⟨33790184096529867958908677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90107157590746314557089805 33790184096529867958908677)
    ·
      refine ⟨6335659518099350242295377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33790184096529867958908677 6335659518099350242295377)
      ·
        refine ⟨4751744638574512681721533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6335659518099350242295377 4751744638574512681721533)
        ·
          refine ⟨1781904239465442255645575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4751744638574512681721533 1781904239465442255645575)
          ·
            refine ⟨2672856359198163383468363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1781904239465442255645575 2672856359198163383468363)
            ·
              refine ⟨4009284538797245075202545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2672856359198163383468363 4009284538797245075202545)
              ·
                refine ⟨3006963404097933806401909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4009284538797245075202545 3006963404097933806401909)
                ·
                  refine ⟨281902819134181294350179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3006963404097933806401909 281902819134181294350179)
                  ·
                    rfl

theorem cell22_2470517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_2470517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470517 prefixEnd_2470517 := by exact prefixLift 2470517
  have htrace : WordTrace (prefixWord ++ tailWord_2470517) baseStart_2470517 baseEnd_2470517 := by
    simpa [prefixWord, tailWord_2470517, baseEnd_2470517] using wordTrace_append hprefix tailTrace_2470517
  have hstable : (prefixWord ++ tailWord_2470517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470517).length < 2 ^ (prefixWord ++ tailWord_2470517).sum := by decide
  have hdescent : baseEnd_2470517 < baseStart_2470517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470528 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_2470528 : Nat := 118140960795 + 2470528 * 2 ^ 59
def prefixEnd_2470528 : Nat := 4983230072969 + 3 ^ 40 * 2470528 * 2
def baseEnd_2470528 : Nat := 281904074309114507008501

theorem tailTrace_2470528 : CollatzResearch.WordTrace tailWord_2470528 prefixEnd_2470528 281904074309114507008501 := by
  unfold tailWord_2470528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45053779396853231717870119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60071705862470975623826825 45053779396853231717870119)
  ·
    refine ⟨67580669095279847576805179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45053779396853231717870119 67580669095279847576805179)
    ·
      refine ⟨101371003642919771365207769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67580669095279847576805179 101371003642919771365207769)
      ·
        refine ⟨76028252732189828523905827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101371003642919771365207769 76028252732189828523905827)
        ·
          refine ⟨114042379098284742785858741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76028252732189828523905827 114042379098284742785858741)
          ·
            refine ⟨10691473040464194636174257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114042379098284742785858741 10691473040464194636174257)
            ·
              refine ⟨8018604780348145977130693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10691473040464194636174257 8018604780348145977130693)
              ·
                refine ⟨1503488396315277370712005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8018604780348145977130693 1503488396315277370712005)
                ·
                  refine ⟨281904074309114507008501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503488396315277370712005 281904074309114507008501)
                  ·
                    rfl

theorem cell22_2470528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_2470528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470528 prefixEnd_2470528 := by exact prefixLift 2470528
  have htrace : WordTrace (prefixWord ++ tailWord_2470528) baseStart_2470528 baseEnd_2470528 := by
    simpa [prefixWord, tailWord_2470528, baseEnd_2470528] using wordTrace_append hprefix tailTrace_2470528
  have hstable : (prefixWord ++ tailWord_2470528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470528).length < 2 ^ (prefixWord ++ tailWord_2470528).sum := by decide
  have hdescent : baseEnd_2470528 < baseStart_2470528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470558 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2470558 : Nat := 118140960795 + 2470558 * 2 ^ 59
def prefixEnd_2470558 : Nat := 4983230072969 + 3 ^ 40 * 2470558 * 2
def baseEnd_2470558 : Nat := 845722492540433442775411

theorem tailTrace_2470558 : CollatzResearch.WordTrace tailWord_2470558 prefixEnd_2470558 845722492540433442775411 := by
  unfold tailWord_2470558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263581622949722319916541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60072435322398519039554885 11263581622949722319916541)
  ·
    refine ⟨4223843108606145869968703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11263581622949722319916541 4223843108606145869968703)
    ·
      refine ⟨6335764662909218804953055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4223843108606145869968703 6335764662909218804953055)
      ·
        refine ⟨9503646994363828207429583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6335764662909218804953055 9503646994363828207429583)
        ·
          refine ⟨14255470491545742311144375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9503646994363828207429583 14255470491545742311144375)
          ·
            refine ⟨21383205737318613466716563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14255470491545742311144375 21383205737318613466716563)
            ·
              refine ⟨32074808605977920200074845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21383205737318613466716563 32074808605977920200074845)
              ·
                refine ⟨12028053227241720075028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32074808605977920200074845 12028053227241720075028067)
                ·
                  refine ⟨18042079840862580112542101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12028053227241720075028067 18042079840862580112542101)
                  ·
                    refine ⟨845722492540433442775411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18042079840862580112542101 845722492540433442775411)
                    ·
                      rfl

theorem cell22_2470558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2470558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470558 prefixEnd_2470558 := by exact prefixLift 2470558
  have htrace : WordTrace (prefixWord ++ tailWord_2470558) baseStart_2470558 baseEnd_2470558 := by
    simpa [prefixWord, tailWord_2470558, baseEnd_2470558] using wordTrace_append hprefix tailTrace_2470558
  have hstable : (prefixWord ++ tailWord_2470558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470558).length < 2 ^ (prefixWord ++ tailWord_2470558).sum := by decide
  have hdescent : baseEnd_2470558 < baseStart_2470558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470573 : List Nat := [1, 5, 2, 1, 1, 4, 8]
def baseStart_2470573 : Nat := 118140960795 + 2470573 * 2 ^ 59
def prefixEnd_2470573 : Nat := 4983230072969 + 3 ^ 40 * 2470573 * 2
def baseEnd_2470573 : Nat := 31323245457295496431495

theorem tailTrace_2470573 : CollatzResearch.WordTrace tailWord_2470573 prefixEnd_2470573 31323245457295496431495 := by
  unfold tailWord_2470573
  simp only [CollatzResearch.WordTrace]
  refine ⟨90109200078543436121128373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60072800052362290747418915 90109200078543436121128373)
  ·
    refine ⟨8447737507363447136355785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90109200078543436121128373 8447737507363447136355785)
    ·
      refine ⟨6335803130522585352266839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8447737507363447136355785 6335803130522585352266839)
      ·
        refine ⟨9503704695783878028400259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6335803130522585352266839 9503704695783878028400259)
        ·
          refine ⟨14255557043675817042600389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9503704695783878028400259 14255557043675817042600389)
          ·
            refine ⟨2672916945689215695487573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14255557043675817042600389 2672916945689215695487573)
            ·
              refine ⟨31323245457295496431495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2672916945689215695487573 31323245457295496431495)
              ·
                rfl

theorem cell22_2470573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 8].length) (baseStart_2470573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470573 prefixEnd_2470573 := by exact prefixLift 2470573
  have htrace : WordTrace (prefixWord ++ tailWord_2470573) baseStart_2470573 baseEnd_2470573 := by
    simpa [prefixWord, tailWord_2470573, baseEnd_2470573] using wordTrace_append hprefix tailTrace_2470573
  have hstable : (prefixWord ++ tailWord_2470573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470573).length < 2 ^ (prefixWord ++ tailWord_2470573).sum := by decide
  have hdescent : baseEnd_2470573 < baseStart_2470573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470586 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_2470586 : Nat := 118140960795 + 2470586 * 2 ^ 59
def prefixEnd_2470586 : Nat := 4983230072969 + 3 ^ 40 * 2470586 * 2
def baseEnd_2470586 : Nat := 845732077512650703075325

theorem tailTrace_2470586 : CollatzResearch.WordTrace tailWord_2470586 prefixEnd_2470586 845732077512650703075325 := by
  unfold tailWord_2470586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22527418556874084835337903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60073116151664226227567741 22527418556874084835337903)
  ·
    refine ⟨33791127835311127253006855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22527418556874084835337903 33791127835311127253006855)
    ·
      refine ⟨50686691752966690879510283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33791127835311127253006855 50686691752966690879510283)
      ·
        refine ⟨76030037629450036319265425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50686691752966690879510283 76030037629450036319265425)
        ·
          refine ⟨57022528222087527239449069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76030037629450036319265425 57022528222087527239449069)
          ·
            refine ⟨21383448083282822714793401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57022528222087527239449069 21383448083282822714793401)
            ·
              refine ⟨16037586062462117036095051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21383448083282822714793401 16037586062462117036095051)
              ·
                refine ⟨24056379093693175554142577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16037586062462117036095051 24056379093693175554142577)
                ·
                  refine ⟨18042284320269881665606933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24056379093693175554142577 18042284320269881665606933)
                  ·
                    refine ⟨845732077512650703075325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18042284320269881665606933 845732077512650703075325)
                    ·
                      rfl

theorem cell22_2470586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_2470586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470586 prefixEnd_2470586 := by exact prefixLift 2470586
  have htrace : WordTrace (prefixWord ++ tailWord_2470586) baseStart_2470586 baseEnd_2470586 := by
    simpa [prefixWord, tailWord_2470586, baseEnd_2470586] using wordTrace_append hprefix tailTrace_2470586
  have hstable : (prefixWord ++ tailWord_2470586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470586).length < 2 ^ (prefixWord ++ tailWord_2470586).sum := by decide
  have hdescent : baseEnd_2470586 < baseStart_2470586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470639 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 1, 3]
def baseStart_2470639 : Nat := 118140960795 + 2470639 * 2 ^ 59
def prefixEnd_2470639 : Nat := 4983230072969 + 3 ^ 40 * 2470639 * 2
def baseEnd_2470639 : Nat := 845750220495776231500163

theorem tailTrace_2470639 : CollatzResearch.WordTrace tailWord_2470639 prefixEnd_2470639 845750220495776231500163 := by
  unfold tailWord_2470639
  simp only [CollatzResearch.WordTrace]
  refine ⟨90111607296304329393030971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60074404864202886262020647 90111607296304329393030971)
  ·
    refine ⟨135167410944456494089546457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90111607296304329393030971 135167410944456494089546457)
    ·
      refine ⟨101375558208342370567159843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135167410944456494089546457 101375558208342370567159843)
      ·
        refine ⟨152063337312513555850739765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101375558208342370567159843 152063337312513555850739765)
        ·
          refine ⟨14255937873048145861006853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152063337312513555850739765 14255937873048145861006853)
          ·
            refine ⟨2672988351196527348938785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14255937873048145861006853 2672988351196527348938785)
            ·
              refine ⟨2004741263397395511704089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672988351196527348938785 2004741263397395511704089)
              ·
                refine ⟨1503555947548046633778067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2004741263397395511704089 1503555947548046633778067)
                ·
                  refine ⟨2255333921322069950667101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503555947548046633778067 2255333921322069950667101)
                  ·
                    refine ⟨845750220495776231500163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255333921322069950667101 845750220495776231500163)
                    ·
                      rfl

theorem cell22_2470639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_2470639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470639 prefixEnd_2470639 := by exact prefixLift 2470639
  have htrace : WordTrace (prefixWord ++ tailWord_2470639) baseStart_2470639 baseEnd_2470639 := by
    simpa [prefixWord, tailWord_2470639, baseEnd_2470639] using wordTrace_append hprefix tailTrace_2470639
  have hstable : (prefixWord ++ tailWord_2470639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470639).length < 2 ^ (prefixWord ++ tailWord_2470639).sum := by decide
  have hdescent : baseEnd_2470639 < baseStart_2470639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470663 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 8]
def baseStart_2470663 : Nat := 118140960795 + 2470663 * 2 ^ 59
def prefixEnd_2470663 : Nat := 4983230072969 + 3 ^ 40 * 2470663 * 2
def baseEnd_2470663 : Nat := 281919478728749389633363

theorem tailTrace_2470663 : CollatzResearch.WordTrace tailWord_2470663 prefixEnd_2470663 281919478728749389633363 := by
  unfold tailWord_2470663
  simp only [CollatzResearch.WordTrace]
  refine ⟨90112482648217381491904643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60074988432144920994603095 90112482648217381491904643)
  ·
    refine ⟨135168723972326072237856965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90112482648217381491904643 135168723972326072237856965)
    ·
      refine ⟨25344135744811138544598181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135168723972326072237856965 25344135744811138544598181)
      ·
        refine ⟨4752025452152088477112159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25344135744811138544598181 4752025452152088477112159)
        ·
          refine ⟨7128038178228132715668239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752025452152088477112159 7128038178228132715668239)
          ·
            refine ⟨10692057267342199073502359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7128038178228132715668239 10692057267342199073502359)
            ·
              refine ⟨16038085901013298610253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10692057267342199073502359 16038085901013298610253539)
              ·
                refine ⟨24057128851519947915380309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16038085901013298610253539 24057128851519947915380309)
                ·
                  refine ⟨281919478728749389633363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24057128851519947915380309 281919478728749389633363)
                  ·
                    rfl

theorem cell22_2470663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_2470663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470663 prefixEnd_2470663 := by exact prefixLift 2470663
  have htrace : WordTrace (prefixWord ++ tailWord_2470663) baseStart_2470663 baseEnd_2470663 := by
    simpa [prefixWord, tailWord_2470663, baseEnd_2470663] using wordTrace_append hprefix tailTrace_2470663
  have hstable : (prefixWord ++ tailWord_2470663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470663).length < 2 ^ (prefixWord ++ tailWord_2470663).sum := by decide
  have hdescent : baseEnd_2470663 < baseStart_2470663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470693 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_2470693 : Nat := 118140960795 + 2470693 * 2 ^ 59
def prefixEnd_2470693 : Nat := 4983230072969 + 3 ^ 40 * 2470693 * 2
def baseEnd_2470693 : Nat := 845768705799338090649997

theorem tailTrace_2470693 : CollatzResearch.WordTrace tailWord_2470693 prefixEnd_2470693 845768705799338090649997 := by
  unfold tailWord_2470693
  simp only [CollatzResearch.WordTrace]
  refine ⟨90113576838108696615496733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60075717892072464410331155 90113576838108696615496733)
  ·
    refine ⟨33792591314290761230811275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90113576838108696615496733 33792591314290761230811275)
    ·
      refine ⟨50688886971436141846216913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33792591314290761230811275 50688886971436141846216913)
      ·
        refine ⟨38016665228577106384662685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50688886971436141846216913 38016665228577106384662685)
        ·
          refine ⟨14256249460716414894248507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38016665228577106384662685 14256249460716414894248507)
          ·
            refine ⟨21384374191074622341372761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14256249460716414894248507 21384374191074622341372761)
            ·
              refine ⟨16038280643305966756029571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21384374191074622341372761 16038280643305966756029571)
              ·
                refine ⟨24057420964958950134044357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16038280643305966756029571 24057420964958950134044357)
                ·
                  refine ⟨4510766430929803150133317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24057420964958950134044357 4510766430929803150133317)
                  ·
                    refine ⟨845768705799338090649997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4510766430929803150133317 845768705799338090649997)
                    ·
                      rfl

theorem cell22_2470693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_2470693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470693 prefixEnd_2470693 := by exact prefixLift 2470693
  have htrace : WordTrace (prefixWord ++ tailWord_2470693) baseStart_2470693 baseEnd_2470693 := by
    simpa [prefixWord, tailWord_2470693, baseEnd_2470693] using wordTrace_append hprefix tailTrace_2470693
  have hstable : (prefixWord ++ tailWord_2470693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470693).length < 2 ^ (prefixWord ++ tailWord_2470693).sum := by decide
  have hdescent : baseEnd_2470693 < baseStart_2470693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470712 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 2, 3]
def baseStart_2470712 : Nat := 118140960795 + 2470712 * 2 ^ 59
def prefixEnd_2470712 : Nat := 4983230072969 + 3 ^ 40 * 2470712 * 2
def baseEnd_2470712 : Nat := 845775209887628374424939

theorem tailTrace_2470712 : CollatzResearch.WordTrace tailWord_2470712 prefixEnd_2470712 845775209887628374424939 := by
  unfold tailWord_2470712
  simp only [CollatzResearch.WordTrace]
  refine ⟨45057134912519931430219195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60076179883359908573625593 45057134912519931430219195)
  ·
    refine ⟨67585702368779897145328793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45057134912519931430219195 67585702368779897145328793)
    ·
      refine ⟨50689276776584922858996595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67585702368779897145328793 50689276776584922858996595)
      ·
        refine ⟨76033915164877384288494893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50689276776584922858996595 76033915164877384288494893)
        ·
          refine ⟨28512718186829019108185585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76033915164877384288494893 28512718186829019108185585)
          ·
            refine ⟨21384538640121764331139189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28512718186829019108185585 21384538640121764331139189)
            ·
              refine ⟨2004800497511415406044299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21384538640121764331139189 2004800497511415406044299)
              ·
                refine ⟨3007200746267123109066449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004800497511415406044299 3007200746267123109066449)
                ·
                  refine ⟨2255400559700342331799837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007200746267123109066449 2255400559700342331799837)
                  ·
                    refine ⟨845775209887628374424939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255400559700342331799837 845775209887628374424939)
                    ·
                      rfl

theorem cell22_2470712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_2470712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470712 prefixEnd_2470712 := by exact prefixLift 2470712
  have htrace : WordTrace (prefixWord ++ tailWord_2470712) baseStart_2470712 baseEnd_2470712 := by
    simpa [prefixWord, tailWord_2470712, baseEnd_2470712] using wordTrace_append hprefix tailTrace_2470712
  have hstable : (prefixWord ++ tailWord_2470712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470712).length < 2 ^ (prefixWord ++ tailWord_2470712).sum := by decide
  have hdescent : baseEnd_2470712 < baseStart_2470712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470757 : List Nat := [1, 3, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_2470757 : Nat := 118140960795 + 2470757 * 2 ^ 59
def prefixEnd_2470757 : Nat := 4983230072969 + 3 ^ 40 * 2470757 * 2
def baseEnd_2470757 : Nat := 845790614307263257049801

theorem tailTrace_2470757 : CollatzResearch.WordTrace tailWord_2470757 prefixEnd_2470757 845790614307263257049801 := by
  unfold tailWord_2470757
  simp only [CollatzResearch.WordTrace]
  refine ⟨90115911109876835545826525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60077274073251223697217683 90115911109876835545826525)
  ·
    refine ⟨33793466666203813329684947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90115911109876835545826525 33793466666203813329684947)
    ·
      refine ⟨50690199999305719994527421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33793466666203813329684947 50690199999305719994527421)
      ·
        refine ⟨19008824999739644997947783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50690199999305719994527421 19008824999739644997947783)
        ·
          refine ⟨28513237499609467496921675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19008824999739644997947783 28513237499609467496921675)
          ·
            refine ⟨42769856249414201245382513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28513237499609467496921675 42769856249414201245382513)
            ·
              refine ⟨32077392187060650934036885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42769856249414201245382513 32077392187060650934036885)
              ·
                refine ⟨1503627758768468012532979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32077392187060650934036885 1503627758768468012532979)
                ·
                  refine ⟨2255441638152702018799469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503627758768468012532979 2255441638152702018799469)
                  ·
                    refine ⟨845790614307263257049801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255441638152702018799469 845790614307263257049801)
                    ·
                      rfl

theorem cell22_2470757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_2470757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470757 prefixEnd_2470757 := by exact prefixLift 2470757
  have htrace : WordTrace (prefixWord ++ tailWord_2470757) baseStart_2470757 baseEnd_2470757 := by
    simpa [prefixWord, tailWord_2470757, baseEnd_2470757] using wordTrace_append hprefix tailTrace_2470757
  have hstable : (prefixWord ++ tailWord_2470757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470757).length < 2 ^ (prefixWord ++ tailWord_2470757).sum := by decide
  have hdescent : baseEnd_2470757 < baseStart_2470757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470768 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_2470768 : Nat := 118140960795 + 2470768 * 2 ^ 59
def prefixEnd_2470768 : Nat := 4983230072969 + 3 ^ 40 * 2470768 * 2
def baseEnd_2470768 : Nat := 845794379832062895024767

theorem tailTrace_2470768 : CollatzResearch.WordTrace tailWord_2470768 prefixEnd_2470768 845794379832062895024767 := by
  unfold tailWord_2470768
  simp only [CollatzResearch.WordTrace]
  refine ⟨45058156156418492212238479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60077541541891322949651305 45058156156418492212238479)
  ·
    refine ⟨67587234234627738318357719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45058156156418492212238479 67587234234627738318357719)
    ·
      refine ⟨101380851351941607477536579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67587234234627738318357719 101380851351941607477536579)
      ·
        refine ⟨152071277027912411216304869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101380851351941607477536579 152071277027912411216304869)
        ·
          refine ⟨28513364442733577103057163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152071277027912411216304869 28513364442733577103057163)
          ·
            refine ⟨42770046664100365654585745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28513364442733577103057163 42770046664100365654585745)
            ·
              refine ⟨32077534998075274240939309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42770046664100365654585745 32077534998075274240939309)
              ·
                refine ⟨12029075624278227840352241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32077534998075274240939309 12029075624278227840352241)
                ·
                  refine ⟨9021806718208670880264181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12029075624278227840352241 9021806718208670880264181)
                  ·
                    refine ⟨845794379832062895024767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9021806718208670880264181 845794379832062895024767)
                    ·
                      rfl

theorem cell22_2470768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_2470768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470768 prefixEnd_2470768 := by exact prefixLift 2470768
  have htrace : WordTrace (prefixWord ++ tailWord_2470768) baseStart_2470768 baseEnd_2470768 := by
    simpa [prefixWord, tailWord_2470768, baseEnd_2470768] using wordTrace_append hprefix tailTrace_2470768
  have hstable : (prefixWord ++ tailWord_2470768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470768).length < 2 ^ (prefixWord ++ tailWord_2470768).sum := by decide
  have hdescent : baseEnd_2470768 < baseStart_2470768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470828 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2470828 : Nat := 118140960795 + 2470828 * 2 ^ 59
def prefixEnd_2470828 : Nat := 4983230072969 + 3 ^ 40 * 2470828 * 2
def baseEnd_2470828 : Nat := 845814919058242738524583

theorem tailTrace_2470828 : CollatzResearch.WordTrace tailWord_2470828 prefixEnd_2470828 845814919058242738524583 := by
  unfold tailWord_2470828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45059250346309807335830569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60079000461746409781107425 45059250346309807335830569)
  ·
    refine ⟨33794437759732355501872927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45059250346309807335830569 33794437759732355501872927)
    ·
      refine ⟨50691656639598533252809391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33794437759732355501872927 50691656639598533252809391)
      ·
        refine ⟨76037484959397799879214087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50691656639598533252809391 76037484959397799879214087)
        ·
          refine ⟨114056227439096699818821131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76037484959397799879214087 114056227439096699818821131)
          ·
            refine ⟨171084341158645049728231697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114056227439096699818821131 171084341158645049728231697)
            ·
              refine ⟨128313255868983787296173773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171084341158645049728231697 128313255868983787296173773)
              ·
                refine ⟨48117470950868920236065165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128313255868983787296173773 48117470950868920236065165)
                ·
                  refine ⟨18044051606575845088524437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48117470950868920236065165 18044051606575845088524437)
                  ·
                    refine ⟨845814919058242738524583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18044051606575845088524437 845814919058242738524583)
                    ·
                      rfl

theorem cell22_2470828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2470828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470828 prefixEnd_2470828 := by exact prefixLift 2470828
  have htrace : WordTrace (prefixWord ++ tailWord_2470828) baseStart_2470828 baseEnd_2470828 := by
    simpa [prefixWord, tailWord_2470828, baseEnd_2470828] using wordTrace_append hprefix tailTrace_2470828
  have hstable : (prefixWord ++ tailWord_2470828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470828).length < 2 ^ (prefixWord ++ tailWord_2470828).sum := by decide
  have hdescent : baseEnd_2470828 < baseStart_2470828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470894 : List Nat := [4, 1, 2, 1, 4, 2, 2, 6]
def baseStart_2470894 : Nat := 118140960795 + 2470894 * 2 ^ 59
def prefixEnd_2470894 : Nat := 4983230072969 + 3 ^ 40 * 2470894 * 2
def baseEnd_2470894 : Nat := 93981945800782285152709

theorem tailTrace_2470894 : CollatzResearch.WordTrace tailWord_2470894 prefixEnd_2470894 93981945800782285152709 := by
  unfold tailWord_2470894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265113488797563492945467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60080605273587005295709157 11265113488797563492945467)
  ·
    refine ⟨16897670233196345239418201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11265113488797563492945467 16897670233196345239418201)
    ·
      refine ⟨12673252674897258929563651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16897670233196345239418201 12673252674897258929563651)
      ·
        refine ⟨19009879012345888394345477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12673252674897258929563651 19009879012345888394345477)
        ·
          refine ⟨3564352314814854073939777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19009879012345888394345477 3564352314814854073939777)
          ·
            refine ⟨2673264236111140555454833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564352314814854073939777 2673264236111140555454833)
            ·
              refine ⟨2004948177083355416591125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673264236111140555454833 2004948177083355416591125)
              ·
                refine ⟨93981945800782285152709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2004948177083355416591125 93981945800782285152709)
                ·
                  rfl

theorem cell22_2470894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_2470894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470894 prefixEnd_2470894 := by exact prefixLift 2470894
  have htrace : WordTrace (prefixWord ++ tailWord_2470894) baseStart_2470894 baseEnd_2470894 := by
    simpa [prefixWord, tailWord_2470894, baseEnd_2470894] using wordTrace_append hprefix tailTrace_2470894
  have hstable : (prefixWord ++ tailWord_2470894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470894).length < 2 ^ (prefixWord ++ tailWord_2470894).sum := by decide
  have hdescent : baseEnd_2470894 < baseStart_2470894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2470967 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 4]
def baseStart_2470967 : Nat := 118140960795 + 2470967 * 2 ^ 59
def prefixEnd_2470967 : Nat := 4983230072969 + 3 ^ 40 * 2470967 * 2
def baseEnd_2470967 : Nat := 281954167199630903099719

theorem tailTrace_2470967 : CollatzResearch.WordTrace tailWord_2470967 prefixEnd_2470967 281954167199630903099719 := by
  unfold tailWord_2470967
  simp only [CollatzResearch.WordTrace]
  refine ⟨90123570439116041410971155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60082380292744027607314103 90123570439116041410971155)
  ·
    refine ⟨135185355658674062116456733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90123570439116041410971155 135185355658674062116456733)
    ·
      refine ⟨50694508372002773293671275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135185355658674062116456733 50694508372002773293671275)
      ·
        refine ⟨76041762558004159940506913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50694508372002773293671275 76041762558004159940506913)
        ·
          refine ⟨57031321918503119955380185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76041762558004159940506913 57031321918503119955380185)
          ·
            refine ⟨42773491438877339966535139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57031321918503119955380185 42773491438877339966535139)
            ·
              refine ⟨64160237158316009949802709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42773491438877339966535139 64160237158316009949802709)
              ·
                refine ⟨1503755558398031483198501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64160237158316009949802709 1503755558398031483198501)
                ·
                  refine ⟨281954167199630903099719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1503755558398031483198501 281954167199630903099719)
                  ·
                    rfl

theorem cell22_2470967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 4].length) (baseStart_2470967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2470967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2470967 prefixEnd_2470967 := by exact prefixLift 2470967
  have htrace : WordTrace (prefixWord ++ tailWord_2470967) baseStart_2470967 baseEnd_2470967 := by
    simpa [prefixWord, tailWord_2470967, baseEnd_2470967] using wordTrace_append hprefix tailTrace_2470967
  have hstable : (prefixWord ++ tailWord_2470967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2470967).length < 2 ^ (prefixWord ++ tailWord_2470967).sum := by decide
  have hdescent : baseEnd_2470967 < baseStart_2470967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2470967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471025 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2471025 : Nat := 118140960795 + 2471025 * 2 ^ 59
def prefixEnd_2471025 : Nat := 4983230072969 + 3 ^ 40 * 2471025 * 2
def baseEnd_2471025 : Nat := 845882356184199891348979

theorem tailTrace_2471025 : CollatzResearch.WordTrace tailWord_2471025 prefixEnd_2471025 845882356184199891348979 := by
  unfold tailWord_2471025
  simp only [CollatzResearch.WordTrace]
  refine ⟨90125685872905917316582529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60083790581937278211055019 90125685872905917316582529)
  ·
    refine ⟨67594264404679437987436897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90125685872905917316582529 67594264404679437987436897)
    ·
      refine ⟨50695698303509578490577673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67594264404679437987436897 50695698303509578490577673)
      ·
        refine ⟨38021773727632183867933255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50695698303509578490577673 38021773727632183867933255)
        ·
          refine ⟨57032660591448275801899883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38021773727632183867933255 57032660591448275801899883)
          ·
            refine ⟨85548990887172413702849825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57032660591448275801899883 85548990887172413702849825)
            ·
              refine ⟨64161743165379310277137369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85548990887172413702849825 64161743165379310277137369)
              ·
                refine ⟨48121307374034482707853027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64161743165379310277137369 48121307374034482707853027)
                ·
                  refine ⟨72181961061051724061779541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48121307374034482707853027 72181961061051724061779541)
                  ·
                    refine ⟨845882356184199891348979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72181961061051724061779541 845882356184199891348979)
                    ·
                      rfl

theorem cell22_2471025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2471025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471025 prefixEnd_2471025 := by exact prefixLift 2471025
  have htrace : WordTrace (prefixWord ++ tailWord_2471025) baseStart_2471025 baseEnd_2471025 := by
    simpa [prefixWord, tailWord_2471025, baseEnd_2471025] using wordTrace_append hprefix tailTrace_2471025
  have hstable : (prefixWord ++ tailWord_2471025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471025).length < 2 ^ (prefixWord ++ tailWord_2471025).sum := by decide
  have hdescent : baseEnd_2471025 < baseStart_2471025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471029 : List Nat := [1, 3, 4, 3, 1, 1, 9]
def baseStart_2471029 : Nat := 118140960795 + 2471029 * 2 ^ 59
def prefixEnd_2471029 : Nat := 4983230072969 + 3 ^ 40 * 2471029 * 2
def baseEnd_2471029 : Nat := 31329026869109082009221

theorem tailTrace_2471029 : CollatzResearch.WordTrace tailWord_2471029 prefixEnd_2471029 31329026869109082009221 := by
  unfold tailWord_2471029
  simp only [CollatzResearch.WordTrace]
  refine ⟨90125831764891425999728141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60083887843260950666485427 90125831764891425999728141)
  ·
    refine ⟨33797186911834284749898053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90125831764891425999728141 33797186911834284749898053)
    ·
      refine ⟨6336972545968928390605885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33797186911834284749898053 6336972545968928390605885)
      ·
        refine ⟨2376364704738348146477207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6336972545968928390605885 2376364704738348146477207)
        ·
          refine ⟨3564547057107522219715811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376364704738348146477207 3564547057107522219715811)
          ·
            refine ⟨5346820585661283329573717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3564547057107522219715811 5346820585661283329573717)
            ·
              refine ⟨31329026869109082009221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5346820585661283329573717 31329026869109082009221)
              ·
                rfl

theorem cell22_2471029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 9].length) (baseStart_2471029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471029 prefixEnd_2471029 := by exact prefixLift 2471029
  have htrace : WordTrace (prefixWord ++ tailWord_2471029) baseStart_2471029 baseEnd_2471029 := by
    simpa [prefixWord, tailWord_2471029, baseEnd_2471029] using wordTrace_append hprefix tailTrace_2471029
  have hstable : (prefixWord ++ tailWord_2471029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471029).length < 2 ^ (prefixWord ++ tailWord_2471029).sum := by decide
  have hdescent : baseEnd_2471029 < baseStart_2471029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471033 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_2471033 : Nat := 118140960795 + 2471033 * 2 ^ 59
def prefixEnd_2471033 : Nat := 4983230072969 + 3 ^ 40 * 2471033 * 2
def baseEnd_2471033 : Nat := 845885094747690537148955

theorem tailTrace_2471033 : CollatzResearch.WordTrace tailWord_2471033 prefixEnd_2471033 845885094747690537148955 := by
  unfold tailWord_2471033
  simp only [CollatzResearch.WordTrace]
  refine ⟨90125977656876934682873753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60083985104584623121915835 90125977656876934682873753)
  ·
    refine ⟨67594483242657701012155315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90125977656876934682873753 67594483242657701012155315)
    ·
      refine ⟨101391724863986551518232973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67594483242657701012155315 101391724863986551518232973)
      ·
        refine ⟨38021896823994956819337365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101391724863986551518232973 38021896823994956819337365)
        ·
          refine ⟨1782276413624763600906439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38021896823994956819337365 1782276413624763600906439)
          ·
            refine ⟨2673414620437145401359659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782276413624763600906439 2673414620437145401359659)
            ·
              refine ⟨4010121930655718102039489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673414620437145401359659 4010121930655718102039489)
              ·
                refine ⟨3007591447991788576529617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4010121930655718102039489 3007591447991788576529617)
                ·
                  refine ⟨2255693585993841432397213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007591447991788576529617 2255693585993841432397213)
                  ·
                    refine ⟨845885094747690537148955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255693585993841432397213 845885094747690537148955)
                    ·
                      rfl

theorem cell22_2471033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_2471033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471033 prefixEnd_2471033 := by exact prefixLift 2471033
  have htrace : WordTrace (prefixWord ++ tailWord_2471033) baseStart_2471033 baseEnd_2471033 := by
    simpa [prefixWord, tailWord_2471033, baseEnd_2471033] using wordTrace_append hprefix tailTrace_2471033
  have hstable : (prefixWord ++ tailWord_2471033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471033).length < 2 ^ (prefixWord ++ tailWord_2471033).sum := by decide
  have hdescent : baseEnd_2471033 < baseStart_2471033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471044 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2471044 : Nat := 118140960795 + 2471044 * 2 ^ 59
def prefixEnd_2471044 : Nat := 4983230072969 + 3 ^ 40 * 2471044 * 2
def baseEnd_2471044 : Nat := 845888860272490175123921

theorem tailTrace_2471044 : CollatzResearch.WordTrace tailWord_2471044 prefixEnd_2471044 845888860272490175123921 := by
  unfold tailWord_2471044
  simp only [CollatzResearch.WordTrace]
  refine ⟨45063189429918541780762093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60084252573224722374349457 45063189429918541780762093)
  ·
    refine ⟨16898696036219453167785785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45063189429918541780762093 16898696036219453167785785)
    ·
      refine ⟨12674022027164589875839339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16898696036219453167785785 12674022027164589875839339)
      ·
        refine ⟨19011033040746884813759009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12674022027164589875839339 19011033040746884813759009)
        ·
          refine ⟨14258274780560163610319257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19011033040746884813759009 14258274780560163610319257)
          ·
            refine ⟨10693706085420122707739443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14258274780560163610319257 10693706085420122707739443)
            ·
              refine ⟨16040559128130184061609165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10693706085420122707739443 16040559128130184061609165)
              ·
                refine ⟨6015209673048819023103437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16040559128130184061609165 6015209673048819023103437)
                ·
                  refine ⟨2255703627393307133663789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6015209673048819023103437 2255703627393307133663789)
                  ·
                    refine ⟨845888860272490175123921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255703627393307133663789 845888860272490175123921)
                    ·
                      rfl

theorem cell22_2471044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2471044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471044 prefixEnd_2471044 := by exact prefixLift 2471044
  have htrace : WordTrace (prefixWord ++ tailWord_2471044) baseStart_2471044 baseEnd_2471044 := by
    simpa [prefixWord, tailWord_2471044, baseEnd_2471044] using wordTrace_append hprefix tailTrace_2471044
  have hstable : (prefixWord ++ tailWord_2471044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471044).length < 2 ^ (prefixWord ++ tailWord_2471044).sum := by decide
  have hdescent : baseEnd_2471044 < baseStart_2471044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471055 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 7]
def baseStart_2471055 : Nat := 118140960795 + 2471055 * 2 ^ 59
def prefixEnd_2471055 : Nat := 4983230072969 + 3 ^ 40 * 2471055 * 2
def baseEnd_2471055 : Nat := 845892625797289813098887

theorem tailTrace_2471055 : CollatzResearch.WordTrace tailWord_2471055 prefixEnd_2471055 845892625797289813098887 := by
  unfold tailWord_2471055
  simp only [CollatzResearch.WordTrace]
  refine ⟨90126780062797232440174619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60084520041864821626783079 90126780062797232440174619)
  ·
    refine ⟨135190170094195848660261929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90126780062797232440174619 135190170094195848660261929)
    ·
      refine ⟨101392627570646886495196447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135190170094195848660261929 101392627570646886495196447)
      ·
        refine ⟨152088941355970329742794671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101392627570646886495196447 152088941355970329742794671)
        ·
          refine ⟨228133412033955494614192007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152088941355970329742794671 228133412033955494614192007)
          ·
            refine ⟨342200118050933241921288011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228133412033955494614192007 342200118050933241921288011)
            ·
              refine ⟨513300177076399862881932017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342200118050933241921288011 513300177076399862881932017)
              ·
                refine ⟨384975132807299897161449013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513300177076399862881932017 384975132807299897161449013)
                ·
                  refine ⟨36091418700684365358885845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384975132807299897161449013 36091418700684365358885845)
                  ·
                    refine ⟨845892625797289813098887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36091418700684365358885845 845892625797289813098887)
                    ·
                      rfl

theorem cell22_2471055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_2471055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471055 prefixEnd_2471055 := by exact prefixLift 2471055
  have htrace : WordTrace (prefixWord ++ tailWord_2471055) baseStart_2471055 baseEnd_2471055 := by
    simpa [prefixWord, tailWord_2471055, baseEnd_2471055] using wordTrace_append hprefix tailTrace_2471055
  have hstable : (prefixWord ++ tailWord_2471055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471055).length < 2 ^ (prefixWord ++ tailWord_2471055).sum := by decide
  have hdescent : baseEnd_2471055 < baseStart_2471055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471108 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 5]
def baseStart_2471108 : Nat := 118140960795 + 2471108 * 2 ^ 59
def prefixEnd_2471108 : Nat := 4983230072969 + 3 ^ 40 * 2471108 * 2
def baseEnd_2471108 : Nat := 281970256260138447174575

theorem tailTrace_2471108 : CollatzResearch.WordTrace tailWord_2471108 prefixEnd_2471108 281970256260138447174575 := by
  unfold tailWord_2471108
  simp only [CollatzResearch.WordTrace]
  refine ⟨45064356565802611245926989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60085808754403481661235985 45064356565802611245926989)
  ·
    refine ⟨16899133712175979217222621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45064356565802611245926989 16899133712175979217222621)
    ·
      refine ⟨6337175142065992206458483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16899133712175979217222621 6337175142065992206458483)
      ·
        refine ⟨9505762713098988309687725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6337175142065992206458483 9505762713098988309687725)
        ·
          refine ⟨3564661017412120616132897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9505762713098988309687725 3564661017412120616132897)
          ·
            refine ⟨2673495763059090462099673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3564661017412120616132897 2673495763059090462099673)
            ·
              refine ⟨2005121822294317846574755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673495763059090462099673 2005121822294317846574755)
              ·
                refine ⟨3007682733441476769862133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005121822294317846574755 3007682733441476769862133)
                ·
                  refine ⟨281970256260138447174575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3007682733441476769862133 281970256260138447174575)
                  ·
                    rfl

theorem cell22_2471108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_2471108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471108 prefixEnd_2471108 := by exact prefixLift 2471108
  have htrace : WordTrace (prefixWord ++ tailWord_2471108) baseStart_2471108 baseEnd_2471108 := by
    simpa [prefixWord, tailWord_2471108, baseEnd_2471108] using wordTrace_append hprefix tailTrace_2471108
  have hstable : (prefixWord ++ tailWord_2471108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471108).length < 2 ^ (prefixWord ++ tailWord_2471108).sum := by decide
  have hdescent : baseEnd_2471108 < baseStart_2471108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471177 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_2471177 : Nat := 118140960795 + 2471177 * 2 ^ 59
def prefixEnd_2471177 : Nat := 4983230072969 + 3 ^ 40 * 2471177 * 2
def baseEnd_2471177 : Nat := 845934388890522161548513

theorem tailTrace_2471177 : CollatzResearch.WordTrace tailWord_2471177 prefixEnd_2471177 845934388890522161548513 := by
  unfold tailWord_2471177
  simp only [CollatzResearch.WordTrace]
  refine ⟨90131229768355247276115785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60087486512236831517410523 90131229768355247276115785)
  ·
    refine ⟨67598422326266435457086839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90131229768355247276115785 67598422326266435457086839)
    ·
      refine ⟨101397633489399653185630259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67598422326266435457086839 101397633489399653185630259)
      ·
        refine ⟨152096450234099479778445389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101397633489399653185630259 152096450234099479778445389)
        ·
          refine ⟨57036168837787304916917021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152096450234099479778445389 57036168837787304916917021)
          ·
            refine ⟨21388563314170239343843883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57036168837787304916917021 21388563314170239343843883)
            ·
              refine ⟨32082844971255359015765825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21388563314170239343843883 32082844971255359015765825)
              ·
                refine ⟨24062133728441519261824369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32082844971255359015765825 24062133728441519261824369)
                ·
                  refine ⟨18046600296331139446368277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24062133728441519261824369 18046600296331139446368277)
                  ·
                    refine ⟨845934388890522161548513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18046600296331139446368277 845934388890522161548513)
                    ·
                      rfl

theorem cell22_2471177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_2471177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471177 prefixEnd_2471177 := by exact prefixLift 2471177
  have htrace : WordTrace (prefixWord ++ tailWord_2471177) baseStart_2471177 baseEnd_2471177 := by
    simpa [prefixWord, tailWord_2471177, baseEnd_2471177] using wordTrace_append hprefix tailTrace_2471177
  have hstable : (prefixWord ++ tailWord_2471177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471177).length < 2 ^ (prefixWord ++ tailWord_2471177).sum := by decide
  have hdescent : baseEnd_2471177 < baseStart_2471177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471179 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 5, 3]
def baseStart_2471179 : Nat := 118140960795 + 2471179 * 2 ^ 59
def prefixEnd_2471179 : Nat := 4983230072969 + 3 ^ 40 * 2471179 * 2
def baseEnd_2471179 : Nat := 845935073531394822998507

theorem tailTrace_2471179 : CollatzResearch.WordTrace tailWord_2471179 prefixEnd_2471179 845935073531394822998507 := by
  unfold tailWord_2471179
  simp only [CollatzResearch.WordTrace]
  refine ⟨90131302714348001617688591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60087535142898667745125727 90131302714348001617688591)
  ·
    refine ⟨135196954071522002426532887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90131302714348001617688591 135196954071522002426532887)
    ·
      refine ⟨202795431107283003639799331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135196954071522002426532887 202795431107283003639799331)
      ·
        refine ⟨304193146660924505459698997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202795431107283003639799331 304193146660924505459698997)
        ·
          refine ⟨28518107499461672386846781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304193146660924505459698997 28518107499461672386846781)
          ·
            refine ⟨10694290312298127145067543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28518107499461672386846781 10694290312298127145067543)
            ·
              refine ⟨16041435468447190717601315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10694290312298127145067543 16041435468447190717601315)
              ·
                refine ⟨24062153202670786076401973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16041435468447190717601315 24062153202670786076401973)
                ·
                  refine ⟨2255826862750386194662685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24062153202670786076401973 2255826862750386194662685)
                  ·
                    refine ⟨845935073531394822998507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255826862750386194662685 845935073531394822998507)
                    ·
                      rfl

theorem cell22_2471179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3].length) (baseStart_2471179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471179 prefixEnd_2471179 := by exact prefixLift 2471179
  have htrace : WordTrace (prefixWord ++ tailWord_2471179) baseStart_2471179 baseEnd_2471179 := by
    simpa [prefixWord, tailWord_2471179, baseEnd_2471179] using wordTrace_append hprefix tailTrace_2471179
  have hstable : (prefixWord ++ tailWord_2471179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471179).length < 2 ^ (prefixWord ++ tailWord_2471179).sum := by decide
  have hdescent : baseEnd_2471179 < baseStart_2471179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471213 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2471213 : Nat := 118140960795 + 2471213 * 2 ^ 59
def prefixEnd_2471213 : Nat := 4983230072969 + 3 ^ 40 * 2471213 * 2
def baseEnd_2471213 : Nat := 845946712426230067648403

theorem tailTrace_2471213 : CollatzResearch.WordTrace tailWord_2471213 prefixEnd_2471213 845946712426230067648403 := by
  unfold tailWord_2471213
  simp only [CollatzResearch.WordTrace]
  refine ⟨90132542796224825424426293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60088361864149883616284195 90132542796224825424426293)
  ·
    refine ⟨8449925887146077383539965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90132542796224825424426293 8449925887146077383539965)
    ·
      refine ⟨3168722207679779018827487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8449925887146077383539965 3168722207679779018827487)
      ·
        refine ⟨4753083311519668528241231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168722207679779018827487 4753083311519668528241231)
        ·
          refine ⟨7129624967279502792361847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753083311519668528241231 7129624967279502792361847)
          ·
            refine ⟨10694437450919254188542771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129624967279502792361847 10694437450919254188542771)
            ·
              refine ⟨16041656176378881282814157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10694437450919254188542771 16041656176378881282814157)
              ·
                refine ⟨6015621066142080481055309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16041656176378881282814157 6015621066142080481055309)
                ·
                  refine ⟨2255857899803280180395741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6015621066142080481055309 2255857899803280180395741)
                  ·
                    refine ⟨845946712426230067648403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255857899803280180395741 845946712426230067648403)
                    ·
                      rfl

theorem cell22_2471213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2471213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471213 prefixEnd_2471213 := by exact prefixLift 2471213
  have htrace : WordTrace (prefixWord ++ tailWord_2471213) baseStart_2471213 baseEnd_2471213 := by
    simpa [prefixWord, tailWord_2471213, baseEnd_2471213] using wordTrace_append hprefix tailTrace_2471213
  have hstable : (prefixWord ++ tailWord_2471213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471213).length < 2 ^ (prefixWord ++ tailWord_2471213).sum := by decide
  have hdescent : baseEnd_2471213 < baseStart_2471213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471226 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_2471226 : Nat := 118140960795 + 2471226 * 2 ^ 59
def prefixEnd_2471226 : Nat := 4983230072969 + 3 ^ 40 * 2471226 * 2
def baseEnd_2471226 : Nat := 281983720863967455691121

theorem tailTrace_2471226 : CollatzResearch.WordTrace tailWord_2471226 prefixEnd_2471226 281983720863967455691121 := by
  unfold tailWord_2471226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22533254236294432161162383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60088677963451819096433021 22533254236294432161162383)
  ·
    refine ⟨33799881354441648241743575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22533254236294432161162383 33799881354441648241743575)
    ·
      refine ⟨50699822031662472362615363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33799881354441648241743575 50699822031662472362615363)
      ·
        refine ⟨76049733047493708543923045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50699822031662472362615363 76049733047493708543923045)
        ·
          refine ⟨14259324946405070351985571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76049733047493708543923045 14259324946405070351985571)
          ·
            refine ⟨21388987419607605527978357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14259324946405070351985571 21388987419607605527978357)
            ·
              refine ⟨2005217570588213018247971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21388987419607605527978357 2005217570588213018247971)
              ·
                refine ⟨3007826355882319527371957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005217570588213018247971 3007826355882319527371957)
                ·
                  refine ⟨281983720863967455691121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3007826355882319527371957 281983720863967455691121)
                  ·
                    rfl

theorem cell22_2471226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_2471226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471226 prefixEnd_2471226 := by exact prefixLift 2471226
  have htrace : WordTrace (prefixWord ++ tailWord_2471226) baseStart_2471226 baseEnd_2471226 := by
    simpa [prefixWord, tailWord_2471226, baseEnd_2471226] using wordTrace_append hprefix tailTrace_2471226
  have hstable : (prefixWord ++ tailWord_2471226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471226).length < 2 ^ (prefixWord ++ tailWord_2471226).sum := by decide
  have hdescent : baseEnd_2471226 < baseStart_2471226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471299 : List Nat := [1, 1, 1, 3, 5, 1, 2, 8]
def baseStart_2471299 : Nat := 118140960795 + 2471299 * 2 ^ 59
def prefixEnd_2471299 : Nat := 4983230072969 + 3 ^ 40 * 2471299 * 2
def baseEnd_2471299 : Nat := 93997350220417167777571

theorem tailTrace_2471299 : CollatzResearch.WordTrace tailWord_2471299 prefixEnd_2471299 93997350220417167777571 := by
  unfold tailWord_2471299
  simp only [CollatzResearch.WordTrace]
  refine ⟨90135679473913262112056951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60090452982608841408037967 90135679473913262112056951)
  ·
    refine ⟨135203519210869893168085427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90135679473913262112056951 135203519210869893168085427)
    ·
      refine ⟨202805278816304839752128141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135203519210869893168085427 202805278816304839752128141)
      ·
        refine ⟨76051979556114314907048053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202805278816304839752128141 76051979556114314907048053)
        ·
          refine ⟨7129873083385717022535755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76051979556114314907048053 7129873083385717022535755)
          ·
            refine ⟨10694809625078575533803633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129873083385717022535755 10694809625078575533803633)
            ·
              refine ⟨8021107218808931650352725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10694809625078575533803633 8021107218808931650352725)
              ·
                refine ⟨93997350220417167777571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8021107218808931650352725 93997350220417167777571)
                ·
                  rfl

theorem cell22_2471299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 8].length) (baseStart_2471299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471299 prefixEnd_2471299 := by exact prefixLift 2471299
  have htrace : WordTrace (prefixWord ++ tailWord_2471299) baseStart_2471299 baseEnd_2471299 := by
    simpa [prefixWord, tailWord_2471299, baseEnd_2471299] using wordTrace_append hprefix tailTrace_2471299
  have hstable : (prefixWord ++ tailWord_2471299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471299).length < 2 ^ (prefixWord ++ tailWord_2471299).sum := by decide
  have hdescent : baseEnd_2471299 < baseStart_2471299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471320 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_2471320 : Nat := 118140960795 + 2471320 * 2 ^ 59
def prefixEnd_2471320 : Nat := 4983230072969 + 3 ^ 40 * 2471320 * 2
def baseEnd_2471320 : Nat := 845983340712917455223075

theorem tailTrace_2471320 : CollatzResearch.WordTrace tailWord_2471320 prefixEnd_2471320 845983340712917455223075 := by
  unfold tailWord_2471320
  simp only [CollatzResearch.WordTrace]
  refine ⟨45068222703418591349285707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60090963604558121799047609 45068222703418591349285707)
  ·
    refine ⟨67602334055127887023928561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45068222703418591349285707 67602334055127887023928561)
    ·
      refine ⟨50701750541345915267946421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67602334055127887023928561 50701750541345915267946421)
      ·
        refine ⟨4753289113251179556369977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50701750541345915267946421 4753289113251179556369977)
        ·
          refine ⟨3564966834938384667277483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4753289113251179556369977 3564966834938384667277483)
          ·
            refine ⟨5347450252407577000916225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3564966834938384667277483 5347450252407577000916225)
            ·
              refine ⟨4010587689305682750687169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347450252407577000916225 4010587689305682750687169)
              ·
                refine ⟨3007940766979262063015377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4010587689305682750687169 3007940766979262063015377)
                ·
                  refine ⟨2255955575234446547261533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3007940766979262063015377 2255955575234446547261533)
                  ·
                    refine ⟨845983340712917455223075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255955575234446547261533 845983340712917455223075)
                    ·
                      rfl

theorem cell22_2471320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_2471320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471320 prefixEnd_2471320 := by exact prefixLift 2471320
  have htrace : WordTrace (prefixWord ++ tailWord_2471320) baseStart_2471320 baseEnd_2471320 := by
    simpa [prefixWord, tailWord_2471320, baseEnd_2471320] using wordTrace_append hprefix tailTrace_2471320
  have hstable : (prefixWord ++ tailWord_2471320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471320).length < 2 ^ (prefixWord ++ tailWord_2471320).sum := by decide
  have hdescent : baseEnd_2471320 < baseStart_2471320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471331 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 3, 3]
def baseStart_2471331 : Nat := 118140960795 + 2471331 * 2 ^ 59
def prefixEnd_2471331 : Nat := 4983230072969 + 3 ^ 40 * 2471331 * 2
def baseEnd_2471331 : Nat := 845987106237717093198041

theorem tailTrace_2471331 : CollatzResearch.WordTrace tailWord_2471331 prefixEnd_2471331 845987106237717093198041 := by
  unfold tailWord_2471331
  simp only [CollatzResearch.WordTrace]
  refine ⟨90136846609797331577221847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60091231073198221051481231 90136846609797331577221847)
  ·
    refine ⟨135205269914695997365832771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90136846609797331577221847 135205269914695997365832771)
    ·
      refine ⟨202807904872043996048749157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135205269914695997365832771 202807904872043996048749157)
      ·
        refine ⟨38026482163508249259140467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 202807904872043996048749157 38026482163508249259140467)
        ·
          refine ⟨57039723245262373888710701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38026482163508249259140467 57039723245262373888710701)
          ·
            refine ⟨21389896216973390208266513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57039723245262373888710701 21389896216973390208266513)
            ·
              refine ⟨16042422162730042656199885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21389896216973390208266513 16042422162730042656199885)
              ·
                refine ⟨6015908311023765996074957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16042422162730042656199885 6015908311023765996074957)
                ·
                  refine ⟨2255965616633912248528109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6015908311023765996074957 2255965616633912248528109)
                  ·
                    refine ⟨845987106237717093198041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2255965616633912248528109 845987106237717093198041)
                    ·
                      rfl

theorem cell22_2471331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3].length) (baseStart_2471331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471331 prefixEnd_2471331 := by exact prefixLift 2471331
  have htrace : WordTrace (prefixWord ++ tailWord_2471331) baseStart_2471331 baseEnd_2471331 := by
    simpa [prefixWord, tailWord_2471331, baseEnd_2471331] using wordTrace_append hprefix tailTrace_2471331
  have hstable : (prefixWord ++ tailWord_2471331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471331).length < 2 ^ (prefixWord ++ tailWord_2471331).sum := by decide
  have hdescent : baseEnd_2471331 < baseStart_2471331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471382 : List Nat := [5, 2, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2471382 : Nat := 118140960795 + 2471382 * 2 ^ 59
def prefixEnd_2471382 : Nat := 4983230072969 + 3 ^ 40 * 2471382 * 2
def baseEnd_2471382 : Nat := 846004564579969960172885

theorem tailTrace_2471382 : CollatzResearch.WordTrace tailWord_2471382 prefixEnd_2471382 846004564579969960172885 := by
  unfold tailWord_2471382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633669170788285455458025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60092471155075044858218933 5633669170788285455458025)
  ·
    refine ⟨4225251878091214091593519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5633669170788285455458025 4225251878091214091593519)
    ·
      refine ⟨6337877817136821137390279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4225251878091214091593519 6337877817136821137390279)
      ·
        refine ⟨9506816725705231706085419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6337877817136821137390279 9506816725705231706085419)
        ·
          refine ⟨14260225088557847559128129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9506816725705231706085419 14260225088557847559128129)
          ·
            refine ⟨10695168816418385669346097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14260225088557847559128129 10695168816418385669346097)
            ·
              refine ⟨8021376612313789252009573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10695168816418385669346097 8021376612313789252009573)
              ·
                refine ⟨1504008114808835484751795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8021376612313789252009573 1504008114808835484751795)
                ·
                  refine ⟨2256012172213253227127693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504008114808835484751795 2256012172213253227127693)
                  ·
                    refine ⟨846004564579969960172885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256012172213253227127693 846004564579969960172885)
                    ·
                      rfl

theorem cell22_2471382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2471382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471382 prefixEnd_2471382 := by exact prefixLift 2471382
  have htrace : WordTrace (prefixWord ++ tailWord_2471382) baseStart_2471382 baseEnd_2471382 := by
    simpa [prefixWord, tailWord_2471382, baseEnd_2471382] using wordTrace_append hprefix tailTrace_2471382
  have hstable : (prefixWord ++ tailWord_2471382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471382).length < 2 ^ (prefixWord ++ tailWord_2471382).sum := by decide
  have hdescent : baseEnd_2471382 < baseStart_2471382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471406 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_2471406 : Nat := 118140960795 + 2471406 * 2 ^ 59
def prefixEnd_2471406 : Nat := 4983230072969 + 3 ^ 40 * 2471406 * 2
def baseEnd_2471406 : Nat := 282004260090147299190937

theorem tailTrace_2471406 : CollatzResearch.WordTrace tailWord_2471406 prefixEnd_2471406 282004260090147299190937 := by
  unfold tailWord_2471406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267447760565702423275259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60093054723017079590801381 11267447760565702423275259)
  ·
    refine ⟨16901171640848553634912889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11267447760565702423275259 16901171640848553634912889)
    ·
      refine ⟨12675878730636415226184667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16901171640848553634912889 12675878730636415226184667)
      ·
        refine ⟨19013818095954622839277001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12675878730636415226184667 19013818095954622839277001)
        ·
          refine ⟨14260363571965967129457751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19013818095954622839277001 14260363571965967129457751)
          ·
            refine ⟨21390545357948950694186627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14260363571965967129457751 21390545357948950694186627)
            ·
              refine ⟨32085818036923426041279941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21390545357948950694186627 32085818036923426041279941)
              ·
                refine ⟨6016090881923142382739989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32085818036923426041279941 6016090881923142382739989)
                ·
                  refine ⟨282004260090147299190937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6016090881923142382739989 282004260090147299190937)
                  ·
                    rfl

theorem cell22_2471406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_2471406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471406 prefixEnd_2471406 := by exact prefixLift 2471406
  have htrace : WordTrace (prefixWord ++ tailWord_2471406) baseStart_2471406 baseEnd_2471406 := by
    simpa [prefixWord, tailWord_2471406, baseEnd_2471406] using wordTrace_append hprefix tailTrace_2471406
  have hstable : (prefixWord ++ tailWord_2471406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471406).length < 2 ^ (prefixWord ++ tailWord_2471406).sum := by decide
  have hdescent : baseEnd_2471406 < baseStart_2471406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471408 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_2471408 : Nat := 118140960795 + 2471408 * 2 ^ 59
def prefixEnd_2471408 : Nat := 4983230072969 + 3 ^ 40 * 2471408 * 2
def baseEnd_2471408 : Nat := 846013464911314559022805

theorem tailTrace_2471408 : CollatzResearch.WordTrace tailWord_2471408 prefixEnd_2471408 846013464911314559022805 := by
  unfold tailWord_2471408
  simp only [CollatzResearch.WordTrace]
  refine ⟨45069827515259186863887439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60093103353678915818516585 45069827515259186863887439)
  ·
    refine ⟨67604741272888780295831159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45069827515259186863887439 67604741272888780295831159)
    ·
      refine ⟨101407111909333170443746739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67604741272888780295831159 101407111909333170443746739)
      ·
        refine ⟨152110667863999755665620109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101407111909333170443746739 152110667863999755665620109)
        ·
          refine ⟨57041500448999908374607541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152110667863999755665620109 57041500448999908374607541)
          ·
            refine ⟨5347640667093741410119457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57041500448999908374607541 5347640667093741410119457)
            ·
              refine ⟨4010730500320306057589593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347640667093741410119457 4010730500320306057589593)
              ·
                refine ⟨3008047875240229543192195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4010730500320306057589593 3008047875240229543192195)
                ·
                  refine ⟨4512071812860344314788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008047875240229543192195 4512071812860344314788293)
                  ·
                    refine ⟨846013464911314559022805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512071812860344314788293 846013464911314559022805)
                    ·
                      rfl

theorem cell22_2471408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_2471408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471408 prefixEnd_2471408 := by exact prefixLift 2471408
  have htrace : WordTrace (prefixWord ++ tailWord_2471408) baseStart_2471408 baseEnd_2471408 := by
    simpa [prefixWord, tailWord_2471408, baseEnd_2471408] using wordTrace_append hprefix tailTrace_2471408
  have hstable : (prefixWord ++ tailWord_2471408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471408).length < 2 ^ (prefixWord ++ tailWord_2471408).sum := by decide
  have hdescent : baseEnd_2471408 < baseStart_2471408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471455 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 2, 3]
def baseStart_2471455 : Nat := 118140960795 + 2471455 * 2 ^ 59
def prefixEnd_2471455 : Nat := 4983230072969 + 3 ^ 40 * 2471455 * 2
def baseEnd_2471455 : Nat := 846029553971822103097661

theorem tailTrace_2471455 : CollatzResearch.WordTrace tailWord_2471455 prefixEnd_2471455 846029553971822103097661 := by
  unfold tailWord_2471455
  simp only [CollatzResearch.WordTrace]
  refine ⟨90141369261348100754735819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60094246174232067169823879 90141369261348100754735819)
  ·
    refine ⟨135212053892022151132103729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90141369261348100754735819 135212053892022151132103729)
    ·
      refine ⟨101409040419016613349077797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135212053892022151132103729 101409040419016613349077797)
      ·
        refine ⟨19014195078565615002952087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101409040419016613349077797 19014195078565615002952087)
        ·
          refine ⟨28521292617848422504428131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19014195078565615002952087 28521292617848422504428131)
          ·
            refine ⟨42781938926772633756642197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28521292617848422504428131 42781938926772633756642197)
            ·
              refine ⟨2005403387192467207342603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42781938926772633756642197 2005403387192467207342603)
              ·
                refine ⟨3008105080788700811013905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005403387192467207342603 3008105080788700811013905)
                ·
                  refine ⟨2256078810591525608260429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3008105080788700811013905 2256078810591525608260429)
                  ·
                    refine ⟨846029553971822103097661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256078810591525608260429 846029553971822103097661)
                    ·
                      rfl

theorem cell22_2471455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_2471455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471455 prefixEnd_2471455 := by exact prefixLift 2471455
  have htrace : WordTrace (prefixWord ++ tailWord_2471455) baseStart_2471455 baseEnd_2471455 := by
    simpa [prefixWord, tailWord_2471455, baseEnd_2471455] using wordTrace_append hprefix tailTrace_2471455
  have hstable : (prefixWord ++ tailWord_2471455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471455).length < 2 ^ (prefixWord ++ tailWord_2471455).sum := by decide
  have hdescent : baseEnd_2471455 < baseStart_2471455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471470 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2471470 : Nat := 118140960795 + 2471470 * 2 ^ 59
def prefixEnd_2471470 : Nat := 4983230072969 + 3 ^ 40 * 2471470 * 2
def baseEnd_2471470 : Nat := 846034688778367063972615

theorem tailTrace_2471470 : CollatzResearch.WordTrace tailWord_2471470 prefixEnd_2471470 846034688778367063972615 := by
  unfold tailWord_2471470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267739544536719789566483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60094610904195838877687909 11267739544536719789566483)
  ·
    refine ⟨16901609316805079684349725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11267739544536719789566483 16901609316805079684349725)
    ·
      refine ⟨6338103493801904881631147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16901609316805079684349725 6338103493801904881631147)
      ·
        refine ⟨9507155240702857322446721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6338103493801904881631147 9507155240702857322446721)
        ·
          refine ⟨7130366430527142991835041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9507155240702857322446721 7130366430527142991835041)
          ·
            refine ⟨5347774822895357243876281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130366430527142991835041 5347774822895357243876281)
            ·
              refine ⟨4010831117171517932907211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347774822895357243876281 4010831117171517932907211)
              ·
                refine ⟨6016246675757276899360817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010831117171517932907211 6016246675757276899360817)
                ·
                  refine ⟨4512185006817957674520613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6016246675757276899360817 4512185006817957674520613)
                  ·
                    refine ⟨846034688778367063972615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512185006817957674520613 846034688778367063972615)
                    ·
                      rfl

theorem cell22_2471470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2471470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471470 prefixEnd_2471470 := by exact prefixLift 2471470
  have htrace : WordTrace (prefixWord ++ tailWord_2471470) baseStart_2471470 baseEnd_2471470 := by
    simpa [prefixWord, tailWord_2471470, baseEnd_2471470] using wordTrace_append hprefix tailTrace_2471470
  have hstable : (prefixWord ++ tailWord_2471470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471470).length < 2 ^ (prefixWord ++ tailWord_2471470).sum := by decide
  have hdescent : baseEnd_2471470 < baseStart_2471470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471511 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2471511 : Nat := 118140960795 + 2471511 * 2 ^ 59
def prefixEnd_2471511 : Nat := 4983230072969 + 3 ^ 40 * 2471511 * 2
def baseEnd_2471511 : Nat := 846048723916256623697489

theorem tailTrace_2471511 : CollatzResearch.WordTrace tailWord_2471511 prefixEnd_2471511 846048723916256623697489 := by
  unfold tailWord_2471511
  simp only [CollatzResearch.WordTrace]
  refine ⟨90143411749145222318774387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60095607832763481545849591 90143411749145222318774387)
  ·
    refine ⟨135215117623717833478161581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90143411749145222318774387 135215117623717833478161581)
    ·
      refine ⟨50705669108894187554310593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135215117623717833478161581 50705669108894187554310593)
      ·
        refine ⟨38029251831670640665732945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50705669108894187554310593 38029251831670640665732945)
        ·
          refine ⟨28521938873752980499299709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38029251831670640665732945 28521938873752980499299709)
          ·
            refine ⟨10695727077657367687237391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28521938873752980499299709 10695727077657367687237391)
            ·
              refine ⟨16043590616486051530856087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10695727077657367687237391 16043590616486051530856087)
              ·
                refine ⟨24065385924729077296284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16043590616486051530856087 24065385924729077296284131)
                ·
                  refine ⟨36098078887093615944426197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24065385924729077296284131 36098078887093615944426197)
                  ·
                    refine ⟨846048723916256623697489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36098078887093615944426197 846048723916256623697489)
                    ·
                      rfl

theorem cell22_2471511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2471511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471511 prefixEnd_2471511 := by exact prefixLift 2471511
  have htrace : WordTrace (prefixWord ++ tailWord_2471511) baseStart_2471511 baseEnd_2471511 := by
    simpa [prefixWord, tailWord_2471511, baseEnd_2471511] using wordTrace_append hprefix tailTrace_2471511
  have hstable : (prefixWord ++ tailWord_2471511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471511).length < 2 ^ (prefixWord ++ tailWord_2471511).sum := by decide
  have hdescent : baseEnd_2471511 < baseStart_2471511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471534 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2471534 : Nat := 118140960795 + 2471534 * 2 ^ 59
def prefixEnd_2471534 : Nat := 4983230072969 + 3 ^ 40 * 2471534 * 2
def baseEnd_2471534 : Nat := 846056597286292230372419

theorem tailTrace_2471534 : CollatzResearch.WordTrace tailWord_2471534 prefixEnd_2471534 846056597286292230372419 := by
  unfold tailWord_2471534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11268031328507737155857707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60096167085374598164574437 11268031328507737155857707)
  ·
    refine ⟨16902046992761605733786561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11268031328507737155857707 16902046992761605733786561)
    ·
      refine ⟨12676535244571204300339921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16902046992761605733786561 12676535244571204300339921)
      ·
        refine ⟨9507401433428403225254941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12676535244571204300339921 9507401433428403225254941)
        ·
          refine ⟨3565275537535651209470603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9507401433428403225254941 3565275537535651209470603)
          ·
            refine ⟨5347913306303476814205905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565275537535651209470603 5347913306303476814205905)
            ·
              refine ⟨4010934979727607610654429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5347913306303476814205905 4010934979727607610654429)
              ·
                refine ⟨1504100617397852853995411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4010934979727607610654429 1504100617397852853995411)
                ·
                  refine ⟨2256150926096779280993117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504100617397852853995411 2256150926096779280993117)
                  ·
                    refine ⟨846056597286292230372419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256150926096779280993117 846056597286292230372419)
                    ·
                      rfl

theorem cell22_2471534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2471534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471534 prefixEnd_2471534 := by exact prefixLift 2471534
  have htrace : WordTrace (prefixWord ++ tailWord_2471534) baseStart_2471534 baseEnd_2471534 := by
    simpa [prefixWord, tailWord_2471534, baseEnd_2471534] using wordTrace_append hprefix tailTrace_2471534
  have hstable : (prefixWord ++ tailWord_2471534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471534).length < 2 ^ (prefixWord ++ tailWord_2471534).sum := by decide
  have hdescent : baseEnd_2471534 < baseStart_2471534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471588 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2471588 : Nat := 118140960795 + 2471588 * 2 ^ 59
def prefixEnd_2471588 : Nat := 4983230072969 + 3 ^ 40 * 2471588 * 2
def baseEnd_2471588 : Nat := 846075082589854089522253

theorem tailTrace_2471588 : CollatzResearch.WordTrace tailWord_2471588 prefixEnd_2471588 846075082589854089522253 := by
  unfold tailWord_2471588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45073110084933132234663709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60097480113244176312884945 45073110084933132234663709)
  ·
    refine ⟨16902416281849924587998891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45073110084933132234663709 16902416281849924587998891)
    ·
      refine ⟨25353624422774886881998337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16902416281849924587998891 25353624422774886881998337)
      ·
        refine ⟨19015218317081165161498753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25353624422774886881998337 19015218317081165161498753)
        ·
          refine ⟨14261413737810873871124065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19015218317081165161498753 14261413737810873871124065)
          ·
            refine ⟨10696060303358155403343049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14261413737810873871124065 10696060303358155403343049)
            ·
              refine ⟨8022045227518616552507287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696060303358155403343049 8022045227518616552507287)
              ·
                refine ⟨12033067841277924828760931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022045227518616552507287 12033067841277924828760931)
                ·
                  refine ⟨18049601761916887243141397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12033067841277924828760931 18049601761916887243141397)
                  ·
                    refine ⟨846075082589854089522253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18049601761916887243141397 846075082589854089522253)
                    ·
                      rfl

theorem cell22_2471588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2471588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471588 prefixEnd_2471588 := by exact prefixLift 2471588
  have htrace : WordTrace (prefixWord ++ tailWord_2471588) baseStart_2471588 baseEnd_2471588 := by
    simpa [prefixWord, tailWord_2471588, baseEnd_2471588] using wordTrace_append hprefix tailTrace_2471588
  have hstable : (prefixWord ++ tailWord_2471588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471588).length < 2 ^ (prefixWord ++ tailWord_2471588).sum := by decide
  have hdescent : baseEnd_2471588 < baseStart_2471588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471652 : List Nat := [2, 3, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2471652 : Nat := 118140960795 + 2471652 * 2 ^ 59
def prefixEnd_2471652 : Nat := 4983230072969 + 3 ^ 40 * 2471652 * 2
def baseEnd_2471652 : Nat := 846096991097779255922057

theorem tailTrace_2471652 : CollatzResearch.WordTrace tailWord_2471652 prefixEnd_2471652 846096991097779255922057 := by
  unfold tailWord_2471652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45074277220817201699828605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60099036294422935599771473 45074277220817201699828605)
  ·
    refine ⟨16902853957806450637435727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45074277220817201699828605 16902853957806450637435727)
    ·
      refine ⟨25354280936709675956153591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16902853957806450637435727 25354280936709675956153591)
      ·
        refine ⟨38031421405064513934230387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25354280936709675956153591 38031421405064513934230387)
        ·
          refine ⟨57047132107596770901345581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38031421405064513934230387 57047132107596770901345581)
          ·
            refine ⟨21392674540348789088004593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57047132107596770901345581 21392674540348789088004593)
            ·
              refine ⟨16044505905261591816003445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21392674540348789088004593 16044505905261591816003445)
              ·
                refine ⟨1504172428618274232750323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16044505905261591816003445 1504172428618274232750323)
                ·
                  refine ⟨2256258642927411349125485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504172428618274232750323 2256258642927411349125485)
                  ·
                    refine ⟨846096991097779255922057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256258642927411349125485 846096991097779255922057)
                    ·
                      rfl

theorem cell22_2471652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2471652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471652 prefixEnd_2471652 := by exact prefixLift 2471652
  have htrace : WordTrace (prefixWord ++ tailWord_2471652) baseStart_2471652 baseEnd_2471652 := by
    simpa [prefixWord, tailWord_2471652, baseEnd_2471652] using wordTrace_append hprefix tailTrace_2471652
  have hstable : (prefixWord ++ tailWord_2471652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471652).length < 2 ^ (prefixWord ++ tailWord_2471652).sum := by decide
  have hdescent : baseEnd_2471652 < baseStart_2471652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471663 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 2, 5]
def baseStart_2471663 : Nat := 118140960795 + 2471663 * 2 ^ 59
def prefixEnd_2471663 : Nat := 4983230072969 + 3 ^ 40 * 2471663 * 2
def baseEnd_2471663 : Nat := 846100756622578893897023

theorem tailTrace_2471663 : CollatzResearch.WordTrace tailWord_2471663 prefixEnd_2471663 846100756622578893897023 := by
  unfold tailWord_2471663
  simp only [CollatzResearch.WordTrace]
  refine ⟨90148955644594552278307643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60099303763063034852205095 90148955644594552278307643)
  ·
    refine ⟨135223433466891828417461465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90148955644594552278307643 135223433466891828417461465)
    ·
      refine ⟨101417575100168871313096099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135223433466891828417461465 101417575100168871313096099)
      ·
        refine ⟨152126362650253306969644149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101417575100168871313096099 152126362650253306969644149)
        ·
          refine ⟨14261846498461247528404139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152126362650253306969644149 14261846498461247528404139)
          ·
            refine ⟨21392769747691871292606209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14261846498461247528404139 21392769747691871292606209)
            ·
              refine ⟨16044577310768903469454657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21392769747691871292606209 16044577310768903469454657)
              ·
                refine ⟨12033432983076677602090993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16044577310768903469454657 12033432983076677602090993)
                ·
                  refine ⟨9025074737307508201568245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12033432983076677602090993 9025074737307508201568245)
                  ·
                    refine ⟨846100756622578893897023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9025074737307508201568245 846100756622578893897023)
                    ·
                      rfl

theorem cell22_2471663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_2471663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471663 prefixEnd_2471663 := by exact prefixLift 2471663
  have htrace : WordTrace (prefixWord ++ tailWord_2471663) baseStart_2471663 baseEnd_2471663 := by
    simpa [prefixWord, tailWord_2471663, baseEnd_2471663] using wordTrace_append hprefix tailTrace_2471663
  have hstable : (prefixWord ++ tailWord_2471663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471663).length < 2 ^ (prefixWord ++ tailWord_2471663).sum := by decide
  have hdescent : baseEnd_2471663 < baseStart_2471663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471665 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 5]
def baseStart_2471665 : Nat := 118140960795 + 2471665 * 2 ^ 59
def prefixEnd_2471665 : Nat := 4983230072969 + 3 ^ 40 * 2471665 * 2
def baseEnd_2471665 : Nat := 282033813754483851782339

theorem tailTrace_2471665 : CollatzResearch.WordTrace tailWord_2471665 prefixEnd_2471665 282033813754483851782339 := by
  unfold tailWord_2471665
  simp only [CollatzResearch.WordTrace]
  refine ⟨90149028590587306619880449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60099352393724871079920299 90149028590587306619880449)
  ·
    refine ⟨67611771442940479964910337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90149028590587306619880449 67611771442940479964910337)
    ·
      refine ⟨50708828582205359973682753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67611771442940479964910337 50708828582205359973682753)
      ·
        refine ⟨38031621436654019980262065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50708828582205359973682753 38031621436654019980262065)
        ·
          refine ⟨28523716077490514985196549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38031621436654019980262065 28523716077490514985196549)
          ·
            refine ⟨5348196764529471559724353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28523716077490514985196549 5348196764529471559724353)
            ·
              refine ⟨4011147573397103669793265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5348196764529471559724353 4011147573397103669793265)
              ·
                refine ⟨3008360680047827752344949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4011147573397103669793265 3008360680047827752344949)
                ·
                  refine ⟨282033813754483851782339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3008360680047827752344949 282033813754483851782339)
                  ·
                    rfl

theorem cell22_2471665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_2471665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471665 prefixEnd_2471665 := by exact prefixLift 2471665
  have htrace : WordTrace (prefixWord ++ tailWord_2471665) baseStart_2471665 baseEnd_2471665 := by
    simpa [prefixWord, tailWord_2471665, baseEnd_2471665] using wordTrace_append hprefix tailTrace_2471665
  have hstable : (prefixWord ++ tailWord_2471665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471665).length < 2 ^ (prefixWord ++ tailWord_2471665).sum := by decide
  have hdescent : baseEnd_2471665 < baseStart_2471665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471742 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2471742 : Nat := 118140960795 + 2471742 * 2 ^ 59
def prefixEnd_2471742 : Nat := 4983230072969 + 3 ^ 40 * 2471742 * 2
def baseEnd_2471742 : Nat := 846127799937049021171781

theorem tailTrace_2471742 : CollatzResearch.WordTrace tailWord_2471742 prefixEnd_2471742 846127799937049021171781 := by
  unfold tailWord_2471742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11268979626413543596304185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60101224674205565846955653 11268979626413543596304185)
  ·
    refine ⟨8451734719810157697228139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11268979626413543596304185 8451734719810157697228139)
    ·
      refine ⟨12677602079715236545842209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8451734719810157697228139 12677602079715236545842209)
      ·
        refine ⟨9508201559786427409381657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12677602079715236545842209 9508201559786427409381657)
        ·
          refine ⟨7131151169839820557036243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9508201559786427409381657 7131151169839820557036243)
          ·
            refine ⟨10696726754759730835554365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131151169839820557036243 10696726754759730835554365)
            ·
              refine ⟨4011272533034899063332887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10696726754759730835554365 4011272533034899063332887)
              ·
                refine ⟨6016908799552348594999331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011272533034899063332887 6016908799552348594999331)
                ·
                  refine ⟨9025363199328522892498997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6016908799552348594999331 9025363199328522892498997)
                  ·
                    refine ⟨846127799937049021171781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9025363199328522892498997 846127799937049021171781)
                    ·
                      rfl

theorem cell22_2471742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2471742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471742 prefixEnd_2471742 := by exact prefixLift 2471742
  have htrace : WordTrace (prefixWord ++ tailWord_2471742) baseStart_2471742 baseEnd_2471742 := by
    simpa [prefixWord, tailWord_2471742, baseEnd_2471742] using wordTrace_append hprefix tailTrace_2471742
  have hstable : (prefixWord ++ tailWord_2471742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471742).length < 2 ^ (prefixWord ++ tailWord_2471742).sum := by decide
  have hdescent : baseEnd_2471742 < baseStart_2471742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471753 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_2471753 : Nat := 118140960795 + 2471753 * 2 ^ 59
def prefixEnd_2471753 : Nat := 4983230072969 + 3 ^ 40 * 2471753 * 2
def baseEnd_2471753 : Nat := 846131565461848659146747

theorem tailTrace_2471753 : CollatzResearch.WordTrace tailWord_2471753 prefixEnd_2471753 846131565461848659146747 := by
  unfold tailWord_2471753
  simp only [CollatzResearch.WordTrace]
  refine ⟨90152238214268497649083913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60101492142845665099389275 90152238214268497649083913)
  ·
    refine ⟨67614178660701373236812935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90152238214268497649083913 67614178660701373236812935)
    ·
      refine ⟨101421267991052059855219403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67614178660701373236812935 101421267991052059855219403)
      ·
        refine ⟨152131901986578089782829105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101421267991052059855219403 152131901986578089782829105)
        ·
          refine ⟨114098926489933567337121829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152131901986578089782829105 114098926489933567337121829)
          ·
            refine ⟨21393548716862543875710343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114098926489933567337121829 21393548716862543875710343)
            ·
              refine ⟨32090323075293815813565515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21393548716862543875710343 32090323075293815813565515)
              ·
                refine ⟨48135484612940723720348273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32090323075293815813565515 48135484612940723720348273)
                ·
                  refine ⟨36101613459705542790261205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48135484612940723720348273 36101613459705542790261205)
                  ·
                    refine ⟨846131565461848659146747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36101613459705542790261205 846131565461848659146747)
                    ·
                      rfl

theorem cell22_2471753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_2471753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471753 prefixEnd_2471753 := by exact prefixLift 2471753
  have htrace : WordTrace (prefixWord ++ tailWord_2471753) baseStart_2471753 baseEnd_2471753 := by
    simpa [prefixWord, tailWord_2471753, baseEnd_2471753] using wordTrace_append hprefix tailTrace_2471753
  have hstable : (prefixWord ++ tailWord_2471753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471753).length < 2 ^ (prefixWord ++ tailWord_2471753).sum := by decide
  have hdescent : baseEnd_2471753 < baseStart_2471753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471757 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2471757 : Nat := 118140960795 + 2471757 * 2 ^ 59
def prefixEnd_2471757 : Nat := 4983230072969 + 3 ^ 40 * 2471757 * 2
def baseEnd_2471757 : Nat := 846132934743593982046735

theorem tailTrace_2471757 : CollatzResearch.WordTrace tailWord_2471757 prefixEnd_2471757 846132934743593982046735 := by
  unfold tailWord_2471757
  simp only [CollatzResearch.WordTrace]
  refine ⟨90152384106254006332229525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60101589404169337554819683 90152384106254006332229525)
  ·
    refine ⟨4225893004980656546823259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90152384106254006332229525 4225893004980656546823259)
    ·
      refine ⟨6338839507470984820234889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4225893004980656546823259 6338839507470984820234889)
      ·
        refine ⟨4754129630603238615176167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6338839507470984820234889 4754129630603238615176167)
        ·
          refine ⟨7131194445904857922764251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754129630603238615176167 7131194445904857922764251)
          ·
            refine ⟨10696791668857286884146377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131194445904857922764251 10696791668857286884146377)
            ·
              refine ⟨8022593751642965163109783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10696791668857286884146377 8022593751642965163109783)
              ·
                refine ⟨12033890627464447744664675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8022593751642965163109783 12033890627464447744664675)
                ·
                  refine ⟨18050835941196671616997013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12033890627464447744664675 18050835941196671616997013)
                  ·
                    refine ⟨846132934743593982046735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18050835941196671616997013 846132934743593982046735)
                    ·
                      rfl

theorem cell22_2471757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2471757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471757 prefixEnd_2471757 := by exact prefixLift 2471757
  have htrace : WordTrace (prefixWord ++ tailWord_2471757) baseStart_2471757 baseEnd_2471757 := by
    simpa [prefixWord, tailWord_2471757, baseEnd_2471757] using wordTrace_append hprefix tailTrace_2471757
  have hstable : (prefixWord ++ tailWord_2471757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471757).length < 2 ^ (prefixWord ++ tailWord_2471757).sum := by decide
  have hdescent : baseEnd_2471757 < baseStart_2471757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471768 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_2471768 : Nat := 118140960795 + 2471768 * 2 ^ 59
def prefixEnd_2471768 : Nat := 4983230072969 + 3 ^ 40 * 2471768 * 2
def baseEnd_2471768 : Nat := 846136700268393620021701

theorem tailTrace_2471768 : CollatzResearch.WordTrace tailWord_2471768 prefixEnd_2471768 846136700268393620021701 := by
  unfold tailWord_2471768
  simp only [CollatzResearch.WordTrace]
  refine ⟨45076392654607077605439979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60101856872809436807253305 45076392654607077605439979)
  ·
    refine ⟨67614588981910616408159969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45076392654607077605439979 67614588981910616408159969)
    ·
      refine ⟨50710941736432962306119977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67614588981910616408159969 50710941736432962306119977)
      ·
        refine ⟨38033206302324721729589983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50710941736432962306119977 38033206302324721729589983)
        ·
          refine ⟨57049809453487082594384975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38033206302324721729589983 57049809453487082594384975)
          ·
            refine ⟨85574714180230623891577463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57049809453487082594384975 85574714180230623891577463)
            ·
              refine ⟨128362071270345935837366195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85574714180230623891577463 128362071270345935837366195)
              ·
                refine ⟨192543106905518903756049293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128362071270345935837366195 192543106905518903756049293)
                ·
                  refine ⟨72203665089569588908518485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192543106905518903756049293 72203665089569588908518485)
                  ·
                    refine ⟨846136700268393620021701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72203665089569588908518485 846136700268393620021701)
                    ·
                      rfl

theorem cell22_2471768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_2471768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471768 prefixEnd_2471768 := by exact prefixLift 2471768
  have htrace : WordTrace (prefixWord ++ tailWord_2471768) baseStart_2471768 baseEnd_2471768 := by
    simpa [prefixWord, tailWord_2471768, baseEnd_2471768] using wordTrace_append hprefix tailTrace_2471768
  have hstable : (prefixWord ++ tailWord_2471768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471768).length < 2 ^ (prefixWord ++ tailWord_2471768).sum := by decide
  have hdescent : baseEnd_2471768 < baseStart_2471768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471772 : List Nat := [2, 2, 4, 2, 2, 2, 8]
def baseStart_2471772 : Nat := 118140960795 + 2471772 * 2 ^ 59
def prefixEnd_2471772 : Nat := 4983230072969 + 3 ^ 40 * 2471772 * 2
def baseEnd_2471772 : Nat := 31338447020375516404507

theorem tailTrace_2471772 : CollatzResearch.WordTrace tailWord_2471772 prefixEnd_2471772 31338447020375516404507 := by
  unfold tailWord_2471772
  simp only [CollatzResearch.WordTrace]
  refine ⟨45076465600599831947012785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60101954134133109262683713 45076465600599831947012785)
  ·
    refine ⟨33807349200449873960259589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45076465600599831947012785 33807349200449873960259589)
    ·
      refine ⟨6338877975084351367548673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33807349200449873960259589 6338877975084351367548673)
      ·
        refine ⟨4754158481313263525661505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6338877975084351367548673 4754158481313263525661505)
        ·
          refine ⟨3565618860984947644246129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4754158481313263525661505 3565618860984947644246129)
          ·
            refine ⟨2674214145738710733184597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565618860984947644246129 2674214145738710733184597)
            ·
              refine ⟨31338447020375516404507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2674214145738710733184597 31338447020375516404507)
              ·
                rfl

theorem cell22_2471772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 8].length) (baseStart_2471772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471772 prefixEnd_2471772 := by exact prefixLift 2471772
  have htrace : WordTrace (prefixWord ++ tailWord_2471772) baseStart_2471772 baseEnd_2471772 := by
    simpa [prefixWord, tailWord_2471772, baseEnd_2471772] using wordTrace_append hprefix tailTrace_2471772
  have hstable : (prefixWord ++ tailWord_2471772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471772).length < 2 ^ (prefixWord ++ tailWord_2471772).sum := by decide
  have hdescent : baseEnd_2471772 < baseStart_2471772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471847 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2471847 : Nat := 118140960795 + 2471847 * 2 ^ 59
def prefixEnd_2471847 : Nat := 4983230072969 + 3 ^ 40 * 2471847 * 2
def baseEnd_2471847 : Nat := 846163743582863747296459

theorem tailTrace_2471847 : CollatzResearch.WordTrace tailWord_2471847 prefixEnd_2471847 846163743582863747296459 := by
  unfold tailWord_2471847
  simp only [CollatzResearch.WordTrace]
  refine ⟨90155666675927951703005795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60103777783951967802003863 90155666675927951703005795)
  ·
    refine ⟨135233500013891927554508693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90155666675927951703005795 135233500013891927554508693)
    ·
      refine ⟨6339070313151184104117595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135233500013891927554508693 6339070313151184104117595)
      ·
        refine ⟨9508605469726776156176393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6339070313151184104117595 9508605469726776156176393)
        ·
          refine ⟨7131454102295082117132295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9508605469726776156176393 7131454102295082117132295)
          ·
            refine ⟨10697181153442623175698443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131454102295082117132295 10697181153442623175698443)
            ·
              refine ⟨16045771730163934763547665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10697181153442623175698443 16045771730163934763547665)
              ·
                refine ⟨12034328797622951072660749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16045771730163934763547665 12034328797622951072660749)
                ·
                  refine ⟨4512873299108606652247781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12034328797622951072660749 4512873299108606652247781)
                  ·
                    refine ⟨846163743582863747296459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512873299108606652247781 846163743582863747296459)
                    ·
                      rfl

theorem cell22_2471847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2471847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471847 prefixEnd_2471847 := by exact prefixLift 2471847
  have htrace : WordTrace (prefixWord ++ tailWord_2471847) baseStart_2471847 baseEnd_2471847 := by
    simpa [prefixWord, tailWord_2471847, baseEnd_2471847] using wordTrace_append hprefix tailTrace_2471847
  have hstable : (prefixWord ++ tailWord_2471847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471847).length < 2 ^ (prefixWord ++ tailWord_2471847).sum := by decide
  have hdescent : baseEnd_2471847 < baseStart_2471847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471892 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2471892 : Nat := 118140960795 + 2471892 * 2 ^ 59
def prefixEnd_2471892 : Nat := 4983230072969 + 3 ^ 40 * 2471892 * 2
def baseEnd_2471892 : Nat := 846179148002498629921321

theorem tailTrace_2471892 : CollatzResearch.WordTrace tailWord_2471892 prefixEnd_2471892 846179148002498629921321 := by
  unfold tailWord_2471892
  simp only [CollatzResearch.WordTrace]
  refine ⟨45078653980382462194196965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60104871973843282925595953 45078653980382462194196965)
  ·
    refine ⟨8452247621321711661411931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45078653980382462194196965 8452247621321711661411931)
    ·
      refine ⟨12678371431982567492117897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452247621321711661411931 12678371431982567492117897)
      ·
        refine ⟨9508778573986925619088423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12678371431982567492117897 9508778573986925619088423)
        ·
          refine ⟨14263167860980388428632635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508778573986925619088423 14263167860980388428632635)
          ·
            refine ⟨21394751791470582642948953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14263167860980388428632635 21394751791470582642948953)
            ·
              refine ⟨16046063843602936982211715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21394751791470582642948953 16046063843602936982211715)
              ·
                refine ⟨24069095765404405473317573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16046063843602936982211715 24069095765404405473317573)
                ·
                  refine ⟨4512955456013326026247045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24069095765404405473317573 4512955456013326026247045)
                  ·
                    refine ⟨846179148002498629921321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4512955456013326026247045 846179148002498629921321)
                    ·
                      rfl

theorem cell22_2471892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2471892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471892 prefixEnd_2471892 := by exact prefixLift 2471892
  have htrace : WordTrace (prefixWord ++ tailWord_2471892) baseStart_2471892 baseEnd_2471892 := by
    simpa [prefixWord, tailWord_2471892, baseEnd_2471892] using wordTrace_append hprefix tailTrace_2471892
  have hstable : (prefixWord ++ tailWord_2471892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471892).length < 2 ^ (prefixWord ++ tailWord_2471892).sum := by decide
  have hdescent : baseEnd_2471892 < baseStart_2471892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471911 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2471911 : Nat := 118140960795 + 2471911 * 2 ^ 59
def prefixEnd_2471911 : Nat := 4983230072969 + 3 ^ 40 * 2471911 * 2
def baseEnd_2471911 : Nat := 846185652090788913696263

theorem tailTrace_2471911 : CollatzResearch.WordTrace tailWord_2471911 prefixEnd_2471911 846185652090788913696263 := by
  unfold tailWord_2471911
  simp only [CollatzResearch.WordTrace]
  refine ⟨90158000947696090633335587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60105333965130727088890391 90158000947696090633335587)
  ·
    refine ⟨135237001421544135950003381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90158000947696090633335587 135237001421544135950003381)
    ·
      refine ⟨12678468883269762745312817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135237001421544135950003381 12678468883269762745312817)
      ·
        refine ⟨9508851662452322058984613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12678468883269762745312817 9508851662452322058984613)
        ·
          refine ⟨1782909686709810386059615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9508851662452322058984613 1782909686709810386059615)
          ·
            refine ⟨2674364530064715579089423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782909686709810386059615 2674364530064715579089423)
            ·
              refine ⟨4011546795097073368634135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674364530064715579089423 4011546795097073368634135)
              ·
                refine ⟨6017320192645610052951203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011546795097073368634135 6017320192645610052951203)
                ·
                  refine ⟨9025980288968415079426805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6017320192645610052951203 9025980288968415079426805)
                  ·
                    refine ⟨846185652090788913696263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9025980288968415079426805 846185652090788913696263)
                    ·
                      rfl

theorem cell22_2471911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2471911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471911 prefixEnd_2471911 := by exact prefixLift 2471911
  have htrace : WordTrace (prefixWord ++ tailWord_2471911) baseStart_2471911 baseEnd_2471911 := by
    simpa [prefixWord, tailWord_2471911, baseEnd_2471911] using wordTrace_append hprefix tailTrace_2471911
  have hstable : (prefixWord ++ tailWord_2471911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471911).length < 2 ^ (prefixWord ++ tailWord_2471911).sum := by decide
  have hdescent : baseEnd_2471911 < baseStart_2471911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471920 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_2471920 : Nat := 118140960795 + 2471920 * 2 ^ 59
def prefixEnd_2471920 : Nat := 4983230072969 + 3 ^ 40 * 2471920 * 2
def baseEnd_2471920 : Nat := 846188732974715890221235

theorem tailTrace_2471920 : CollatzResearch.WordTrace tailWord_2471920 prefixEnd_2471920 846188732974715890221235 := by
  unfold tailWord_2471920
  simp only [CollatzResearch.WordTrace]
  refine ⟨45079164602331742585206607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60105552803108990113608809 45079164602331742585206607)
  ·
    refine ⟨67618746903497613877809911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45079164602331742585206607 67618746903497613877809911)
    ·
      refine ⟨101428120355246420816714867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67618746903497613877809911 101428120355246420816714867)
      ·
        refine ⟨152142180532869631225072301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101428120355246420816714867 152142180532869631225072301)
        ·
          refine ⟨57053317699826111709402113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152142180532869631225072301 57053317699826111709402113)
          ·
            refine ⟨42789988274869583782051585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57053317699826111709402113 42789988274869583782051585)
            ·
              refine ⟨32092491206152187836538689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42789988274869583782051585 32092491206152187836538689)
              ·
                refine ⟨24069368404614140877404017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32092491206152187836538689 24069368404614140877404017)
                ·
                  refine ⟨18052026303460605658053013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24069368404614140877404017 18052026303460605658053013)
                  ·
                    refine ⟨846188732974715890221235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18052026303460605658053013 846188732974715890221235)
                    ·
                      rfl

theorem cell22_2471920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_2471920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471920 prefixEnd_2471920 := by exact prefixLift 2471920
  have htrace : WordTrace (prefixWord ++ tailWord_2471920) baseStart_2471920 baseEnd_2471920 := by
    simpa [prefixWord, tailWord_2471920, baseEnd_2471920] using wordTrace_append hprefix tailTrace_2471920
  have hstable : (prefixWord ++ tailWord_2471920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471920).length < 2 ^ (prefixWord ++ tailWord_2471920).sum := by decide
  have hdescent : baseEnd_2471920 < baseStart_2471920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2471969 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 5]
def baseStart_2471969 : Nat := 118140960795 + 2471969 * 2 ^ 59
def prefixEnd_2471969 : Nat := 4983230072969 + 3 ^ 40 * 2471969 * 2
def baseEnd_2471969 : Nat := 282068502225365365248695

theorem tailTrace_2471969 : CollatzResearch.WordTrace tailWord_2471969 prefixEnd_2471969 282068502225365365248695 := by
  unfold tailWord_2471969
  simp only [CollatzResearch.WordTrace]
  refine ⟨90160116381485966538946961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60106744254323977692631307 90160116381485966538946961)
  ·
    refine ⟨67620087286114474904210221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90160116381485966538946961 67620087286114474904210221)
    ·
      refine ⟨25357532732292928089078833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67620087286114474904210221 25357532732292928089078833)
      ·
        refine ⟨19018149549219696066809125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25357532732292928089078833 19018149549219696066809125)
        ·
          refine ⟨3565903040478693012526711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19018149549219696066809125 3565903040478693012526711)
          ·
            refine ⟨5348854560718039518790067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565903040478693012526711 5348854560718039518790067)
            ·
              refine ⟨8023281841077059278185101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5348854560718039518790067 8023281841077059278185101)
              ·
                refine ⟨3008730690403897229319413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8023281841077059278185101 3008730690403897229319413)
                ·
                  refine ⟨282068502225365365248695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3008730690403897229319413 282068502225365365248695)
                  ·
                    rfl

theorem cell22_2471969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_2471969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2471969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2471969 prefixEnd_2471969 := by exact prefixLift 2471969
  have htrace : WordTrace (prefixWord ++ tailWord_2471969) baseStart_2471969 baseEnd_2471969 := by
    simpa [prefixWord, tailWord_2471969, baseEnd_2471969] using wordTrace_append hprefix tailTrace_2471969
  have hstable : (prefixWord ++ tailWord_2471969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2471969).length < 2 ^ (prefixWord ++ tailWord_2471969).sum := by decide
  have hdescent : baseEnd_2471969 < baseStart_2471969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2471969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472044 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_2472044 : Nat := 118140960795 + 2472044 * 2 ^ 59
def prefixEnd_2472044 : Nat := 4983230072969 + 3 ^ 40 * 2472044 * 2
def baseEnd_2472044 : Nat := 846231180708820900120855

theorem tailTrace_2472044 : CollatzResearch.WordTrace tailWord_2472044 prefixEnd_2472044 846231180708820900120855 := by
  unfold tailWord_2472044
  simp only [CollatzResearch.WordTrace]
  refine ⟨45081425928107127173963593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60108567904142836231951457 45081425928107127173963593)
  ·
    refine ⟨33811069446080345380472695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45081425928107127173963593 33811069446080345380472695)
    ·
      refine ⟨50716604169120518070709043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33811069446080345380472695 50716604169120518070709043)
      ·
        refine ⟨76074906253680777106063565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50716604169120518070709043 76074906253680777106063565)
        ·
          refine ⟨28528089845130291414773837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76074906253680777106063565 28528089845130291414773837)
          ·
            refine ⟨10698033691923859280540189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28528089845130291414773837 10698033691923859280540189)
            ·
              refine ⟨4011762634471447230202571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10698033691923859280540189 4011762634471447230202571)
              ·
                refine ⟨6017643951707170845303857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011762634471447230202571 6017643951707170845303857)
                ·
                  refine ⟨4513232963780378133977893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017643951707170845303857 4513232963780378133977893)
                  ·
                    refine ⟨846231180708820900120855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513232963780378133977893 846231180708820900120855)
                    ·
                      rfl

theorem cell22_2472044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_2472044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472044 prefixEnd_2472044 := by exact prefixLift 2472044
  have htrace : WordTrace (prefixWord ++ tailWord_2472044) baseStart_2472044 baseEnd_2472044 := by
    simpa [prefixWord, tailWord_2472044, baseEnd_2472044] using wordTrace_append hprefix tailTrace_2472044
  have hstable : (prefixWord ++ tailWord_2472044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472044).length < 2 ^ (prefixWord ++ tailWord_2472044).sum := by decide
  have hdescent : baseEnd_2472044 < baseStart_2472044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472168 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_2472168 : Nat := 118140960795 + 2472168 * 2 ^ 59
def prefixEnd_2472168 : Nat := 4983230072969 + 3 ^ 40 * 2472168 * 2
def baseEnd_2472168 : Nat := 846273628442925910020475

theorem tailTrace_2472168 : CollatzResearch.WordTrace tailWord_2472168 prefixEnd_2472168 846273628442925910020475 := by
  unfold tailWord_2472168
  simp only [CollatzResearch.WordTrace]
  refine ⟨45083687253882511762720579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60111583005176682350294105 45083687253882511762720579)
  ·
    refine ⟨67625530880823767644080869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45083687253882511762720579 67625530880823767644080869)
    ·
      refine ⟨12679787040154456433265163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67625530880823767644080869 12679787040154456433265163)
      ·
        refine ⟨19019680560231684649897745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12679787040154456433265163 19019680560231684649897745)
        ·
          refine ⟨14264760420173763487423309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19019680560231684649897745 14264760420173763487423309)
          ·
            refine ⟨5349285157565161307783741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14264760420173763487423309 5349285157565161307783741)
            ·
              refine ⟨2005981934086935490418903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5349285157565161307783741 2005981934086935490418903)
              ·
                refine ⟨3008972901130403235628355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2005981934086935490418903 3008972901130403235628355)
                ·
                  refine ⟨4513459351695604853442533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3008972901130403235628355 4513459351695604853442533)
                  ·
                    refine ⟨846273628442925910020475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513459351695604853442533 846273628442925910020475)
                    ·
                      rfl

theorem cell22_2472168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_2472168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472168 prefixEnd_2472168 := by exact prefixLift 2472168
  have htrace : WordTrace (prefixWord ++ tailWord_2472168) baseStart_2472168 baseEnd_2472168 := by
    simpa [prefixWord, tailWord_2472168, baseEnd_2472168] using wordTrace_append hprefix tailTrace_2472168
  have hstable : (prefixWord ++ tailWord_2472168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472168).length < 2 ^ (prefixWord ++ tailWord_2472168).sum := by decide
  have hdescent : baseEnd_2472168 < baseStart_2472168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472179 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 2, 4]
def baseStart_2472179 : Nat := 118140960795 + 2472179 * 2 ^ 59
def prefixEnd_2472179 : Nat := 4983230072969 + 3 ^ 40 * 2472179 * 2
def baseEnd_2472179 : Nat := 846277393967725547995441

theorem tailTrace_2472179 : CollatzResearch.WordTrace tailWord_2472179 prefixEnd_2472179 846277393967725547995441 := by
  unfold tailWord_2472179
  simp only [CollatzResearch.WordTrace]
  refine ⟨90167775710725172404091591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60111850473816781602727727 90167775710725172404091591)
  ·
    refine ⟨135251663566087758606137387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90167775710725172404091591 135251663566087758606137387)
    ·
      refine ⟨202877495349131637909206081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135251663566087758606137387 202877495349131637909206081)
      ·
        refine ⟨152158121511848728431904561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202877495349131637909206081 152158121511848728431904561)
        ·
          refine ⟨114118591133886546323928421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152158121511848728431904561 114118591133886546323928421)
          ·
            refine ⟨21397235837603727435736579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114118591133886546323928421 21397235837603727435736579)
            ·
              refine ⟨32095853756405591153604869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21397235837603727435736579 32095853756405591153604869)
              ·
                refine ⟨6017972579326048341300913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32095853756405591153604869 6017972579326048341300913)
                ·
                  refine ⟨4513479434494536255975685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6017972579326048341300913 4513479434494536255975685)
                  ·
                    refine ⟨846277393967725547995441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513479434494536255975685 846277393967725547995441)
                    ·
                      rfl

theorem cell22_2472179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 4].length) (baseStart_2472179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472179 prefixEnd_2472179 := by exact prefixLift 2472179
  have htrace : WordTrace (prefixWord ++ tailWord_2472179) baseStart_2472179 baseEnd_2472179 := by
    simpa [prefixWord, tailWord_2472179, baseEnd_2472179] using wordTrace_append hprefix tailTrace_2472179
  have hstable : (prefixWord ++ tailWord_2472179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472179).length < 2 ^ (prefixWord ++ tailWord_2472179).sum := by decide
  have hdescent : baseEnd_2472179 < baseStart_2472179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472232 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_2472232 : Nat := 118140960795 + 2472232 * 2 ^ 59
def prefixEnd_2472232 : Nat := 4983230072969 + 3 ^ 40 * 2472232 * 2
def baseEnd_2472232 : Nat := 846295536950851076420279

theorem tailTrace_2472232 : CollatzResearch.WordTrace tailWord_2472232 prefixEnd_2472232 846295536950851076420279 := by
  unfold tailWord_2472232
  simp only [CollatzResearch.WordTrace]
  refine ⟨45084854389766581227885475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60113139186355441637180633 45084854389766581227885475)
  ·
    refine ⟨67627281584649871841828213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45084854389766581227885475 67627281584649871841828213)
    ·
      refine ⟨6340057648560925485171395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67627281584649871841828213 6340057648560925485171395)
      ·
        refine ⟨9510086472841388227757093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340057648560925485171395 9510086472841388227757093)
        ·
          refine ⟨1783141213657760292704455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9510086472841388227757093 1783141213657760292704455)
          ·
            refine ⟨2674711820486640439056683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783141213657760292704455 2674711820486640439056683)
            ·
              refine ⟨4012067730729960658585025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674711820486640439056683 4012067730729960658585025)
              ·
                refine ⟨3009050798047470493938769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4012067730729960658585025 3009050798047470493938769)
                ·
                  refine ⟨2256788098535602870454077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009050798047470493938769 2256788098535602870454077)
                  ·
                    refine ⟨846295536950851076420279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256788098535602870454077 846295536950851076420279)
                    ·
                      rfl

theorem cell22_2472232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_2472232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472232 prefixEnd_2472232 := by exact prefixLift 2472232
  have htrace : WordTrace (prefixWord ++ tailWord_2472232) baseStart_2472232 baseEnd_2472232 := by
    simpa [prefixWord, tailWord_2472232, baseEnd_2472232] using wordTrace_append hprefix tailTrace_2472232
  have hstable : (prefixWord ++ tailWord_2472232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472232).length < 2 ^ (prefixWord ++ tailWord_2472232).sum := by decide
  have hdescent : baseEnd_2472232 < baseStart_2472232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472243 : List Nat := [1, 1, 1, 2, 5, 1, 1, 6, 1, 3]
def baseStart_2472243 : Nat := 118140960795 + 2472243 * 2 ^ 59
def prefixEnd_2472243 : Nat := 4983230072969 + 3 ^ 40 * 2472243 * 2
def baseEnd_2472243 : Nat := 846299302475650714395245

theorem tailTrace_2472243 : CollatzResearch.WordTrace tailWord_2472243 prefixEnd_2472243 846299302475650714395245 := by
  unfold tailWord_2472243
  simp only [CollatzResearch.WordTrace]
  refine ⟨90170109982493311334421383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60113406654995540889614255 90170109982493311334421383)
  ·
    refine ⟨135255164973739967001632075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90170109982493311334421383 135255164973739967001632075)
    ·
      refine ⟨202882747460609950502448113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135255164973739967001632075 202882747460609950502448113)
      ·
        refine ⟨152162060595457462876836085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202882747460609950502448113 152162060595457462876836085)
        ·
          refine ⟨14265193180824137144703383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152162060595457462876836085 14265193180824137144703383)
          ·
            refine ⟨21397789771236205717055075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14265193180824137144703383 21397789771236205717055075)
            ·
              refine ⟨32096684656854308575582613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21397789771236205717055075 32096684656854308575582613)
              ·
                refine ⟨1504532093290045714480435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32096684656854308575582613 1504532093290045714480435)
                ·
                  refine ⟨2256798139935068571720653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504532093290045714480435 2256798139935068571720653)
                  ·
                    refine ⟨846299302475650714395245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256798139935068571720653 846299302475650714395245)
                    ·
                      rfl

theorem cell22_2472243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 3].length) (baseStart_2472243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472243 prefixEnd_2472243 := by exact prefixLift 2472243
  have htrace : WordTrace (prefixWord ++ tailWord_2472243) baseStart_2472243 baseEnd_2472243 := by
    simpa [prefixWord, tailWord_2472243, baseEnd_2472243] using wordTrace_append hprefix tailTrace_2472243
  have hstable : (prefixWord ++ tailWord_2472243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472243).length < 2 ^ (prefixWord ++ tailWord_2472243).sum := by decide
  have hdescent : baseEnd_2472243 < baseStart_2472243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472277 : List Nat := [1, 3, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_2472277 : Nat := 118140960795 + 2472277 * 2 ^ 59
def prefixEnd_2472277 : Nat := 4983230072969 + 3 ^ 40 * 2472277 * 2
def baseEnd_2472277 : Nat := 846310941370485959045141

theorem tailTrace_2472277 : CollatzResearch.WordTrace tailWord_2472277 prefixEnd_2472277 846310941370485959045141 := by
  unfold tailWord_2472277
  simp only [CollatzResearch.WordTrace]
  refine ⟨90171350064370135141159085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60114233376246756760772723 90171350064370135141159085)
  ·
    refine ⟨33814256274138800677934657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90171350064370135141159085 33814256274138800677934657)
    ·
      refine ⟨25360692205604100508450993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33814256274138800677934657 25360692205604100508450993)
      ·
        refine ⟨19020519154203075381338245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25360692205604100508450993 19020519154203075381338245)
        ·
          refine ⟨3566347341413076634000921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19020519154203075381338245 3566347341413076634000921)
          ·
            refine ⟨2674760506059807475500691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3566347341413076634000921 2674760506059807475500691)
            ·
              refine ⟨4012140759089711213251037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674760506059807475500691 4012140759089711213251037)
              ·
                refine ⟨1504552784658641704969139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4012140759089711213251037 1504552784658641704969139)
                ·
                  refine ⟨2256829176987962557453709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504552784658641704969139 2256829176987962557453709)
                  ·
                    refine ⟨846310941370485959045141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256829176987962557453709 846310941370485959045141)
                    ·
                      rfl

theorem cell22_2472277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_2472277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472277 prefixEnd_2472277 := by exact prefixLift 2472277
  have htrace : WordTrace (prefixWord ++ tailWord_2472277) baseStart_2472277 baseEnd_2472277 := by
    simpa [prefixWord, tailWord_2472277, baseEnd_2472277] using wordTrace_append hprefix tailTrace_2472277
  have hstable : (prefixWord ++ tailWord_2472277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472277).length < 2 ^ (prefixWord ++ tailWord_2472277).sum := by decide
  have hdescent : baseEnd_2472277 < baseStart_2472277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472299 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 3, 5]
def baseStart_2472299 : Nat := 118140960795 + 2472299 * 2 ^ 59
def prefixEnd_2472299 : Nat := 4983230072969 + 3 ^ 40 * 2472299 * 2
def baseEnd_2472299 : Nat := 846318472420085234995073

theorem tailTrace_2472299 : CollatzResearch.WordTrace tailWord_2472299 prefixEnd_2472299 846318472420085234995073 := by
  unfold tailWord_2472299
  simp only [CollatzResearch.WordTrace]
  refine ⟨90172152470290432898459951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60114768313526955265639967 90172152470290432898459951)
  ·
    refine ⟨135258228705435649347689927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90172152470290432898459951 135258228705435649347689927)
    ·
      refine ⟨202887343058153474021534891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135258228705435649347689927 202887343058153474021534891)
      ·
        refine ⟨304331014587230211032302337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202887343058153474021534891 304331014587230211032302337)
        ·
          refine ⟨228248260940422658274226753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304331014587230211032302337 228248260940422658274226753)
          ·
            refine ⟨171186195705316993705670065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228248260940422658274226753 171186195705316993705670065)
            ·
              refine ⟨128389646778987745279252549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171186195705316993705670065 128389646778987745279252549)
              ·
                refine ⟨24073058771060202239859853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128389646778987745279252549 24073058771060202239859853)
                ·
                  refine ⟨9027397039147575839947445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24073058771060202239859853 9027397039147575839947445)
                  ·
                    refine ⟨846318472420085234995073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9027397039147575839947445 846318472420085234995073)
                    ·
                      rfl

theorem cell22_2472299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_2472299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472299 prefixEnd_2472299 := by exact prefixLift 2472299
  have htrace : WordTrace (prefixWord ++ tailWord_2472299) baseStart_2472299 baseEnd_2472299 := by
    simpa [prefixWord, tailWord_2472299, baseEnd_2472299] using wordTrace_append hprefix tailTrace_2472299
  have hstable : (prefixWord ++ tailWord_2472299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472299).length < 2 ^ (prefixWord ++ tailWord_2472299).sum := by decide
  have hdescent : baseEnd_2472299 < baseStart_2472299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472316 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_2472316 : Nat := 118140960795 + 2472316 * 2 ^ 59
def prefixEnd_2472316 : Nat := 4983230072969 + 3 ^ 40 * 2472316 * 2
def baseEnd_2472316 : Nat := 846324291867502857320021

theorem tailTrace_2472316 : CollatzResearch.WordTrace tailWord_2472316 prefixEnd_2472316 846324291867502857320021 := by
  unfold tailWord_2472316
  simp only [CollatzResearch.WordTrace]
  refine ⟨45086386255614422400914401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60115181674152563201219201 45086386255614422400914401)
  ·
    refine ⟨33814789691710816800685801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45086386255614422400914401 33814789691710816800685801)
    ·
      refine ⟨25361092268783112600514351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33814789691710816800685801 25361092268783112600514351)
      ·
        refine ⟨38041638403174668900771527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25361092268783112600514351 38041638403174668900771527)
        ·
          refine ⟨57062457604762003351157291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38041638403174668900771527 57062457604762003351157291)
          ·
            refine ⟨85593686407143005026735937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57062457604762003351157291 85593686407143005026735937)
            ·
              refine ⟨64195264805357253770051953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85593686407143005026735937 64195264805357253770051953)
              ·
                refine ⟨48146448604017940327538965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64195264805357253770051953 48146448604017940327538965)
                ·
                  refine ⟨2256864778313340952853389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48146448604017940327538965 2256864778313340952853389)
                  ·
                    refine ⟨846324291867502857320021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256864778313340952853389 846324291867502857320021)
                    ·
                      rfl

theorem cell22_2472316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_2472316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472316 prefixEnd_2472316 := by exact prefixLift 2472316
  have htrace : WordTrace (prefixWord ++ tailWord_2472316) baseStart_2472316 baseEnd_2472316 := by
    simpa [prefixWord, tailWord_2472316, baseEnd_2472316] using wordTrace_append hprefix tailTrace_2472316
  have hstable : (prefixWord ++ tailWord_2472316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472316).length < 2 ^ (prefixWord ++ tailWord_2472316).sum := by decide
  have hdescent : baseEnd_2472316 < baseStart_2472316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472331 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_2472331 : Nat := 118140960795 + 2472331 * 2 ^ 59
def prefixEnd_2472331 : Nat := 4983230072969 + 3 ^ 40 * 2472331 * 2
def baseEnd_2472331 : Nat := 846329426674047818194975

theorem tailTrace_2472331 : CollatzResearch.WordTrace tailWord_2472331 prefixEnd_2472331 846329426674047818194975 := by
  unfold tailWord_2472331
  simp only [CollatzResearch.WordTrace]
  refine ⟨90173319606174502363624847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60115546404116334909083231 90173319606174502363624847)
  ·
    refine ⟨135259979409261753545437271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90173319606174502363624847 135259979409261753545437271)
    ·
      refine ⟨202889969113892630318155907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135259979409261753545437271 202889969113892630318155907)
      ·
        refine ⟨304334953670838945477233861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202889969113892630318155907 304334953670838945477233861)
        ·
          refine ⟨57062803813282302276981349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304334953670838945477233861 57062803813282302276981349)
          ·
            refine ⟨10699275714990431676934003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57062803813282302276981349 10699275714990431676934003)
            ·
              refine ⟨16048913572485647515401005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10699275714990431676934003 16048913572485647515401005)
              ·
                refine ⟨6018342589682117818275377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16048913572485647515401005 6018342589682117818275377)
                ·
                  refine ⟨4513756942261588363706533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6018342589682117818275377 4513756942261588363706533)
                  ·
                    refine ⟨846329426674047818194975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4513756942261588363706533 846329426674047818194975)
                    ·
                      rfl

theorem cell22_2472331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_2472331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472331 prefixEnd_2472331 := by exact prefixLift 2472331
  have htrace : WordTrace (prefixWord ++ tailWord_2472331) baseStart_2472331 baseEnd_2472331 := by
    simpa [prefixWord, tailWord_2472331, baseEnd_2472331] using wordTrace_append hprefix tailTrace_2472331
  have hstable : (prefixWord ++ tailWord_2472331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472331).length < 2 ^ (prefixWord ++ tailWord_2472331).sum := by decide
  have hdescent : baseEnd_2472331 < baseStart_2472331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472361 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_2472361 : Nat := 118140960795 + 2472361 * 2 ^ 59
def prefixEnd_2472361 : Nat := 4983230072969 + 3 ^ 40 * 2472361 * 2
def baseEnd_2472361 : Nat := 846339696287137739944883

theorem tailTrace_2472361 : CollatzResearch.WordTrace tailWord_2472361 prefixEnd_2472361 846339696287137739944883 := by
  unfold tailWord_2472361
  simp only [CollatzResearch.WordTrace]
  refine ⟨90174413796065817487216937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60116275864043878324811291 90174413796065817487216937)
  ·
    refine ⟨67630810347049363115412703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90174413796065817487216937 67630810347049363115412703)
    ·
      refine ⟨101446215520574044673119055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67630810347049363115412703 101446215520574044673119055)
      ·
        refine ⟨152169323280861067009678583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101446215520574044673119055 152169323280861067009678583)
        ·
          refine ⟨228253984921291600514517875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152169323280861067009678583 228253984921291600514517875)
          ·
            refine ⟨342380977381937400771776813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228253984921291600514517875 342380977381937400771776813)
            ·
              refine ⟨128392866518226525289416305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342380977381937400771776813 128392866518226525289416305)
              ·
                refine ⟨96294649888669893967062229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128392866518226525289416305 96294649888669893967062229)
                ·
                  refine ⟨2256905856765700639853021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 96294649888669893967062229 2256905856765700639853021)
                  ·
                    refine ⟨846339696287137739944883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2256905856765700639853021 846339696287137739944883)
                    ·
                      rfl

theorem cell22_2472361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_2472361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472361 prefixEnd_2472361 := by exact prefixLift 2472361
  have htrace : WordTrace (prefixWord ++ tailWord_2472361) baseStart_2472361 baseEnd_2472361 := by
    simpa [prefixWord, tailWord_2472361, baseEnd_2472361] using wordTrace_append hprefix tailTrace_2472361
  have hstable : (prefixWord ++ tailWord_2472361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472361).length < 2 ^ (prefixWord ++ tailWord_2472361).sum := by decide
  have hdescent : baseEnd_2472361 < baseStart_2472361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472451 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_2472451 : Nat := 118140960795 + 2472451 * 2 ^ 59
def prefixEnd_2472451 : Nat := 4983230072969 + 3 ^ 40 * 2472451 * 2
def baseEnd_2472451 : Nat := 846370505126407505194607

theorem tailTrace_2472451 : CollatzResearch.WordTrace tailWord_2472451 prefixEnd_2472451 846370505126407505194607 := by
  unfold tailWord_2472451
  simp only [CollatzResearch.WordTrace]
  refine ⟨90177696365739762857993207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60118464243826508571995471 90177696365739762857993207)
  ·
    refine ⟨135266544548609644286989811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90177696365739762857993207 135266544548609644286989811)
    ·
      refine ⟨202899816822914466430484717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135266544548609644286989811 202899816822914466430484717)
      ·
        refine ⟨76087431308592924911431769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202899816822914466430484717 76087431308592924911431769)
        ·
          refine ⟨57065573481444693683573827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76087431308592924911431769 57065573481444693683573827)
          ·
            refine ⟨85598360222167040525360741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57065573481444693683573827 85598360222167040525360741)
            ·
              refine ⟨16049692541656320098505139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85598360222167040525360741 16049692541656320098505139)
              ·
                refine ⟨24074538812484480147757709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16049692541656320098505139 24074538812484480147757709)
                ·
                  refine ⟨9027952054681680055409141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24074538812484480147757709 9027952054681680055409141)
                  ·
                    refine ⟨846370505126407505194607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9027952054681680055409141 846370505126407505194607)
                    ·
                      rfl

theorem cell22_2472451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_2472451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472451 prefixEnd_2472451 := by exact prefixLift 2472451
  have htrace : WordTrace (prefixWord ++ tailWord_2472451) baseStart_2472451 baseEnd_2472451 := by
    simpa [prefixWord, tailWord_2472451, baseEnd_2472451] using wordTrace_append hprefix tailTrace_2472451
  have hstable : (prefixWord ++ tailWord_2472451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472451).length < 2 ^ (prefixWord ++ tailWord_2472451).sum := by decide
  have hdescent : baseEnd_2472451 < baseStart_2472451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472496 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_2472496 : Nat := 118140960795 + 2472496 * 2 ^ 59
def prefixEnd_2472496 : Nat := 4983230072969 + 3 ^ 40 * 2472496 * 2
def baseEnd_2472496 : Nat := 846385909546042387819469

theorem tailTrace_2472496 : CollatzResearch.WordTrace tailWord_2472496 prefixEnd_2472496 846385909546042387819469 := by
  unfold tailWord_2472496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45089668825288367771690671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60119558433717823695587561 45089668825288367771690671)
  ·
    refine ⟨67634503237932551657536007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45089668825288367771690671 67634503237932551657536007)
    ·
      refine ⟨101451754856898827486304011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67634503237932551657536007 101451754856898827486304011)
      ·
        refine ⟨152177632285348241229456017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101451754856898827486304011 152177632285348241229456017)
        ·
          refine ⟨114133224214011180922092013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152177632285348241229456017 114133224214011180922092013)
          ·
            refine ⟨42799959080254192845784505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114133224214011180922092013 42799959080254192845784505)
            ·
              refine ⟨32099969310190644634338379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42799959080254192845784505 32099969310190644634338379)
              ·
                refine ⟨48149953965285966951507569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32099969310190644634338379 48149953965285966951507569)
                ·
                  refine ⟨36112465473964475213630677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48149953965285966951507569 36112465473964475213630677)
                  ·
                    refine ⟨846385909546042387819469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36112465473964475213630677 846385909546042387819469)
                    ·
                      rfl

theorem cell22_2472496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_2472496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472496 prefixEnd_2472496 := by exact prefixLift 2472496
  have htrace : WordTrace (prefixWord ++ tailWord_2472496) baseStart_2472496 baseEnd_2472496 := by
    simpa [prefixWord, tailWord_2472496, baseEnd_2472496] using wordTrace_append hprefix tailTrace_2472496
  have hstable : (prefixWord ++ tailWord_2472496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472496).length < 2 ^ (prefixWord ++ tailWord_2472496).sum := by decide
  have hdescent : baseEnd_2472496 < baseStart_2472496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472530 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_2472530 : Nat := 118140960795 + 2472530 * 2 ^ 59
def prefixEnd_2472530 : Nat := 4983230072969 + 3 ^ 40 * 2472530 * 2
def baseEnd_2472530 : Nat := 846397548440877632469365

theorem tailTrace_2472530 : CollatzResearch.WordTrace tailWord_2472530 prefixEnd_2472530 846397548440877632469365 := by
  unfold tailWord_2472530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22545144433113389837529761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60120385154969039566746029 22545144433113389837529761)
  ·
    refine ⟨16908858324835042378147321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22545144433113389837529761 16908858324835042378147321)
    ·
      refine ⟨12681643743626281783610491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16908858324835042378147321 12681643743626281783610491)
      ·
        refine ⟨19022465615439422675415737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12681643743626281783610491 19022465615439422675415737)
        ·
          refine ⟨14266849211579567006561803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19022465615439422675415737 14266849211579567006561803)
          ·
            refine ⟨21400273817369350509842705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14266849211579567006561803 21400273817369350509842705)
            ·
              refine ⟨16050205363027012882382029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21400273817369350509842705 16050205363027012882382029)
              ·
                refine ⟨6018827011135129830893261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16050205363027012882382029 6018827011135129830893261)
                ·
                  refine ⟨2257060129175673686584973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6018827011135129830893261 2257060129175673686584973)
                  ·
                    refine ⟨846397548440877632469365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257060129175673686584973 846397548440877632469365)
                    ·
                      rfl

theorem cell22_2472530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_2472530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472530 prefixEnd_2472530 := by exact prefixLift 2472530
  have htrace : WordTrace (prefixWord ++ tailWord_2472530) baseStart_2472530 baseEnd_2472530 := by
    simpa [prefixWord, tailWord_2472530, baseEnd_2472530] using wordTrace_append hprefix tailTrace_2472530
  have hstable : (prefixWord ++ tailWord_2472530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472530).length < 2 ^ (prefixWord ++ tailWord_2472530).sum := by decide
  have hdescent : baseEnd_2472530 < baseStart_2472530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472650 : List Nat := [3, 1, 2, 1, 4, 2, 2, 7]
def baseStart_2472650 : Nat := 118140960795 + 2472650 * 2 ^ 59
def prefixEnd_2472650 : Nat := 4983230072969 + 3 ^ 40 * 2472650 * 2
def baseEnd_2472650 : Nat := 94048736321470813274333

theorem tailTrace_2472650 : CollatzResearch.WordTrace tailWord_2472650 prefixEnd_2472650 94048736321470813274333 := by
  unfold tailWord_2472650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22546238623004704961121851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60123302994679213229658269 22546238623004704961121851)
  ·
    refine ⟨33819357934507057441682777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22546238623004704961121851 33819357934507057441682777)
    ·
      refine ⟨25364518450880293081262083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33819357934507057441682777 25364518450880293081262083)
      ·
        refine ⟨38046777676320439621893125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25364518450880293081262083 38046777676320439621893125)
        ·
          refine ⟨7133770814310082429104961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38046777676320439621893125 7133770814310082429104961)
          ·
            refine ⟨5350328110732561821828721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7133770814310082429104961 5350328110732561821828721)
            ·
              refine ⟨4012746083049421366371541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350328110732561821828721 4012746083049421366371541)
              ·
                refine ⟨94048736321470813274333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4012746083049421366371541 94048736321470813274333)
                ·
                  rfl

theorem cell22_2472650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 7].length) (baseStart_2472650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472650 prefixEnd_2472650 := by exact prefixLift 2472650
  have htrace : WordTrace (prefixWord ++ tailWord_2472650) baseStart_2472650 baseEnd_2472650 := by
    simpa [prefixWord, tailWord_2472650, baseEnd_2472650] using wordTrace_append hprefix tailTrace_2472650
  have hstable : (prefixWord ++ tailWord_2472650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472650).length < 2 ^ (prefixWord ++ tailWord_2472650).sum := by decide
  have hdescent : baseEnd_2472650 < baseStart_2472650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472654 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_2472654 : Nat := 118140960795 + 2472654 * 2 ^ 59
def prefixEnd_2472654 : Nat := 4983230072969 + 3 ^ 40 * 2472654 * 2
def baseEnd_2472654 : Nat := 846439996174982642368985

theorem tailTrace_2472654 : CollatzResearch.WordTrace tailWord_2472654 prefixEnd_2472654 846439996174982642368985 := by
  unfold tailWord_2472654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11273137548000541065954127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60123400256002885685088677 11273137548000541065954127)
  ·
    refine ⟨16909706322000811598931191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11273137548000541065954127 16909706322000811598931191)
    ·
      refine ⟨25364559483001217398396787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16909706322000811598931191 25364559483001217398396787)
      ·
        refine ⟨38046839224501826097595181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25364559483001217398396787 38046839224501826097595181)
        ·
          refine ⟨14267564709188184786598193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38046839224501826097595181 14267564709188184786598193)
          ·
            refine ⟨10700673531891138589948645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14267564709188184786598193 10700673531891138589948645)
            ·
              refine ⟨2006376287229588485615371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10700673531891138589948645 2006376287229588485615371)
              ·
                refine ⟨3009564430844382728423057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006376287229588485615371 3009564430844382728423057)
                ·
                  refine ⟨2257173323133287046317293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009564430844382728423057 2257173323133287046317293)
                  ·
                    refine ⟨846439996174982642368985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257173323133287046317293 846439996174982642368985)
                    ·
                      rfl

theorem cell22_2472654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_2472654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472654 prefixEnd_2472654 := by exact prefixLift 2472654
  have htrace : WordTrace (prefixWord ++ tailWord_2472654) baseStart_2472654 baseEnd_2472654 := by
    simpa [prefixWord, tailWord_2472654, baseEnd_2472654] using wordTrace_append hprefix tailTrace_2472654
  have hstable : (prefixWord ++ tailWord_2472654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472654).length < 2 ^ (prefixWord ++ tailWord_2472654).sum := by decide
  have hdescent : baseEnd_2472654 < baseStart_2472654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472665 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_2472665 : Nat := 118140960795 + 2472665 * 2 ^ 59
def prefixEnd_2472665 : Nat := 4983230072969 + 3 ^ 40 * 2472665 * 2
def baseEnd_2472665 : Nat := 846443761699782280343951

theorem tailTrace_2472665 : CollatzResearch.WordTrace tailWord_2472665 prefixEnd_2472665 846443761699782280343951 := by
  unfold tailWord_2472665
  simp only [CollatzResearch.WordTrace]
  refine ⟨90185501586964477406283449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60123667724642984937522299 90185501586964477406283449)
  ·
    refine ⟨67639126190223358054712587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90185501586964477406283449 67639126190223358054712587)
    ·
      refine ⟨101458689285335037082068881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67639126190223358054712587 101458689285335037082068881)
      ·
        refine ⟨76094016964001277811551661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101458689285335037082068881 76094016964001277811551661)
        ·
          refine ⟨28535256361500479179331873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76094016964001277811551661 28535256361500479179331873)
          ·
            refine ⟨21401442271125359384498905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28535256361500479179331873 21401442271125359384498905)
            ·
              refine ⟨16051081703344019538374179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21401442271125359384498905 16051081703344019538374179)
              ·
                refine ⟨24076622555016029307561269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16051081703344019538374179 24076622555016029307561269)
                ·
                  refine ⟨2257183364532752747583869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24076622555016029307561269 2257183364532752747583869)
                  ·
                    refine ⟨846443761699782280343951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257183364532752747583869 846443761699782280343951)
                    ·
                      rfl

theorem cell22_2472665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_2472665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472665 prefixEnd_2472665 := by exact prefixLift 2472665
  have htrace : WordTrace (prefixWord ++ tailWord_2472665) baseStart_2472665 baseEnd_2472665 := by
    simpa [prefixWord, tailWord_2472665, baseEnd_2472665] using wordTrace_append hprefix tailTrace_2472665
  have hstable : (prefixWord ++ tailWord_2472665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472665).length < 2 ^ (prefixWord ++ tailWord_2472665).sum := by decide
  have hdescent : baseEnd_2472665 < baseStart_2472665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472725 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_2472725 : Nat := 118140960795 + 2472725 * 2 ^ 59
def prefixEnd_2472725 : Nat := 4983230072969 + 3 ^ 40 * 2472725 * 2
def baseEnd_2472725 : Nat := 846464300925962123843767

theorem tailTrace_2472725 : CollatzResearch.WordTrace tailWord_2472725 prefixEnd_2472725 846464300925962123843767 := by
  unfold tailWord_2472725
  simp only [CollatzResearch.WordTrace]
  refine ⟨90187689966747107653467629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60125126644498071768978419 90187689966747107653467629)
  ·
    refine ⟨33820383737530165370050361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90187689966747107653467629 33820383737530165370050361)
    ·
      refine ⟨25365287803147624027537771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33820383737530165370050361 25365287803147624027537771)
      ·
        refine ⟨38047931704721436041306657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25365287803147624027537771 38047931704721436041306657)
        ·
          refine ⟨28535948778541077030979993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38047931704721436041306657 28535948778541077030979993)
          ·
            refine ⟨21401961583905807773234995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28535948778541077030979993 21401961583905807773234995)
            ·
              refine ⟨32102942375858711659852493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21401961583905807773234995 32102942375858711659852493)
              ·
                refine ⟨12038603390947016872444685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32102942375858711659852493 12038603390947016872444685)
                ·
                  refine ⟨4514476271605131327166757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12038603390947016872444685 4514476271605131327166757)
                  ·
                    refine ⟨846464300925962123843767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4514476271605131327166757 846464300925962123843767)
                    ·
                      rfl

theorem cell22_2472725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_2472725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472725 prefixEnd_2472725 := by exact prefixLift 2472725
  have htrace : WordTrace (prefixWord ++ tailWord_2472725) baseStart_2472725 baseEnd_2472725 := by
    simpa [prefixWord, tailWord_2472725, baseEnd_2472725] using wordTrace_append hprefix tailTrace_2472725
  have hstable : (prefixWord ++ tailWord_2472725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472725).length < 2 ^ (prefixWord ++ tailWord_2472725).sum := by decide
  have hdescent : baseEnd_2472725 < baseStart_2472725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472733 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_2472733 : Nat := 118140960795 + 2472733 * 2 ^ 59
def prefixEnd_2472733 : Nat := 4983230072969 + 3 ^ 40 * 2472733 * 2
def baseEnd_2472733 : Nat := 846467039489452769643743

theorem tailTrace_2472733 : CollatzResearch.WordTrace tailWord_2472733 prefixEnd_2472733 846467039489452769643743 := by
  unfold tailWord_2472733
  simp only [CollatzResearch.WordTrace]
  refine ⟨90187981750718125019758853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60125321167145416679839235 90187981750718125019758853)
  ·
    refine ⟨16910246578259648441204785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90187981750718125019758853 16910246578259648441204785)
    ·
      refine ⟨12682684933694736330903589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16910246578259648441204785 12682684933694736330903589)
      ·
        refine ⟨2378003425067763062044423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12682684933694736330903589 2378003425067763062044423)
        ·
          refine ⟨3567005137601644593066635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378003425067763062044423 3567005137601644593066635)
          ·
            refine ⟨5350507706402466889599953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567005137601644593066635 5350507706402466889599953)
            ·
              refine ⟨4012880779801850167199965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350507706402466889599953 4012880779801850167199965)
              ·
                refine ⟨1504830292425693812699987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4012880779801850167199965 1504830292425693812699987)
                ·
                  refine ⟨2257245438638540719049981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1504830292425693812699987 2257245438638540719049981)
                  ·
                    refine ⟨846467039489452769643743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257245438638540719049981 846467039489452769643743)
                    ·
                      rfl

theorem cell22_2472733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_2472733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472733 prefixEnd_2472733 := by exact prefixLift 2472733
  have htrace : WordTrace (prefixWord ++ tailWord_2472733) baseStart_2472733 baseEnd_2472733 := by
    simpa [prefixWord, tailWord_2472733, baseEnd_2472733] using wordTrace_append hprefix tailTrace_2472733
  have hstable : (prefixWord ++ tailWord_2472733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472733).length < 2 ^ (prefixWord ++ tailWord_2472733).sum := by decide
  have hdescent : baseEnd_2472733 < baseStart_2472733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472746 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 5]
def baseStart_2472746 : Nat := 118140960795 + 2472746 * 2 ^ 59
def prefixEnd_2472746 : Nat := 4983230072969 + 3 ^ 40 * 2472746 * 2
def baseEnd_2472746 : Nat := 282157163218375023022901

theorem tailTrace_2472746 : CollatzResearch.WordTrace tailWord_2472746 prefixEnd_2472746 282157163218375023022901 := by
  unfold tailWord_2472746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22547113974917757059995523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60125637266447352159988061 22547113974917757059995523)
  ·
    refine ⟨33820670962376635589993285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22547113974917757059995523 33820670962376635589993285)
    ·
      refine ⟨6341375805445619173123741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33820670962376635589993285 6341375805445619173123741)
      ·
        refine ⟨2378015927042107189921403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6341375805445619173123741 2378015927042107189921403)
        ·
          refine ⟨3567023890563160784882105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378015927042107189921403 3567023890563160784882105)
          ·
            refine ⟨2675267917922370588661579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3567023890563160784882105 2675267917922370588661579)
            ·
              refine ⟨4012901876883555882992369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675267917922370588661579 4012901876883555882992369)
              ·
                refine ⟨3009676407662666912244277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4012901876883555882992369 3009676407662666912244277)
                ·
                  refine ⟨282157163218375023022901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009676407662666912244277 282157163218375023022901)
                  ·
                    rfl

theorem cell22_2472746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_2472746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472746 prefixEnd_2472746 := by exact prefixLift 2472746
  have htrace : WordTrace (prefixWord ++ tailWord_2472746) baseStart_2472746 baseEnd_2472746 := by
    simpa [prefixWord, tailWord_2472746, baseEnd_2472746] using wordTrace_append hprefix tailTrace_2472746
  have hstable : (prefixWord ++ tailWord_2472746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472746).length < 2 ^ (prefixWord ++ tailWord_2472746).sum := by decide
  have hdescent : baseEnd_2472746 < baseStart_2472746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472757 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 6]
def baseStart_2472757 : Nat := 118140960795 + 2472757 * 2 ^ 59
def prefixEnd_2472757 : Nat := 4983230072969 + 3 ^ 40 * 2472757 * 2
def baseEnd_2472757 : Nat := 282158418393308235681223

theorem tailTrace_2472757 : CollatzResearch.WordTrace tailWord_2472757 prefixEnd_2472757 282158418393308235681223 := by
  unfold tailWord_2472757
  simp only [CollatzResearch.WordTrace]
  refine ⟨90188857102631177118632525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60125904735087451412421683 90188857102631177118632525)
  ·
    refine ⟨33820821413486691419487197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90188857102631177118632525 33820821413486691419487197)
    ·
      refine ⟨12682808030057509282307699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33820821413486691419487197 12682808030057509282307699)
      ·
        refine ⟨19024212045086263923461549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12682808030057509282307699 19024212045086263923461549)
        ·
          refine ⟨7134079516907348971298081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19024212045086263923461549 7134079516907348971298081)
          ·
            refine ⟨5350559637680511728473561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7134079516907348971298081 5350559637680511728473561)
            ·
              refine ⟨4012919728260383796355171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5350559637680511728473561 4012919728260383796355171)
              ·
                refine ⟨6019379592390575694532757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012919728260383796355171 6019379592390575694532757)
                ·
                  refine ⟨282158418393308235681223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6019379592390575694532757 282158418393308235681223)
                  ·
                    rfl

theorem cell22_2472757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_2472757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472757 prefixEnd_2472757 := by exact prefixLift 2472757
  have htrace : WordTrace (prefixWord ++ tailWord_2472757) baseStart_2472757 baseEnd_2472757 := by
    simpa [prefixWord, tailWord_2472757, baseEnd_2472757] using wordTrace_append hprefix tailTrace_2472757
  have hstable : (prefixWord ++ tailWord_2472757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472757).length < 2 ^ (prefixWord ++ tailWord_2472757).sum := by decide
  have hdescent : baseEnd_2472757 < baseStart_2472757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472894 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2472894 : Nat := 118140960795 + 2472894 * 2 ^ 59
def prefixEnd_2472894 : Nat := 4983230072969 + 3 ^ 40 * 2472894 * 2
def baseEnd_2472894 : Nat := 846522153079702016368249

theorem tailTrace_2472894 : CollatzResearch.WordTrace tailWord_2472894 prefixEnd_2472894 846522153079702016368249 := by
  unfold tailWord_2472894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11274231737891856189546217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60129235935423233010913157 11274231737891856189546217)
  ·
    refine ⟨8455673803418892142159663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11274231737891856189546217 8455673803418892142159663)
    ·
      refine ⟨12683510705128338213239495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8455673803418892142159663 12683510705128338213239495)
      ·
        refine ⟨19025266057692507319859243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12683510705128338213239495 19025266057692507319859243)
        ·
          refine ⟨28537899086538760979788865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19025266057692507319859243 28537899086538760979788865)
          ·
            refine ⟨21403424314904070734841649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28537899086538760979788865 21403424314904070734841649)
            ·
              refine ⟨16052568236178053051131237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21403424314904070734841649 16052568236178053051131237)
              ·
                refine ⟨3009856544283384947087107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16052568236178053051131237 3009856544283384947087107)
                ·
                  refine ⟨4514784816425077420630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009856544283384947087107 4514784816425077420630661)
                  ·
                    refine ⟨846522153079702016368249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4514784816425077420630661 846522153079702016368249)
                    ·
                      rfl

theorem cell22_2472894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2472894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472894 prefixEnd_2472894 := by exact prefixLift 2472894
  have htrace : WordTrace (prefixWord ++ tailWord_2472894) baseStart_2472894 baseEnd_2472894 := by
    simpa [prefixWord, tailWord_2472894, baseEnd_2472894] using wordTrace_append hprefix tailTrace_2472894
  have hstable : (prefixWord ++ tailWord_2472894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472894).length < 2 ^ (prefixWord ++ tailWord_2472894).sum := by decide
  have hdescent : baseEnd_2472894 < baseStart_2472894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472907 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_2472907 : Nat := 118140960795 + 2472907 * 2 ^ 59
def prefixEnd_2472907 : Nat := 4983230072969 + 3 ^ 40 * 2472907 * 2
def baseEnd_2472907 : Nat := 846526603245374315793209

theorem tailTrace_2472907 : CollatzResearch.WordTrace tailWord_2472907 prefixEnd_2472907 846526603245374315793209 := by
  unfold tailWord_2472907
  simp only [CollatzResearch.WordTrace]
  refine ⟨90194328052087752736592975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60129552034725168491061983 90194328052087752736592975)
  ·
    refine ⟨135291492078131629104889463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90194328052087752736592975 135291492078131629104889463)
    ·
      refine ⟨202937238117197443657334195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135291492078131629104889463 202937238117197443657334195)
      ·
        refine ⟨304405857175796165486001293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202937238117197443657334195 304405857175796165486001293)
        ·
          refine ⟨114152196440923562057250485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304405857175796165486001293 114152196440923562057250485)
          ·
            refine ⟨10701768416336583942867233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114152196440923562057250485 10701768416336583942867233)
            ·
              refine ⟨8026326312252437957150425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10701768416336583942867233 8026326312252437957150425)
              ·
                refine ⟨6019744734189328467862819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8026326312252437957150425 6019744734189328467862819)
                ·
                  refine ⟨9029617101283992701794229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6019744734189328467862819 9029617101283992701794229)
                  ·
                    refine ⟨846526603245374315793209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9029617101283992701794229 846526603245374315793209)
                    ·
                      rfl

theorem cell22_2472907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_2472907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472907 prefixEnd_2472907 := by exact prefixLift 2472907
  have htrace : WordTrace (prefixWord ++ tailWord_2472907) baseStart_2472907 baseEnd_2472907 := by
    simpa [prefixWord, tailWord_2472907, baseEnd_2472907] using wordTrace_append hprefix tailTrace_2472907
  have hstable : (prefixWord ++ tailWord_2472907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472907).length < 2 ^ (prefixWord ++ tailWord_2472907).sum := by decide
  have hdescent : baseEnd_2472907 < baseStart_2472907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472911 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 1, 4]
def baseStart_2472911 : Nat := 118140960795 + 2472911 * 2 ^ 59
def prefixEnd_2472911 : Nat := 4983230072969 + 3 ^ 40 * 2472911 * 2
def baseEnd_2472911 : Nat := 846527972527119638693197

theorem tailTrace_2472911 : CollatzResearch.WordTrace tailWord_2472911 prefixEnd_2472911 846527972527119638693197 := by
  unfold tailWord_2472911
  simp only [CollatzResearch.WordTrace]
  refine ⟨90194473944073261419738587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60129649296048840946492391 90194473944073261419738587)
  ·
    refine ⟨135291710916109892129607881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90194473944073261419738587 135291710916109892129607881)
    ·
      refine ⟨101468783187082419097205911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135291710916109892129607881 101468783187082419097205911)
      ·
        refine ⟨152203174780623628645808867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101468783187082419097205911 152203174780623628645808867)
        ·
          refine ⟨228304762170935442968713301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152203174780623628645808867 228304762170935442968713301)
          ·
            refine ⟨2675446431690649722289609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 228304762170935442968713301 2675446431690649722289609)
            ·
              refine ⟨2006584823767987291717207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675446431690649722289609 2006584823767987291717207)
              ·
                refine ⟨3009877235651980937575811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006584823767987291717207 3009877235651980937575811)
                ·
                  refine ⟨4514815853477971406363717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009877235651980937575811 4514815853477971406363717)
                  ·
                    refine ⟨846527972527119638693197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4514815853477971406363717 846527972527119638693197)
                    ·
                      rfl

theorem cell22_2472911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_2472911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472911 prefixEnd_2472911 := by exact prefixLift 2472911
  have htrace : WordTrace (prefixWord ++ tailWord_2472911) baseStart_2472911 baseEnd_2472911 := by
    simpa [prefixWord, tailWord_2472911, baseEnd_2472911] using wordTrace_append hprefix tailTrace_2472911
  have hstable : (prefixWord ++ tailWord_2472911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472911).length < 2 ^ (prefixWord ++ tailWord_2472911).sum := by decide
  have hdescent : baseEnd_2472911 < baseStart_2472911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472992 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_2472992 : Nat := 118140960795 + 2472992 * 2 ^ 59
def prefixEnd_2472992 : Nat := 4983230072969 + 3 ^ 40 * 2472992 * 2
def baseEnd_2472992 : Nat := 846555700482462427417949

theorem tailTrace_2472992 : CollatzResearch.WordTrace tailWord_2472992 prefixEnd_2472992 846555700482462427417949 := by
  unfold tailWord_2472992
  simp only [CollatzResearch.WordTrace]
  refine ⟨45098714128389906126718615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60131618837853208168958153 45098714128389906126718615)
  ·
    refine ⟨67648071192584859190077923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45098714128389906126718615 67648071192584859190077923)
    ·
      refine ⟨101472106788877288785116885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67648071192584859190077923 101472106788877288785116885)
      ·
        refine ⟨2378252502864311455901177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 101472106788877288785116885 2378252502864311455901177)
        ·
          refine ⟨1783689377148233591925883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2378252502864311455901177 1783689377148233591925883)
          ·
            refine ⟨2675534065722350387888825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1783689377148233591925883 2675534065722350387888825)
            ·
              refine ⟨2006650549291762790916619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675534065722350387888825 2006650549291762790916619)
              ·
                refine ⟨3009975823937644186374929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2006650549291762790916619 3009975823937644186374929)
                ·
                  refine ⟨2257481867953233139781197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3009975823937644186374929 2257481867953233139781197)
                  ·
                    refine ⟨846555700482462427417949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257481867953233139781197 846555700482462427417949)
                    ·
                      rfl

theorem cell22_2472992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_2472992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472992 prefixEnd_2472992 := by exact prefixLift 2472992
  have htrace : WordTrace (prefixWord ++ tailWord_2472992) baseStart_2472992 baseEnd_2472992 := by
    simpa [prefixWord, tailWord_2472992, baseEnd_2472992] using wordTrace_append hprefix tailTrace_2472992
  have hstable : (prefixWord ++ tailWord_2472992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472992).length < 2 ^ (prefixWord ++ tailWord_2472992).sum := by decide
  have hdescent : baseEnd_2472992 < baseStart_2472992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2472997 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_2472997 : Nat := 118140960795 + 2472997 * 2 ^ 59
def prefixEnd_2472997 : Nat := 4983230072969 + 3 ^ 40 * 2472997 * 2
def baseEnd_2472997 : Nat := 846557412084644081042933

theorem tailTrace_2472997 : CollatzResearch.WordTrace tailWord_2472997 prefixEnd_2472997 846557412084644081042933 := by
  unfold tailWord_2472997
  simp only [CollatzResearch.WordTrace]
  refine ⟨90197610621761698107369245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60131740414507798738246163 90197610621761698107369245)
  ·
    refine ⟨33824103983160636790263467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90197610621761698107369245 33824103983160636790263467)
    ·
      refine ⟨50736155974740955185395201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33824103983160636790263467 50736155974740955185395201)
      ·
        refine ⟨38052116981055716389046401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50736155974740955185395201 38052116981055716389046401)
        ·
          refine ⟨28539087735791787291784801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38052116981055716389046401 28539087735791787291784801)
          ·
            refine ⟨21404315801843840468838601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28539087735791787291784801 21404315801843840468838601)
            ·
              refine ⟨16053236851382880351628951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21404315801843840468838601 16053236851382880351628951)
              ·
                refine ⟨24079855277074320527443427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16053236851382880351628951 24079855277074320527443427)
                ·
                  refine ⟨36119782915611480791165141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24079855277074320527443427 36119782915611480791165141)
                  ·
                    refine ⟨846557412084644081042933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36119782915611480791165141 846557412084644081042933)
                    ·
                      rfl

theorem cell22_2472997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_2472997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2472997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2472997 prefixEnd_2472997 := by exact prefixLift 2472997
  have htrace : WordTrace (prefixWord ++ tailWord_2472997) baseStart_2472997 baseEnd_2472997 := by
    simpa [prefixWord, tailWord_2472997, baseEnd_2472997] using wordTrace_append hprefix tailTrace_2472997
  have hstable : (prefixWord ++ tailWord_2472997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2472997).length < 2 ^ (prefixWord ++ tailWord_2472997).sum := by decide
  have hdescent : baseEnd_2472997 < baseStart_2472997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2472997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473029 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_2473029 : Nat := 118140960795 + 2473029 * 2 ^ 59
def prefixEnd_2473029 : Nat := 4983230072969 + 3 ^ 40 * 2473029 * 2
def baseEnd_2473029 : Nat := 846568366338606664242835

theorem tailTrace_2473029 : CollatzResearch.WordTrace tailWord_2473029 prefixEnd_2473029 846568366338606664242835 := by
  unfold tailWord_2473029
  simp only [CollatzResearch.WordTrace]
  refine ⟨90198777757645767572534141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60132518505097178381689427 90198777757645767572534141)
  ·
    refine ⟨33824541659117162839700303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90198777757645767572534141 33824541659117162839700303)
    ·
      refine ⟨50736812488675744259550455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33824541659117162839700303 50736812488675744259550455)
      ·
        refine ⟨76105218733013616389325683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50736812488675744259550455 76105218733013616389325683)
        ·
          refine ⟨114157828099520424583988525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76105218733013616389325683 114157828099520424583988525)
          ·
            refine ⟨42809185537320159218995697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114157828099520424583988525 42809185537320159218995697)
            ·
              refine ⟨32106889152990119414246773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42809185537320159218995697 32106889152990119414246773)
              ·
                refine ⟨3010020858092823695085635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32106889152990119414246773 3010020858092823695085635)
                ·
                  refine ⟨4515031287139235542628453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010020858092823695085635 4515031287139235542628453)
                  ·
                    refine ⟨846568366338606664242835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515031287139235542628453 846568366338606664242835)
                    ·
                      rfl

theorem cell22_2473029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_2473029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473029 prefixEnd_2473029 := by exact prefixLift 2473029
  have htrace : WordTrace (prefixWord ++ tailWord_2473029) baseStart_2473029 baseEnd_2473029 := by
    simpa [prefixWord, tailWord_2473029, baseEnd_2473029] using wordTrace_append hprefix tailTrace_2473029
  have hstable : (prefixWord ++ tailWord_2473029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473029).length < 2 ^ (prefixWord ++ tailWord_2473029).sum := by decide
  have hdescent : baseEnd_2473029 < baseStart_2473029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473037 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2473037 : Nat := 118140960795 + 2473037 * 2 ^ 59
def prefixEnd_2473037 : Nat := 4983230072969 + 3 ^ 40 * 2473037 * 2
def baseEnd_2473037 : Nat := 846571104902097310042811

theorem tailTrace_2473037 : CollatzResearch.WordTrace tailWord_2473037 prefixEnd_2473037 846571104902097310042811 := by
  unfold tailWord_2473037
  simp only [CollatzResearch.WordTrace]
  refine ⟨90199069541616784938825365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60132713027744523292550243 90199069541616784938825365)
  ·
    refine ⟨4228081384763286794007439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90199069541616784938825365 4228081384763286794007439)
    ·
      refine ⟨6342122077144930191011159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4228081384763286794007439 6342122077144930191011159)
      ·
        refine ⟨9513183115717395286516739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342122077144930191011159 9513183115717395286516739)
        ·
          refine ⟨14269774673576092929775109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513183115717395286516739 14269774673576092929775109)
          ·
            refine ⟨2675582751295517424332833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14269774673576092929775109 2675582751295517424332833)
            ·
              refine ⟨2006687063471638068249625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2675582751295517424332833 2006687063471638068249625)
              ·
                refine ⟨1505015297603728551187219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2006687063471638068249625 1505015297603728551187219)
                ·
                  refine ⟨2257522946405592826780829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505015297603728551187219 2257522946405592826780829)
                  ·
                    refine ⟨846571104902097310042811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257522946405592826780829 846571104902097310042811)
                    ·
                      rfl

theorem cell22_2473037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2473037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473037 prefixEnd_2473037 := by exact prefixLift 2473037
  have htrace : WordTrace (prefixWord ++ tailWord_2473037) baseStart_2473037 baseEnd_2473037 := by
    simpa [prefixWord, tailWord_2473037, baseEnd_2473037] using wordTrace_append hprefix tailTrace_2473037
  have hstable : (prefixWord ++ tailWord_2473037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473037).length < 2 ^ (prefixWord ++ tailWord_2473037).sum := by decide
  have hdescent : baseEnd_2473037 < baseStart_2473037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473059 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 6, 3]
def baseStart_2473059 : Nat := 118140960795 + 2473059 * 2 ^ 59
def prefixEnd_2473059 : Nat := 4983230072969 + 3 ^ 40 * 2473059 * 2
def baseEnd_2473059 : Nat := 846578635951696585992743

theorem tailTrace_2473059 : CollatzResearch.WordTrace tailWord_2473059 prefixEnd_2473059 846578635951696585992743 := by
  unfold tailWord_2473059
  simp only [CollatzResearch.WordTrace]
  refine ⟨90199871947537082696126231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60133247965024721797417487 90199871947537082696126231)
  ·
    refine ⟨135299807921305624044189347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90199871947537082696126231 135299807921305624044189347)
    ·
      refine ⟨202949711881958436066284021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135299807921305624044189347 202949711881958436066284021)
      ·
        refine ⟨19026535488933603381214127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 202949711881958436066284021 19026535488933603381214127)
        ·
          refine ⟨28539803233400405071821191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19026535488933603381214127 28539803233400405071821191)
          ·
            refine ⟨42809704850100607607731787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28539803233400405071821191 42809704850100607607731787)
            ·
              refine ⟨64214557275150911411597681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42809704850100607607731787 64214557275150911411597681)
              ·
                refine ⟨48160917956363183558698261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64214557275150911411597681 48160917956363183558698261)
                ·
                  refine ⟨2257543029204524229313981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48160917956363183558698261 2257543029204524229313981)
                  ·
                    refine ⟨846578635951696585992743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257543029204524229313981 846578635951696585992743)
                    ·
                      rfl

theorem cell22_2473059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3].length) (baseStart_2473059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473059 prefixEnd_2473059 := by exact prefixLift 2473059
  have htrace : WordTrace (prefixWord ++ tailWord_2473059) baseStart_2473059 baseEnd_2473059 := by
    simpa [prefixWord, tailWord_2473059, baseEnd_2473059] using wordTrace_append hprefix tailTrace_2473059
  have hstable : (prefixWord ++ tailWord_2473059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473059).length < 2 ^ (prefixWord ++ tailWord_2473059).sum := by decide
  have hdescent : baseEnd_2473059 < baseStart_2473059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473074 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2473074 : Nat := 118140960795 + 2473074 * 2 ^ 59
def prefixEnd_2473074 : Nat := 4983230072969 + 3 ^ 40 * 2473074 * 2
def baseEnd_2473074 : Nat := 846583770758241546867697

theorem tailTrace_2473074 : CollatzResearch.WordTrace tailWord_2473074 prefixEnd_2473074 846583770758241546867697 := by
  unfold tailWord_2473074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22550104760620685064480569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60133612694988493505281517 22550104760620685064480569)
  ·
    refine ⟨16912578570465513798360427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22550104760620685064480569 16912578570465513798360427)
    ·
      refine ⟨25368867855698270697540641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16912578570465513798360427 25368867855698270697540641)
      ·
        refine ⟨19026650891773703023155481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25368867855698270697540641 19026650891773703023155481)
        ·
          refine ⟨14269988168830277267366611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19026650891773703023155481 14269988168830277267366611)
          ·
            refine ⟨21404982253245415901049917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14269988168830277267366611 21404982253245415901049917)
            ·
              refine ⟨8026868344967030962893719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21404982253245415901049917 8026868344967030962893719)
              ·
                refine ⟨12040302517450546444340579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8026868344967030962893719 12040302517450546444340579)
                ·
                  refine ⟨18060453776175819666510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12040302517450546444340579 18060453776175819666510869)
                  ·
                    refine ⟨846583770758241546867697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18060453776175819666510869 846583770758241546867697)
                    ·
                      rfl

theorem cell22_2473074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2473074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473074 prefixEnd_2473074 := by exact prefixLift 2473074
  have htrace : WordTrace (prefixWord ++ tailWord_2473074) baseStart_2473074 baseEnd_2473074 := by
    simpa [prefixWord, tailWord_2473074, baseEnd_2473074] using wordTrace_append hprefix tailTrace_2473074
  have hstable : (prefixWord ++ tailWord_2473074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473074).length < 2 ^ (prefixWord ++ tailWord_2473074).sum := by decide
  have hdescent : baseEnd_2473074 < baseStart_2473074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473078 : List Nat := [5, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2473078 : Nat := 118140960795 + 2473078 * 2 ^ 59
def prefixEnd_2473078 : Nat := 4983230072969 + 3 ^ 40 * 2473078 * 2
def baseEnd_2473078 : Nat := 282195046679995623255895

theorem tailTrace_2473078 : CollatzResearch.WordTrace tailWord_2473078 prefixEnd_2473078 282195046679995623255895 := by
  unfold tailWord_2473078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637535308404265558816743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60133709956312165960711925 5637535308404265558816743)
  ·
    refine ⟨8456302962606398338225115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5637535308404265558816743 8456302962606398338225115)
    ·
      refine ⟨12684454443909597507337673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8456302962606398338225115 12684454443909597507337673)
      ·
        refine ⟨9513340832932198130503255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12684454443909597507337673 9513340832932198130503255)
        ·
          refine ⟨14270011249398297195754883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513340832932198130503255 14270011249398297195754883)
          ·
            refine ⟨21405016874097445793632325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270011249398297195754883 21405016874097445793632325)
            ·
              refine ⟨4013440663893271086306061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21405016874097445793632325 4013440663893271086306061)
              ·
                refine ⟨1505040248959976657364773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4013440663893271086306061 1505040248959976657364773)
                ·
                  refine ⟨282195046679995623255895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505040248959976657364773 282195046679995623255895)
                  ·
                    rfl

theorem cell22_2473078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2473078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473078 prefixEnd_2473078 := by exact prefixLift 2473078
  have htrace : WordTrace (prefixWord ++ tailWord_2473078) baseStart_2473078 baseEnd_2473078 := by
    simpa [prefixWord, tailWord_2473078, baseEnd_2473078] using wordTrace_append hprefix tailTrace_2473078
  have hstable : (prefixWord ++ tailWord_2473078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473078).length < 2 ^ (prefixWord ++ tailWord_2473078).sum := by decide
  have hdescent : baseEnd_2473078 < baseStart_2473078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473087 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_2473087 : Nat := 118140960795 + 2473087 * 2 ^ 59
def prefixEnd_2473087 : Nat := 4983230072969 + 3 ^ 40 * 2473087 * 2
def baseEnd_2473087 : Nat := 846588220923913846292657

theorem tailTrace_2473087 : CollatzResearch.WordTrace tailWord_2473087 prefixEnd_2473087 846588220923913846292657 := by
  unfold tailWord_2473087
  simp only [CollatzResearch.WordTrace]
  refine ⟨90200893191435643478145515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60133928794290428985430343 90200893191435643478145515)
  ·
    refine ⟨135301339787153465217218273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90200893191435643478145515 135301339787153465217218273)
    ·
      refine ⟨101476004840365098912913705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135301339787153465217218273 101476004840365098912913705)
      ·
        refine ⟨76107003630273824184685279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101476004840365098912913705 76107003630273824184685279)
        ·
          refine ⟨114160505445410736277027919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76107003630273824184685279 114160505445410736277027919)
          ·
            refine ⟨171240758168116104415541879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114160505445410736277027919 171240758168116104415541879)
            ·
              refine ⟨256861137252174156623312819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171240758168116104415541879 256861137252174156623312819)
              ·
                refine ⟨385291705878261234934969229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256861137252174156623312819 385291705878261234934969229)
                ·
                  refine ⟨144484389704347963100613461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385291705878261234934969229 144484389704347963100613461)
                  ·
                    refine ⟨846588220923913846292657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144484389704347963100613461 846588220923913846292657)
                    ·
                      rfl

theorem cell22_2473087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_2473087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473087 prefixEnd_2473087 := by exact prefixLift 2473087
  have htrace : WordTrace (prefixWord ++ tailWord_2473087) baseStart_2473087 baseEnd_2473087 := by
    simpa [prefixWord, tailWord_2473087, baseEnd_2473087] using wordTrace_append hprefix tailTrace_2473087
  have hstable : (prefixWord ++ tailWord_2473087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473087).length < 2 ^ (prefixWord ++ tailWord_2473087).sum := by decide
  have hdescent : baseEnd_2473087 < baseStart_2473087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473089 : List Nat := [1, 2, 4, 2, 2, 2, 9]
def baseStart_2473089 : Nat := 118140960795 + 2473089 * 2 ^ 59
def prefixEnd_2473089 : Nat := 4983230072969 + 3 ^ 40 * 2473089 * 2
def baseEnd_2473089 : Nat := 31355144650547648434913

theorem tailTrace_2473089 : CollatzResearch.WordTrace tailWord_2473089 prefixEnd_2473089 31355144650547648434913 := by
  unfold tailWord_2473089
  simp only [CollatzResearch.WordTrace]
  refine ⟨90200966137428397819718321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60133977424952265213145547 90200966137428397819718321)
  ·
    refine ⟨67650724603071298364788741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90200966137428397819718321 67650724603071298364788741)
    ·
      refine ⟨12684510863075868443397889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67650724603071298364788741 12684510863075868443397889)
      ·
        refine ⟨9513383147306901332548417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12684510863075868443397889 9513383147306901332548417)
        ·
          refine ⟨7135037360480175999411313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9513383147306901332548417 7135037360480175999411313)
          ·
            refine ⟨5351278020360131999558485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7135037360480175999411313 5351278020360131999558485)
            ·
              refine ⟨31355144650547648434913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5351278020360131999558485 31355144650547648434913)
              ·
                rfl

theorem cell22_2473089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 9].length) (baseStart_2473089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473089 prefixEnd_2473089 := by exact prefixLift 2473089
  have htrace : WordTrace (prefixWord ++ tailWord_2473089) baseStart_2473089 baseEnd_2473089 := by
    simpa [prefixWord, tailWord_2473089, baseEnd_2473089] using wordTrace_append hprefix tailTrace_2473089
  have hstable : (prefixWord ++ tailWord_2473089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473089).length < 2 ^ (prefixWord ++ tailWord_2473089).sum := by decide
  have hdescent : baseEnd_2473089 < baseStart_2473089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473121 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_2473121 : Nat := 118140960795 + 2473121 * 2 ^ 59
def prefixEnd_2473121 : Nat := 4983230072969 + 3 ^ 40 * 2473121 * 2
def baseEnd_2473121 : Nat := 846599859818749090942553

theorem tailTrace_2473121 : CollatzResearch.WordTrace tailWord_2473121 prefixEnd_2473121 846599859818749090942553 := by
  unfold tailWord_2473121
  simp only [CollatzResearch.WordTrace]
  refine ⟨90202133273312467284883217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60134755515541644856588811 90202133273312467284883217)
  ·
    refine ⟨67651599954984350463662413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90202133273312467284883217 67651599954984350463662413)
    ·
      refine ⟨25369349983119131423873405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67651599954984350463662413 25369349983119131423873405)
      ·
        refine ⟨9513506243669674283952527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25369349983119131423873405 9513506243669674283952527)
        ·
          refine ⟨14270259365504511425928791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513506243669674283952527 14270259365504511425928791)
          ·
            refine ⟨21405389048256767138893187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270259365504511425928791 21405389048256767138893187)
            ·
              refine ⟨32108083572385150708339781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21405389048256767138893187 32108083572385150708339781)
              ·
                refine ⟨6020265669822215757813709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32108083572385150708339781 6020265669822215757813709)
                ·
                  refine ⟨2257599626183330909180141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6020265669822215757813709 2257599626183330909180141)
                  ·
                    refine ⟨846599859818749090942553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257599626183330909180141 846599859818749090942553)
                    ·
                      rfl

theorem cell22_2473121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_2473121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473121 prefixEnd_2473121 := by exact prefixLift 2473121
  have htrace : WordTrace (prefixWord ++ tailWord_2473121) baseStart_2473121 baseEnd_2473121 := by
    simpa [prefixWord, tailWord_2473121, baseEnd_2473121] using wordTrace_append hprefix tailTrace_2473121
  have hstable : (prefixWord ++ tailWord_2473121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473121).length < 2 ^ (prefixWord ++ tailWord_2473121).sum := by decide
  have hdescent : baseEnd_2473121 < baseStart_2473121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473149 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2473149 : Nat := 118140960795 + 2473149 * 2 ^ 59
def prefixEnd_2473149 : Nat := 4983230072969 + 3 ^ 40 * 2473149 * 2
def baseEnd_2473149 : Nat := 846609444790966351242467

theorem tailTrace_2473149 : CollatzResearch.WordTrace tailWord_2473149 prefixEnd_2473149 846609444790966351242467 := by
  unfold tailWord_2473149
  simp only [CollatzResearch.WordTrace]
  refine ⟨90203154517211028066902501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60135436344807352044601667 90203154517211028066902501)
  ·
    refine ⟨16913091471977067762544219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90203154517211028066902501 16913091471977067762544219)
    ·
      refine ⟨25369637207965601643816329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16913091471977067762544219 25369637207965601643816329)
      ·
        refine ⟨19027227905974201232862247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25369637207965601643816329 19027227905974201232862247)
        ·
          refine ⟨28540841858961301849293371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19027227905974201232862247 28540841858961301849293371)
          ·
            refine ⟨42811262788441952773940057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28540841858961301849293371 42811262788441952773940057)
            ·
              refine ⟨32108447091331464580455043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42811262788441952773940057 32108447091331464580455043)
              ·
                refine ⟨48162670636997196870682565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32108447091331464580455043 48162670636997196870682565)
                ·
                  refine ⟨9030500744436974413252981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48162670636997196870682565 9030500744436974413252981)
                  ·
                    refine ⟨846609444790966351242467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9030500744436974413252981 846609444790966351242467)
                    ·
                      rfl

theorem cell22_2473149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2473149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473149 prefixEnd_2473149 := by exact prefixLift 2473149
  have htrace : WordTrace (prefixWord ++ tailWord_2473149) baseStart_2473149 baseEnd_2473149 := by
    simpa [prefixWord, tailWord_2473149, baseEnd_2473149] using wordTrace_append hprefix tailTrace_2473149
  have hstable : (prefixWord ++ tailWord_2473149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473149).length < 2 ^ (prefixWord ++ tailWord_2473149).sum := by decide
  have hdescent : baseEnd_2473149 < baseStart_2473149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473228 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_2473228 : Nat := 118140960795 + 2473228 * 2 ^ 59
def prefixEnd_2473228 : Nat := 4983230072969 + 3 ^ 40 * 2473228 * 2
def baseEnd_2473228 : Nat := 846636488105436478517225

theorem tailTrace_2473228 : CollatzResearch.WordTrace tailWord_2473228 prefixEnd_2473228 846636488105436478517225 := by
  unfold tailWord_2473228
  simp only [CollatzResearch.WordTrace]
  refine ⟨45103017941962412279514169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60137357255949883039352225 45103017941962412279514169)
  ·
    refine ⟨33827263456471809209635627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45103017941962412279514169 33827263456471809209635627)
    ·
      refine ⟨50740895184707713814453441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33827263456471809209635627 50740895184707713814453441)
      ·
        refine ⟨38055671388530785360840081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50740895184707713814453441 38055671388530785360840081)
        ·
          refine ⟨28541753541398089020630061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38055671388530785360840081 28541753541398089020630061)
          ·
            refine ⟨10703157578024283382736273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28541753541398089020630061 10703157578024283382736273)
            ·
              refine ⟨8027368183518212537052205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10703157578024283382736273 8027368183518212537052205)
              ·
                refine ⟨3010263068819329701394577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8027368183518212537052205 3010263068819329701394577)
                ·
                  refine ⟨2257697301614497276045933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3010263068819329701394577 2257697301614497276045933)
                  ·
                    refine ⟨846636488105436478517225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257697301614497276045933 846636488105436478517225)
                    ·
                      rfl

theorem cell22_2473228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_2473228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473228 prefixEnd_2473228 := by exact prefixLift 2473228
  have htrace : WordTrace (prefixWord ++ tailWord_2473228) baseStart_2473228 baseEnd_2473228 := by
    simpa [prefixWord, tailWord_2473228, baseEnd_2473228] using wordTrace_append hprefix tailTrace_2473228
  have hstable : (prefixWord ++ tailWord_2473228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473228).length < 2 ^ (prefixWord ++ tailWord_2473228).sum := by decide
  have hdescent : baseEnd_2473228 < baseStart_2473228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473361 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2473361 : Nat := 118140960795 + 2473361 * 2 ^ 59
def prefixEnd_2473361 : Nat := 4983230072969 + 3 ^ 40 * 2473361 * 2
def baseEnd_2473361 : Nat := 846682016723468464941817

theorem tailTrace_2473361 : CollatzResearch.WordTrace tailWord_2473361 prefixEnd_2473361 846682016723468464941817 := by
  unfold tailWord_2473361
  simp only [CollatzResearch.WordTrace]
  refine ⟨90210886792442988273619937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60140591194961992182413291 90210886792442988273619937)
  ·
    refine ⟨67658165094332241205214953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90210886792442988273619937 67658165094332241205214953)
    ·
      refine ⟨50743623820749180903911215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67658165094332241205214953 50743623820749180903911215)
      ·
        refine ⟨76115435731123771355866823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50743623820749180903911215 76115435731123771355866823)
        ·
          refine ⟨114173153596685657033800235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76115435731123771355866823 114173153596685657033800235)
          ·
            refine ⟨171259730395028485550700353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114173153596685657033800235 171259730395028485550700353)
            ·
              refine ⟨128444797796271364163025265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171259730395028485550700353 128444797796271364163025265)
              ·
                refine ⟨96333598347203523122268949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128444797796271364163025265 96333598347203523122268949)
                ·
                  refine ⟨4515637422525165146356357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96333598347203523122268949 4515637422525165146356357)
                  ·
                    refine ⟨846682016723468464941817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515637422525165146356357 846682016723468464941817)
                    ·
                      rfl

theorem cell22_2473361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2473361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473361 prefixEnd_2473361 := by exact prefixLift 2473361
  have htrace : WordTrace (prefixWord ++ tailWord_2473361) baseStart_2473361 baseEnd_2473361 := by
    simpa [prefixWord, tailWord_2473361, baseEnd_2473361] using wordTrace_append hprefix tailTrace_2473361
  have hstable : (prefixWord ++ tailWord_2473361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473361).length < 2 ^ (prefixWord ++ tailWord_2473361).sum := by decide
  have hdescent : baseEnd_2473361 < baseStart_2473361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473408 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_2473408 : Nat := 118140960795 + 2473408 * 2 ^ 59
def prefixEnd_2473408 : Nat := 4983230072969 + 3 ^ 40 * 2473408 * 2
def baseEnd_2473408 : Nat := 846698105783976009016673

theorem tailTrace_2473408 : CollatzResearch.WordTrace tailWord_2473408 prefixEnd_2473408 846698105783976009016673 := by
  unfold tailWord_2473408
  simp only [CollatzResearch.WordTrace]
  refine ⟨45106300511636357650290439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60141734015515143533720585 45106300511636357650290439)
  ·
    refine ⟨67659450767454536475435659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45106300511636357650290439 67659450767454536475435659)
    ·
      refine ⟨101489176151181804713153489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67659450767454536475435659 101489176151181804713153489)
      ·
        refine ⟨76116882113386353534865117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101489176151181804713153489 76116882113386353534865117)
        ·
          refine ⟨28543830792519882575574419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76116882113386353534865117 28543830792519882575574419)
          ·
            refine ⟨42815746188779823863361629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28543830792519882575574419 42815746188779823863361629)
            ·
              refine ⟨16055904820792433948760611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42815746188779823863361629 16055904820792433948760611)
              ·
                refine ⟨24083857231188650923140917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16055904820792433948760611 24083857231188650923140917)
                ·
                  refine ⟨2257861615423936024044461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24083857231188650923140917 2257861615423936024044461)
                  ·
                    refine ⟨846698105783976009016673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257861615423936024044461 846698105783976009016673)
                    ·
                      rfl

theorem cell22_2473408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_2473408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473408 prefixEnd_2473408 := by exact prefixLift 2473408
  have htrace : WordTrace (prefixWord ++ tailWord_2473408) baseStart_2473408 baseEnd_2473408 := by
    simpa [prefixWord, tailWord_2473408, baseEnd_2473408] using wordTrace_append hprefix tailTrace_2473408
  have hstable : (prefixWord ++ tailWord_2473408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473408).length < 2 ^ (prefixWord ++ tailWord_2473408).sum := by decide
  have hdescent : baseEnd_2473408 < baseStart_2473408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473412 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2473412 : Nat := 118140960795 + 2473412 * 2 ^ 59
def prefixEnd_2473412 : Nat := 4983230072969 + 3 ^ 40 * 2473412 * 2
def baseEnd_2473412 : Nat := 846699475065721331916661

theorem tailTrace_2473412 : CollatzResearch.WordTrace tailWord_2473412 prefixEnd_2473412 846699475065721331916661 := by
  unfold tailWord_2473412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45106373457629111991863245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60141831276838815989150993 45106373457629111991863245)
  ·
    refine ⟨16914890046610916996948717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45106373457629111991863245 16914890046610916996948717)
    ·
      refine ⟨6343083767479093873855769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16914890046610916996948717 6343083767479093873855769)
      ·
        refine ⟨4757312825609320405391827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6343083767479093873855769 4757312825609320405391827)
        ·
          refine ⟨7135969238413980608087741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757312825609320405391827 7135969238413980608087741)
          ·
            refine ⟨2675988464405242728032903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7135969238413980608087741 2675988464405242728032903)
            ·
              refine ⟨4013982696607864092049355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2675988464405242728032903 4013982696607864092049355)
              ·
                refine ⟨6020974044911796138074033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4013982696607864092049355 6020974044911796138074033)
                ·
                  refine ⟨4515730533683847103555525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6020974044911796138074033 4515730533683847103555525)
                  ·
                    refine ⟨846699475065721331916661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515730533683847103555525 846699475065721331916661)
                    ·
                      rfl

theorem cell22_2473412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2473412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473412 prefixEnd_2473412 := by exact prefixLift 2473412
  have htrace : WordTrace (prefixWord ++ tailWord_2473412) baseStart_2473412 baseEnd_2473412 := by
    simpa [prefixWord, tailWord_2473412, baseEnd_2473412] using wordTrace_append hprefix tailTrace_2473412
  have hstable : (prefixWord ++ tailWord_2473412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473412).length < 2 ^ (prefixWord ++ tailWord_2473412).sum := by decide
  have hdescent : baseEnd_2473412 < baseStart_2473412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473451 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_2473451 : Nat := 118140960795 + 2473451 * 2 ^ 59
def prefixEnd_2473451 : Nat := 4983230072969 + 3 ^ 40 * 2473451 * 2
def baseEnd_2473451 : Nat := 846712825562738230191541

theorem tailTrace_2473451 : CollatzResearch.WordTrace tailWord_2473451 prefixEnd_2473451 846712825562738230191541 := by
  unfold tailWord_2473451
  simp only [CollatzResearch.WordTrace]
  refine ⟨90214169362116933644396207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60142779574744622429597471 90214169362116933644396207)
  ·
    refine ⟨135321254043175400466594311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90214169362116933644396207 135321254043175400466594311)
    ·
      refine ⟨202981881064763100699891467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135321254043175400466594311 202981881064763100699891467)
      ·
        refine ⟨304472821597144651049837201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202981881064763100699891467 304472821597144651049837201)
        ·
          refine ⟨228354616197858488287377901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304472821597144651049837201 228354616197858488287377901)
          ·
            refine ⟨85632981074196933107766713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228354616197858488287377901 85632981074196933107766713)
            ·
              refine ⟨64224735805647699830825035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85632981074196933107766713 64224735805647699830825035)
              ·
                refine ⟨96337103708471549746237553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64224735805647699830825035 96337103708471549746237553)
                ·
                  refine ⟨72252827781353662309678165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96337103708471549746237553 72252827781353662309678165)
                  ·
                    refine ⟨846712825562738230191541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72252827781353662309678165 846712825562738230191541)
                    ·
                      rfl

theorem cell22_2473451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_2473451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473451 prefixEnd_2473451 := by exact prefixLift 2473451
  have htrace : WordTrace (prefixWord ++ tailWord_2473451) baseStart_2473451 baseEnd_2473451 := by
    simpa [prefixWord, tailWord_2473451, baseEnd_2473451] using wordTrace_append hprefix tailTrace_2473451
  have hstable : (prefixWord ++ tailWord_2473451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473451).length < 2 ^ (prefixWord ++ tailWord_2473451).sum := by decide
  have hdescent : baseEnd_2473451 < baseStart_2473451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473468 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_2473468 : Nat := 118140960795 + 2473468 * 2 ^ 59
def prefixEnd_2473468 : Nat := 4983230072969 + 3 ^ 40 * 2473468 * 2
def baseEnd_2473468 : Nat := 846718645010155852516489

theorem tailTrace_2473468 : CollatzResearch.WordTrace tailWord_2473468 prefixEnd_2473468 846718645010155852516489 := by
  unfold tailWord_2473468
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107394701527672773882529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60143192935370230365176705 45107394701527672773882529)
  ·
    refine ⟨33830546026145754580411897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45107394701527672773882529 33830546026145754580411897)
    ·
      refine ⟨25372909519609315935308923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33830546026145754580411897 25372909519609315935308923)
      ·
        refine ⟨38059364279413973902963385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25372909519609315935308923 38059364279413973902963385)
        ·
          refine ⟨28544523209560480427222539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38059364279413973902963385 28544523209560480427222539)
          ·
            refine ⟨42816784814340720640833809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28544523209560480427222539 42816784814340720640833809)
            ·
              refine ⟨32112588610755540480625357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42816784814340720640833809 32112588610755540480625357)
              ·
                refine ⟨12042220729033327680234509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32112588610755540480625357 12042220729033327680234509)
                ·
                  refine ⟨4515832773387497880087941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12042220729033327680234509 4515832773387497880087941)
                  ·
                    refine ⟨846718645010155852516489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515832773387497880087941 846718645010155852516489)
                    ·
                      rfl

theorem cell22_2473468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_2473468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473468 prefixEnd_2473468 := by exact prefixLift 2473468
  have htrace : WordTrace (prefixWord ++ tailWord_2473468) baseStart_2473468 baseEnd_2473468 := by
    simpa [prefixWord, tailWord_2473468, baseEnd_2473468] using wordTrace_append hprefix tailTrace_2473468
  have hstable : (prefixWord ++ tailWord_2473468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473468).length < 2 ^ (prefixWord ++ tailWord_2473468).sum := by decide
  have hdescent : baseEnd_2473468 < baseStart_2473468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473476 : List Nat := [2, 3, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_2473476 : Nat := 118140960795 + 2473476 * 2 ^ 59
def prefixEnd_2473476 : Nat := 4983230072969 + 3 ^ 40 * 2473476 * 2
def baseEnd_2473476 : Nat := 846721383573646498316465

theorem tailTrace_2473476 : CollatzResearch.WordTrace tailWord_2473476 prefixEnd_2473476 846721383573646498316465 := by
  unfold tailWord_2473476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45107540593513181457028141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60143387458017575276037521 45107540593513181457028141)
  ·
    refine ⟨16915327722567443046385553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45107540593513181457028141 16915327722567443046385553)
    ·
      refine ⟨12686495791925582284789165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16915327722567443046385553 12686495791925582284789165)
      ·
        refine ⟨4757435921972093356795937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12686495791925582284789165 4757435921972093356795937)
        ·
          refine ⟨3568076941479070017596953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757435921972093356795937 3568076941479070017596953)
          ·
            refine ⟨2676057706109302513197715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3568076941479070017596953 2676057706109302513197715)
            ·
              refine ⟨4014086559163953769796573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676057706109302513197715 4014086559163953769796573)
              ·
                refine ⟨1505282459686482663673715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4014086559163953769796573 1505282459686482663673715)
                ·
                  refine ⟨2257923689529723995510573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505282459686482663673715 2257923689529723995510573)
                  ·
                    refine ⟨846721383573646498316465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2257923689529723995510573 846721383573646498316465)
                    ·
                      rfl

theorem cell22_2473476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_2473476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473476 prefixEnd_2473476 := by exact prefixLift 2473476
  have htrace : WordTrace (prefixWord ++ tailWord_2473476) baseStart_2473476 baseEnd_2473476 := by
    simpa [prefixWord, tailWord_2473476, baseEnd_2473476] using wordTrace_append hprefix tailTrace_2473476
  have hstable : (prefixWord ++ tailWord_2473476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473476).length < 2 ^ (prefixWord ++ tailWord_2473476).sum := by decide
  have hdescent : baseEnd_2473476 < baseStart_2473476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473528 : List Nat := [2, 1, 2, 1, 4, 2, 2, 8]
def baseStart_2473528 : Nat := 118140960795 + 2473528 * 2 ^ 59
def prefixEnd_2473528 : Nat := 4983230072969 + 3 ^ 40 * 2473528 * 2
def baseEnd_2473528 : Nat := 94082131581815077335145

theorem tailTrace_2473528 : CollatzResearch.WordTrace tailWord_2473528 prefixEnd_2473528 94082131581815077335145 := by
  unfold tailWord_2473528
  simp only [CollatzResearch.WordTrace]
  refine ⟨45108488891418987897474619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60144651855225317196632825 45108488891418987897474619)
  ·
    refine ⟨67662733337128481846211929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45108488891418987897474619 67662733337128481846211929)
    ·
      refine ⟨50747050002846361384658947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67662733337128481846211929 50747050002846361384658947)
      ·
        refine ⟨76120575004269542076988421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50747050002846361384658947 76120575004269542076988421)
        ·
          refine ⟨14272607813300539139435329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76120575004269542076988421 14272607813300539139435329)
          ·
            refine ⟨10704455859975404354576497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14272607813300539139435329 10704455859975404354576497)
            ·
              refine ⟨8028341894981553265932373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10704455859975404354576497 8028341894981553265932373)
              ·
                refine ⟨94082131581815077335145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8028341894981553265932373 94082131581815077335145)
                ·
                  rfl

theorem cell22_2473528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_2473528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473528 prefixEnd_2473528 := by exact prefixLift 2473528
  have htrace : WordTrace (prefixWord ++ tailWord_2473528) baseStart_2473528 baseEnd_2473528 := by
    simpa [prefixWord, tailWord_2473528, baseEnd_2473528] using wordTrace_append hprefix tailTrace_2473528
  have hstable : (prefixWord ++ tailWord_2473528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473528).length < 2 ^ (prefixWord ++ tailWord_2473528).sum := by decide
  have hdescent : baseEnd_2473528 < baseStart_2473528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473530 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_2473530 : Nat := 118140960795 + 2473530 * 2 ^ 59
def prefixEnd_2473530 : Nat := 4983230072969 + 3 ^ 40 * 2473530 * 2
def baseEnd_2473530 : Nat := 846739868877208357466299

theorem tailTrace_2473530 : CollatzResearch.WordTrace tailWord_2473530 prefixEnd_2473530 846739868877208357466299 := by
  unfold tailWord_2473530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22554262682207682534130511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60144700485887153424348029 22554262682207682534130511)
  ·
    refine ⟨33831394023311523801195767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22554262682207682534130511 33831394023311523801195767)
    ·
      refine ⟨50747091034967285701793651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33831394023311523801195767 50747091034967285701793651)
      ·
        refine ⟨76120636552450928552690477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50747091034967285701793651 76120636552450928552690477)
        ·
          refine ⟨28545238707169098207258929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76120636552450928552690477 28545238707169098207258929)
          ·
            refine ⟨21408929030376823655444197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28545238707169098207258929 21408929030376823655444197)
            ·
              refine ⟨4014174193195654435395787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21408929030376823655444197 4014174193195654435395787)
              ·
                refine ⟨6021261289793481653093681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014174193195654435395787 6021261289793481653093681)
                ·
                  refine ⟨4515945967345111239820261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021261289793481653093681 4515945967345111239820261)
                  ·
                    refine ⟨846739868877208357466299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4515945967345111239820261 846739868877208357466299)
                    ·
                      rfl

theorem cell22_2473530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_2473530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473530 prefixEnd_2473530 := by exact prefixLift 2473530
  have htrace : WordTrace (prefixWord ++ tailWord_2473530) baseStart_2473530 baseEnd_2473530 := by
    simpa [prefixWord, tailWord_2473530, baseEnd_2473530] using wordTrace_append hprefix tailTrace_2473530
  have hstable : (prefixWord ++ tailWord_2473530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473530).length < 2 ^ (prefixWord ++ tailWord_2473530).sum := by decide
  have hdescent : baseEnd_2473530 < baseStart_2473530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473560 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_2473560 : Nat := 118140960795 + 2473560 * 2 ^ 59
def prefixEnd_2473560 : Nat := 4983230072969 + 3 ^ 40 * 2473560 * 2
def baseEnd_2473560 : Nat := 846750138490298279216207

theorem tailTrace_2473560 : CollatzResearch.WordTrace tailWord_2473560 prefixEnd_2473560 846750138490298279216207 := by
  unfold tailWord_2473560
  simp only [CollatzResearch.WordTrace]
  refine ⟨45109072459361022630057067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60145429945814696840076089 45109072459361022630057067)
  ·
    refine ⟨67663608689041533945085601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45109072459361022630057067 67663608689041533945085601)
    ·
      refine ⟨50747706516781150458814201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67663608689041533945085601 50747706516781150458814201)
      ·
        refine ⟨38060779887585862844110651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50747706516781150458814201 38060779887585862844110651)
        ·
          refine ⟨57091169831378794266165977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38060779887585862844110651 57091169831378794266165977)
          ·
            refine ⟨42818377373534095699624483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57091169831378794266165977 42818377373534095699624483)
            ·
              refine ⟨64227566060301143549436725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42818377373534095699624483 64227566060301143549436725)
              ·
                refine ⟨6021334318153232207759693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64227566060301143549436725 6021334318153232207759693)
                ·
                  refine ⟨2258000369307462077909885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6021334318153232207759693 2258000369307462077909885)
                  ·
                    refine ⟨846750138490298279216207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258000369307462077909885 846750138490298279216207)
                    ·
                      rfl

theorem cell22_2473560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_2473560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473560 prefixEnd_2473560 := by exact prefixLift 2473560
  have htrace : WordTrace (prefixWord ++ tailWord_2473560) baseStart_2473560 baseEnd_2473560 := by
    simpa [prefixWord, tailWord_2473560, baseEnd_2473560] using wordTrace_append hprefix tailTrace_2473560
  have hstable : (prefixWord ++ tailWord_2473560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473560).length < 2 ^ (prefixWord ++ tailWord_2473560).sum := by decide
  have hdescent : baseEnd_2473560 < baseStart_2473560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473607 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 5]
def baseStart_2473607 : Nat := 118140960795 + 2473607 * 2 ^ 59
def prefixEnd_2473607 : Nat := 4983230072969 + 3 ^ 40 * 2473607 * 2
def baseEnd_2473607 : Nat := 282255409183601941097021

theorem tailTrace_2473607 : CollatzResearch.WordTrace tailWord_2473607 prefixEnd_2473607 282255409183601941097021 := by
  unfold tailWord_2473607
  simp only [CollatzResearch.WordTrace]
  refine ⟨90219859149551772287075075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60146572766367848191383383 90219859149551772287075075)
  ·
    refine ⟨135329788724327658430612613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90219859149551772287075075 135329788724327658430612613)
    ·
      refine ⟨25374335385811435955739865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135329788724327658430612613 25374335385811435955739865)
      ·
        refine ⟨19030751539358576966804899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25374335385811435955739865 19030751539358576966804899)
        ·
          refine ⟨28546127309037865450207349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19030751539358576966804899 28546127309037865450207349)
          ·
            refine ⟨2676199435222299885956939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28546127309037865450207349 2676199435222299885956939)
            ·
              refine ⟨4014299152833449828935409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676199435222299885956939 4014299152833449828935409)
              ·
                refine ⟨3010724364625087371701557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014299152833449828935409 3010724364625087371701557)
                ·
                  refine ⟨282255409183601941097021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3010724364625087371701557 282255409183601941097021)
                  ·
                    rfl

theorem cell22_2473607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 5].length) (baseStart_2473607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473607 prefixEnd_2473607 := by exact prefixLift 2473607
  have htrace : WordTrace (prefixWord ++ tailWord_2473607) baseStart_2473607 baseEnd_2473607 := by
    simpa [prefixWord, tailWord_2473607, baseEnd_2473607] using wordTrace_append hprefix tailTrace_2473607
  have hstable : (prefixWord ++ tailWord_2473607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473607).length < 2 ^ (prefixWord ++ tailWord_2473607).sum := by decide
  have hdescent : baseEnd_2473607 < baseStart_2473607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473650 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_2473650 : Nat := 118140960795 + 2473650 * 2 ^ 59
def prefixEnd_2473650 : Nat := 4983230072969 + 3 ^ 40 * 2473650 * 2
def baseEnd_2473650 : Nat := 846780947329568044465931

theorem tailTrace_2473650 : CollatzResearch.WordTrace tailWord_2473650 prefixEnd_2473650 846780947329568044465931 := by
  unfold tailWord_2473650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22555356872098997657722601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60147618325597327087260269 22555356872098997657722601)
  ·
    refine ⟨16916517654074248243291951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22555356872098997657722601 16916517654074248243291951)
    ·
      refine ⟨25374776481111372364937927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16916517654074248243291951 25374776481111372364937927)
      ·
        refine ⟨38062164721667058547406891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25374776481111372364937927 38062164721667058547406891)
        ·
          refine ⟨57093247082500587821110337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38062164721667058547406891 57093247082500587821110337)
          ·
            refine ⟨42819935311875440865832753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57093247082500587821110337 42819935311875440865832753)
            ·
              refine ⟨32114951483906580649374565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42819935311875440865832753 32114951483906580649374565)
              ·
                refine ⟨6021553403232483871757731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32114951483906580649374565 6021553403232483871757731)
                ·
                  refine ⟨9032330104848725807636597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6021553403232483871757731 9032330104848725807636597)
                  ·
                    refine ⟨846780947329568044465931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9032330104848725807636597 846780947329568044465931)
                    ·
                      rfl

theorem cell22_2473650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_2473650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473650 prefixEnd_2473650 := by exact prefixLift 2473650
  have htrace : WordTrace (prefixWord ++ tailWord_2473650) baseStart_2473650 baseEnd_2473650 := by
    simpa [prefixWord, tailWord_2473650, baseEnd_2473650] using wordTrace_append hprefix tailTrace_2473650
  have hstable : (prefixWord ++ tailWord_2473650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473650).length < 2 ^ (prefixWord ++ tailWord_2473650).sum := by decide
  have hdescent : baseEnd_2473650 < baseStart_2473650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473699 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 2, 4]
def baseStart_2473699 : Nat := 118140960795 + 2473699 * 2 ^ 59
def prefixEnd_2473699 : Nat := 4983230072969 + 3 ^ 40 * 2473699 * 2
def baseEnd_2473699 : Nat := 846797721030948249990781

theorem tailTrace_2473699 : CollatzResearch.WordTrace tailWord_2473699 prefixEnd_2473699 846797721030948249990781 := by
  unfold tailWord_2473699
  simp only [CollatzResearch.WordTrace]
  refine ⟨90223214665218471999424151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60148809776812314666282767 90223214665218471999424151)
  ·
    refine ⟨135334821997827707999136227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90223214665218471999424151 135334821997827707999136227)
    ·
      refine ⟨203002232996741561998704341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135334821997827707999136227 203002232996741561998704341)
      ·
        refine ⟨4757864835861130359344633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 203002232996741561998704341 4757864835861130359344633)
        ·
          refine ⟨3568398626895847769508475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757864835861130359344633 3568398626895847769508475)
          ·
            refine ⟨5352597940343771654262713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568398626895847769508475 5352597940343771654262713)
            ·
              refine ⟨4014448455257828740697035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352597940343771654262713 4014448455257828740697035)
              ·
                refine ⟨6021672682886743111045553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4014448455257828740697035 6021672682886743111045553)
                ·
                  refine ⟨4516254512165057333284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021672682886743111045553 4516254512165057333284165)
                  ·
                    refine ⟨846797721030948249990781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516254512165057333284165 846797721030948249990781)
                    ·
                      rfl

theorem cell22_2473699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_2473699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473699 prefixEnd_2473699 := by exact prefixLift 2473699
  have htrace : WordTrace (prefixWord ++ tailWord_2473699) baseStart_2473699 baseEnd_2473699 := by
    simpa [prefixWord, tailWord_2473699, baseEnd_2473699] using wordTrace_append hprefix tailTrace_2473699
  have hstable : (prefixWord ++ tailWord_2473699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473699).length < 2 ^ (prefixWord ++ tailWord_2473699).sum := by decide
  have hdescent : baseEnd_2473699 < baseStart_2473699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473716 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2473716 : Nat := 118140960795 + 2473716 * 2 ^ 59
def prefixEnd_2473716 : Nat := 4983230072969 + 3 ^ 40 * 2473716 * 2
def baseEnd_2473716 : Nat := 846803540478365872315729

theorem tailTrace_2473716 : CollatzResearch.WordTrace tailWord_2473716 prefixEnd_2473716 846803540478365872315729 := by
  unfold tailWord_2473716
  simp only [CollatzResearch.WordTrace]
  refine ⟨45111917353078441951396501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60149223137437922601862001 45111917353078441951396501)
  ·
    refine ⟨2114621125925551966471711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45111917353078441951396501 2114621125925551966471711)
    ·
      refine ⟨3171931688888327949707567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114621125925551966471711 3171931688888327949707567)
      ·
        refine ⟨4757897533332491924561351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171931688888327949707567 4757897533332491924561351)
        ·
          refine ⟨7136846299998737886842027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757897533332491924561351 7136846299998737886842027)
          ·
            refine ⟨10705269449998106830263041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7136846299998737886842027 10705269449998106830263041)
            ·
              refine ⟨8028952087498580122697281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10705269449998106830263041 8028952087498580122697281)
              ·
                refine ⟨6021714065623935092022961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8028952087498580122697281 6021714065623935092022961)
                ·
                  refine ⟨4516285549217951319017221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021714065623935092022961 4516285549217951319017221)
                  ·
                    refine ⟨846803540478365872315729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516285549217951319017221 846803540478365872315729)
                    ·
                      rfl

theorem cell22_2473716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2473716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473716 prefixEnd_2473716 := by exact prefixLift 2473716
  have htrace : WordTrace (prefixWord ++ tailWord_2473716) baseStart_2473716 baseEnd_2473716 := by
    simpa [prefixWord, tailWord_2473716, baseEnd_2473716] using wordTrace_append hprefix tailTrace_2473716
  have hstable : (prefixWord ++ tailWord_2473716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473716).length < 2 ^ (prefixWord ++ tailWord_2473716).sum := by decide
  have hdescent : baseEnd_2473716 < baseStart_2473716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473740 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2473740 : Nat := 118140960795 + 2473740 * 2 ^ 59
def prefixEnd_2473740 : Nat := 4983230072969 + 3 ^ 40 * 2473740 * 2
def baseEnd_2473740 : Nat := 846811756168837809715655

theorem tailTrace_2473740 : CollatzResearch.WordTrace tailWord_2473740 prefixEnd_2473740 846811756168837809715655 := by
  unfold tailWord_2473740
  simp only [CollatzResearch.WordTrace]
  refine ⟨45112355029034968000833337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60149806705379957334444449 45112355029034968000833337)
  ·
    refine ⟨33834266271776226000625003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45112355029034968000833337 33834266271776226000625003)
    ·
      refine ⟨50751399407664339000937505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33834266271776226000625003 50751399407664339000937505)
      ·
        refine ⟨38063549555748254250703129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50751399407664339000937505 38063549555748254250703129)
        ·
          refine ⟨28547662166811190688027347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38063549555748254250703129 28547662166811190688027347)
          ·
            refine ⟨42821493250216786032041021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28547662166811190688027347 42821493250216786032041021)
            ·
              refine ⟨16058059968831294762015383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42821493250216786032041021 16058059968831294762015383)
              ·
                refine ⟨24087089953246942143023075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16058059968831294762015383 24087089953246942143023075)
                ·
                  refine ⟨36130634929870413214534613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24087089953246942143023075 36130634929870413214534613)
                  ·
                    refine ⟨846811756168837809715655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36130634929870413214534613 846811756168837809715655)
                    ·
                      rfl

theorem cell22_2473740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2473740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473740 prefixEnd_2473740 := by exact prefixLift 2473740
  have htrace : WordTrace (prefixWord ++ tailWord_2473740) baseStart_2473740 baseEnd_2473740 := by
    simpa [prefixWord, tailWord_2473740, baseEnd_2473740] using wordTrace_append hprefix tailTrace_2473740
  have hstable : (prefixWord ++ tailWord_2473740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473740).length < 2 ^ (prefixWord ++ tailWord_2473740).sum := by decide
  have hdescent : baseEnd_2473740 < baseStart_2473740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473742 : List Nat := [4, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_2473742 : Nat := 118140960795 + 2473742 * 2 ^ 59
def prefixEnd_2473742 : Nat := 4983230072969 + 3 ^ 40 * 2473742 * 2
def baseEnd_2473742 : Nat := 282270813603236823721883

theorem tailTrace_2473742 : CollatzResearch.WordTrace tailWord_2473742 prefixEnd_2473742 282270813603236823721883 := by
  unfold tailWord_2473742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278097875507836292904935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60149855336041793562159653 11278097875507836292904935)
  ·
    refine ⟨16917146813261754439357403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11278097875507836292904935 16917146813261754439357403)
    ·
      refine ⟨25375720219892631659036105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16917146813261754439357403 25375720219892631659036105)
      ·
        refine ⟨19031790164919473744277079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25375720219892631659036105 19031790164919473744277079)
        ·
          refine ⟨28547685247379210616415619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19031790164919473744277079 28547685247379210616415619)
          ·
            refine ⟨42821527871068815924623429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28547685247379210616415619 42821527871068815924623429)
            ·
              refine ⟨8029036475825402985866893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42821527871068815924623429 8029036475825402985866893)
              ·
                refine ⟨3010888678434526119700085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8029036475825402985866893 3010888678434526119700085)
                ·
                  refine ⟨282270813603236823721883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3010888678434526119700085 282270813603236823721883)
                  ·
                    rfl

theorem cell22_2473742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_2473742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473742 prefixEnd_2473742 := by exact prefixLift 2473742
  have htrace : WordTrace (prefixWord ++ tailWord_2473742) baseStart_2473742 baseEnd_2473742 := by
    simpa [prefixWord, tailWord_2473742, baseEnd_2473742] using wordTrace_append hprefix tailTrace_2473742
  have hstable : (prefixWord ++ tailWord_2473742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473742).length < 2 ^ (prefixWord ++ tailWord_2473742).sum := by decide
  have hdescent : baseEnd_2473742 < baseStart_2473742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473746 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2473746 : Nat := 118140960795 + 2473746 * 2 ^ 59
def prefixEnd_2473746 : Nat := 4983230072969 + 3 ^ 40 * 2473746 * 2
def baseEnd_2473746 : Nat := 846813810091455794065637

theorem tailTrace_2473746 : CollatzResearch.WordTrace tailWord_2473746 prefixEnd_2473746 846813810091455794065637 := by
  unfold tailWord_2473746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22556232224012049756596273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60149952597365466017590061 22556232224012049756596273)
  ·
    refine ⟨16917174168009037317447205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22556232224012049756596273 16917174168009037317447205)
    ·
      refine ⟨3171970156501694497021351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16917174168009037317447205 3171970156501694497021351)
      ·
        refine ⟨4757955234752541745532027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171970156501694497021351 4757955234752541745532027)
        ·
          refine ⟨7136932852128812618298041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4757955234752541745532027 7136932852128812618298041)
          ·
            refine ⟨5352699639096609463723531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7136932852128812618298041 5352699639096609463723531)
            ·
              refine ⟨8029049458644914195585297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5352699639096609463723531 8029049458644914195585297)
              ·
                refine ⟨6021787093983685646688973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8029049458644914195585297 6021787093983685646688973)
                ·
                  refine ⟨2258170160243882117508365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6021787093983685646688973 2258170160243882117508365)
                  ·
                    refine ⟨846813810091455794065637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258170160243882117508365 846813810091455794065637)
                    ·
                      rfl

theorem cell22_2473746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2473746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473746 prefixEnd_2473746 := by exact prefixLift 2473746
  have htrace : WordTrace (prefixWord ++ tailWord_2473746) baseStart_2473746 baseEnd_2473746 := by
    simpa [prefixWord, tailWord_2473746, baseEnd_2473746] using wordTrace_append hprefix tailTrace_2473746
  have hstable : (prefixWord ++ tailWord_2473746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473746).length < 2 ^ (prefixWord ++ tailWord_2473746).sum := by decide
  have hdescent : baseEnd_2473746 < baseStart_2473746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473748 : List Nat := [2, 4, 4, 1, 1, 1, 3, 6]
def baseStart_2473748 : Nat := 118140960795 + 2473748 * 2 ^ 59
def prefixEnd_2473748 : Nat := 4983230072969 + 3 ^ 40 * 2473748 * 2
def baseEnd_2473748 : Nat := 94090499414703161723959

theorem tailTrace_2473748 : CollatzResearch.WordTrace tailWord_2473748 prefixEnd_2473748 94090499414703161723959 := by
  unfold tailWord_2473748
  simp only [CollatzResearch.WordTrace]
  refine ⟨45112500921020476683978949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60150001228027302245305265 45112500921020476683978949)
  ·
    refine ⟨8458593922691339378246053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45112500921020476683978949 8458593922691339378246053)
    ·
      refine ⟨1585986360504626133421135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8458593922691339378246053 1585986360504626133421135)
      ·
        refine ⟨2378979540756939200131703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585986360504626133421135 2378979540756939200131703)
        ·
          refine ⟨3568469311135408800197555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378979540756939200131703 3568469311135408800197555)
          ·
            refine ⟨5352703966703113200296333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568469311135408800197555 5352703966703113200296333)
            ·
              refine ⟨2007263987513667450111125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5352703966703113200296333 2007263987513667450111125)
              ·
                refine ⟨94090499414703161723959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2007263987513667450111125 94090499414703161723959)
                ·
                  rfl

theorem cell22_2473748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_2473748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473748 prefixEnd_2473748 := by exact prefixLift 2473748
  have htrace : WordTrace (prefixWord ++ tailWord_2473748) baseStart_2473748 baseEnd_2473748 := by
    simpa [prefixWord, tailWord_2473748, baseEnd_2473748] using wordTrace_append hprefix tailTrace_2473748
  have hstable : (prefixWord ++ tailWord_2473748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473748).length < 2 ^ (prefixWord ++ tailWord_2473748).sum := by decide
  have hdescent : baseEnd_2473748 < baseStart_2473748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473817 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_2473817 : Nat := 118140960795 + 2473817 * 2 ^ 59
def prefixEnd_2473817 : Nat := 4983230072969 + 3 ^ 40 * 2473817 * 2
def baseEnd_2473817 : Nat := 846838114842435275540419

theorem tailTrace_2473817 : CollatzResearch.WordTrace tailWord_2473817 prefixEnd_2473817 846838114842435275540419 := by
  unfold tailWord_2473817
  simp only [CollatzResearch.WordTrace]
  refine ⟨90227518478790978152219705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60151678985860652101479803 90227518478790978152219705)
  ·
    refine ⟨67670638859093233614164779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90227518478790978152219705 67670638859093233614164779)
    ·
      refine ⟨101505958288639850421247169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67670638859093233614164779 101505958288639850421247169)
      ·
        refine ⟨76129468716479887815935377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101505958288639850421247169 76129468716479887815935377)
        ·
          refine ⟨57097101537359915861951533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76129468716479887815935377 57097101537359915861951533)
          ·
            refine ⟨21411413076509968448231825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57097101537359915861951533 21411413076509968448231825)
            ·
              refine ⟨16058559807382476336173869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21411413076509968448231825 16058559807382476336173869)
              ·
                refine ⟨6021959927768428626065201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16058559807382476336173869 6021959927768428626065201)
                ·
                  refine ⟨4516469945826321469548901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6021959927768428626065201 4516469945826321469548901)
                  ·
                    refine ⟨846838114842435275540419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516469945826321469548901 846838114842435275540419)
                    ·
                      rfl

theorem cell22_2473817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_2473817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473817 prefixEnd_2473817 := by exact prefixLift 2473817
  have htrace : WordTrace (prefixWord ++ tailWord_2473817) baseStart_2473817 baseEnd_2473817 := by
    simpa [prefixWord, tailWord_2473817, baseEnd_2473817] using wordTrace_append hprefix tailTrace_2473817
  have hstable : (prefixWord ++ tailWord_2473817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473817).length < 2 ^ (prefixWord ++ tailWord_2473817).sum := by decide
  have hdescent : baseEnd_2473817 < baseStart_2473817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473838 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_2473838 : Nat := 118140960795 + 2473838 * 2 ^ 59
def prefixEnd_2473838 : Nat := 4983230072969 + 3 ^ 40 * 2473838 * 2
def baseEnd_2473838 : Nat := 282281767857199406921785

theorem tailTrace_2473838 : CollatzResearch.WordTrace tailWord_2473838 prefixEnd_2473838 282281767857199406921785 := by
  unfold tailWord_2473838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278535551464362342341771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60152189607809932492489445 11278535551464362342341771)
  ·
    refine ⟨16917803327196543513512657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11278535551464362342341771 16917803327196543513512657)
    ·
      refine ⟨12688352495397407635134493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16917803327196543513512657 12688352495397407635134493)
      ·
        refine ⟨4758132185774027863175435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12688352495397407635134493 4758132185774027863175435)
        ·
          refine ⟨7137198278661041794763153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4758132185774027863175435 7137198278661041794763153)
          ·
            refine ⟨5352898708995781346072365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7137198278661041794763153 5352898708995781346072365)
            ·
              refine ⟨2007337015873418004777137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5352898708995781346072365 2007337015873418004777137)
              ·
                refine ⟨1505502761905063503582853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007337015873418004777137 1505502761905063503582853)
                ·
                  refine ⟨282281767857199406921785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505502761905063503582853 282281767857199406921785)
                  ·
                    rfl

theorem cell22_2473838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_2473838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473838 prefixEnd_2473838 := by exact prefixLift 2473838
  have htrace : WordTrace (prefixWord ++ tailWord_2473838) baseStart_2473838 baseEnd_2473838 := by
    simpa [prefixWord, tailWord_2473838, baseEnd_2473838] using wordTrace_append hprefix tailTrace_2473838
  have hstable : (prefixWord ++ tailWord_2473838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473838).length < 2 ^ (prefixWord ++ tailWord_2473838).sum := by decide
  have hdescent : baseEnd_2473838 < baseStart_2473838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473907 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_2473907 : Nat := 118140960795 + 2473907 * 2 ^ 59
def prefixEnd_2473907 : Nat := 4983230072969 + 3 ^ 40 * 2473907 * 2
def baseEnd_2473907 : Nat := 846868923681705040790143

theorem tailTrace_2473907 : CollatzResearch.WordTrace tailWord_2473907 prefixEnd_2473907 846868923681705040790143 := by
  unfold tailWord_2473907
  simp only [CollatzResearch.WordTrace]
  refine ⟨90230801048464923522995975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60153867365643282348663983 90230801048464923522995975)
  ·
    refine ⟨135346201572697385284493963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90230801048464923522995975 135346201572697385284493963)
    ·
      refine ⟨203019302359046077926740945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135346201572697385284493963 203019302359046077926740945)
      ·
        refine ⟨152264476769284558445055709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203019302359046077926740945 152264476769284558445055709)
        ·
          refine ⟨57099178788481709416895891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152264476769284558445055709 57099178788481709416895891)
          ·
            refine ⟨85648768182722564125343837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57099178788481709416895891 85648768182722564125343837)
            ·
              refine ⟨32118288068520961547003939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85648768182722564125343837 32118288068520961547003939)
              ·
                refine ⟨48177432102781442320505909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32118288068520961547003939 48177432102781442320505909)
                ·
                  refine ⟨4516634259635760217547429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48177432102781442320505909 4516634259635760217547429)
                  ·
                    refine ⟨846868923681705040790143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516634259635760217547429 846868923681705040790143)
                    ·
                      rfl

theorem cell22_2473907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_2473907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473907 prefixEnd_2473907 := by exact prefixLift 2473907
  have htrace : WordTrace (prefixWord ++ tailWord_2473907) baseStart_2473907 baseEnd_2473907 := by
    simpa [prefixWord, tailWord_2473907, baseEnd_2473907] using wordTrace_append hprefix tailTrace_2473907
  have hstable : (prefixWord ++ tailWord_2473907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473907).length < 2 ^ (prefixWord ++ tailWord_2473907).sum := by decide
  have hdescent : baseEnd_2473907 < baseStart_2473907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473909 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2473909 : Nat := 118140960795 + 2473909 * 2 ^ 59
def prefixEnd_2473909 : Nat := 4983230072969 + 3 ^ 40 * 2473909 * 2
def baseEnd_2473909 : Nat := 846869608322577702240137

theorem tailTrace_2473909 : CollatzResearch.WordTrace tailWord_2473909 prefixEnd_2473909 846869608322577702240137 := by
  unfold tailWord_2473909
  simp only [CollatzResearch.WordTrace]
  refine ⟨90230873994457677864568781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60153915996305118576379187 90230873994457677864568781)
  ·
    refine ⟨33836577747921629199213293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90230873994457677864568781 33836577747921629199213293)
    ·
      refine ⟨12688716655470610949704985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33836577747921629199213293 12688716655470610949704985)
      ·
        refine ⟨9516537491602958212278739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12688716655470610949704985 9516537491602958212278739)
        ·
          refine ⟨14274806237404437318418109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9516537491602958212278739 14274806237404437318418109)
          ·
            refine ⟨5353052339026663994406791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14274806237404437318418109 5353052339026663994406791)
            ·
              refine ⟨8029578508539995991610187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5353052339026663994406791 8029578508539995991610187)
              ·
                refine ⟨12044367762809993987415281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8029578508539995991610187 12044367762809993987415281)
                ·
                  refine ⟨9033275822107495490561461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12044367762809993987415281 9033275822107495490561461)
                  ·
                    refine ⟨846869608322577702240137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9033275822107495490561461 846869608322577702240137)
                    ·
                      rfl

theorem cell22_2473909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2473909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473909 prefixEnd_2473909 := by exact prefixLift 2473909
  have htrace : WordTrace (prefixWord ++ tailWord_2473909) baseStart_2473909 baseEnd_2473909 := by
    simpa [prefixWord, tailWord_2473909, baseEnd_2473909] using wordTrace_append hprefix tailTrace_2473909
  have hstable : (prefixWord ++ tailWord_2473909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473909).length < 2 ^ (prefixWord ++ tailWord_2473909).sum := by decide
  have hdescent : baseEnd_2473909 < baseStart_2473909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473937 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2473937 : Nat := 118140960795 + 2473937 * 2 ^ 59
def prefixEnd_2473937 : Nat := 4983230072969 + 3 ^ 40 * 2473937 * 2
def baseEnd_2473937 : Nat := 846879193294794962540051

theorem tailTrace_2473937 : CollatzResearch.WordTrace tailWord_2473937 prefixEnd_2473937 846879193294794962540051 := by
  unfold tailWord_2473937
  simp only [CollatzResearch.WordTrace]
  refine ⟨90231895238356238646588065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60154596825570825764392043 90231895238356238646588065)
  ·
    refine ⟨67673921428767178984941049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90231895238356238646588065 67673921428767178984941049)
    ·
      refine ⟨50755441071575384238705787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67673921428767178984941049 50755441071575384238705787)
      ·
        refine ⟨76133161607363076358058681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50755441071575384238705787 76133161607363076358058681)
        ·
          refine ⟨57099871205522307268544011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76133161607363076358058681 57099871205522307268544011)
          ·
            refine ⟨85649806808283460902816017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57099871205522307268544011 85649806808283460902816017)
            ·
              refine ⟨64237355106212595677112013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85649806808283460902816017 64237355106212595677112013)
              ·
                refine ⟨24089008164829723378917005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64237355106212595677112013 24089008164829723378917005)
                ·
                  refine ⟨9033378061811146267093877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24089008164829723378917005 9033378061811146267093877)
                  ·
                    refine ⟨846879193294794962540051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9033378061811146267093877 846879193294794962540051)
                    ·
                      rfl

theorem cell22_2473937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2473937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473937 prefixEnd_2473937 := by exact prefixLift 2473937
  have htrace : WordTrace (prefixWord ++ tailWord_2473937) baseStart_2473937 baseEnd_2473937 := by
    simpa [prefixWord, tailWord_2473937, baseEnd_2473937] using wordTrace_append hprefix tailTrace_2473937
  have hstable : (prefixWord ++ tailWord_2473937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473937).length < 2 ^ (prefixWord ++ tailWord_2473937).sum := by decide
  have hdescent : baseEnd_2473937 < baseStart_2473937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473941 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2473941 : Nat := 118140960795 + 2473941 * 2 ^ 59
def prefixEnd_2473941 : Nat := 4983230072969 + 3 ^ 40 * 2473941 * 2
def baseEnd_2473941 : Nat := 846880562576540285440039

theorem tailTrace_2473941 : CollatzResearch.WordTrace tailWord_2473941 prefixEnd_2473941 846880562576540285440039 := by
  unfold tailWord_2473941
  simp only [CollatzResearch.WordTrace]
  refine ⟨90232041130341747329733677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60154694086894498219822451 90232041130341747329733677)
  ·
    refine ⟨33837015423878155248650129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90232041130341747329733677 33837015423878155248650129)
    ·
      refine ⟨25377761567908616436487597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33837015423878155248650129 25377761567908616436487597)
      ·
        refine ⟨9516660587965731163682849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25377761567908616436487597 9516660587965731163682849)
        ·
          refine ⟨7137495440974298372762137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9516660587965731163682849 7137495440974298372762137)
          ·
            refine ⟨5353121580730723779571603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7137495440974298372762137 5353121580730723779571603)
            ·
              refine ⟨8029682371096085669357405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5353121580730723779571603 8029682371096085669357405)
              ·
                refine ⟨3011130889161032126009027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8029682371096085669357405 3011130889161032126009027)
                ·
                  refine ⟨4516696333741548189013541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011130889161032126009027 4516696333741548189013541)
                  ·
                    refine ⟨846880562576540285440039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516696333741548189013541 846880562576540285440039)
                    ·
                      rfl

theorem cell22_2473941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2473941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473941 prefixEnd_2473941 := by exact prefixLift 2473941
  have htrace : WordTrace (prefixWord ++ tailWord_2473941) baseStart_2473941 baseEnd_2473941 := by
    simpa [prefixWord, tailWord_2473941, baseEnd_2473941] using wordTrace_append hprefix tailTrace_2473941
  have hstable : (prefixWord ++ tailWord_2473941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473941).length < 2 ^ (prefixWord ++ tailWord_2473941).sum := by decide
  have hdescent : baseEnd_2473941 < baseStart_2473941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2473967 : List Nat := [1, 1, 2, 1, 4, 2, 2, 9]
def baseStart_2473967 : Nat := 118140960795 + 2473967 * 2 ^ 59
def prefixEnd_2473967 : Nat := 4983230072969 + 3 ^ 40 * 2473967 * 2
def baseEnd_2473967 : Nat := 94098829211987209365551

theorem tailTrace_2473967 : CollatzResearch.WordTrace tailWord_2473967 prefixEnd_2473967 94098829211987209365551 := by
  unfold tailWord_2473967
  simp only [CollatzResearch.WordTrace]
  refine ⟨90232989428247553770180155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60155326285498369180120103 90232989428247553770180155)
  ·
    refine ⟨135349484142371330655270233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90232989428247553770180155 135349484142371330655270233)
    ·
      refine ⟨101512113106778497991452675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135349484142371330655270233 101512113106778497991452675)
      ·
        refine ⟨152268169660167746987179013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101512113106778497991452675 152268169660167746987179013)
        ·
          refine ⟨28550281811281452560096065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152268169660167746987179013 28550281811281452560096065)
          ·
            refine ⟨21412711358461089420072049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28550281811281452560096065 21412711358461089420072049)
            ·
              refine ⟨16059533518845817065054037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21412711358461089420072049 16059533518845817065054037)
              ·
                refine ⟨94098829211987209365551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16059533518845817065054037 94098829211987209365551)
                ·
                  rfl

theorem cell22_2473967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 9].length) (baseStart_2473967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2473967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2473967 prefixEnd_2473967 := by exact prefixLift 2473967
  have htrace : WordTrace (prefixWord ++ tailWord_2473967) baseStart_2473967 baseEnd_2473967 := by
    simpa [prefixWord, tailWord_2473967, baseEnd_2473967] using wordTrace_append hprefix tailTrace_2473967
  have hstable : (prefixWord ++ tailWord_2473967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2473967).length < 2 ^ (prefixWord ++ tailWord_2473967).sum := by decide
  have hdescent : baseEnd_2473967 < baseStart_2473967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2473967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474061 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2474061 : Nat := 118140960795 + 2474061 * 2 ^ 59
def prefixEnd_2474061 : Nat := 4983230072969 + 3 ^ 40 * 2474061 * 2
def baseEnd_2474061 : Nat := 846921641028899972439671

theorem tailTrace_2474061 : CollatzResearch.WordTrace tailWord_2474061 prefixEnd_2474061 846921641028899972439671 := by
  unfold tailWord_2474061
  simp only [CollatzResearch.WordTrace]
  refine ⟨90236417889907007824102037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60157611926604671882734691 90236417889907007824102037)
  ·
    refine ⟨4229832088589390991754783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90236417889907007824102037 4229832088589390991754783)
    ·
      refine ⟨6344748132884086487632175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4229832088589390991754783 6344748132884086487632175)
      ·
        refine ⟨9517122199326129731448263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6344748132884086487632175 9517122199326129731448263)
        ·
          refine ⟨14275683298989194597172395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9517122199326129731448263 14275683298989194597172395)
          ·
            refine ⟨21413524948483791895758593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14275683298989194597172395 21413524948483791895758593)
            ·
              refine ⟨16060143711362843921818945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21413524948483791895758593 16060143711362843921818945)
              ·
                refine ⟨12045107783522132941364209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16060143711362843921818945 12045107783522132941364209)
                ·
                  refine ⟨9033830837641599706023157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12045107783522132941364209 9033830837641599706023157)
                  ·
                    refine ⟨846921641028899972439671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9033830837641599706023157 846921641028899972439671)
                    ·
                      rfl

theorem cell22_2474061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2474061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474061 prefixEnd_2474061 := by exact prefixLift 2474061
  have htrace : WordTrace (prefixWord ++ tailWord_2474061) baseStart_2474061 baseEnd_2474061 := by
    simpa [prefixWord, tailWord_2474061, baseEnd_2474061] using wordTrace_append hprefix tailTrace_2474061
  have hstable : (prefixWord ++ tailWord_2474061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474061).length < 2 ^ (prefixWord ++ tailWord_2474061).sum := by decide
  have hdescent : baseEnd_2474061 < baseStart_2474061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474074 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_2474074 : Nat := 118140960795 + 2474074 * 2 ^ 59
def prefixEnd_2474074 : Nat := 4983230072969 + 3 ^ 40 * 2474074 * 2
def baseEnd_2474074 : Nat := 282308697064857423954877

theorem tailTrace_2474074 : CollatzResearch.WordTrace tailWord_2474074 prefixEnd_2474074 282308697064857423954877 := by
  unfold tailWord_2474074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559223009714977761081319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60157928025906607362883517 22559223009714977761081319)
  ·
    refine ⟨33838834514572466641621979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22559223009714977761081319 33838834514572466641621979)
    ·
      refine ⟨50758251771858699962432969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33838834514572466641621979 50758251771858699962432969)
      ·
        refine ⟨38068688828894024971824727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50758251771858699962432969 38068688828894024971824727)
        ·
          refine ⟨57103033243341037457737091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38068688828894024971824727 57103033243341037457737091)
          ·
            refine ⟨85654549865011556186605637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57103033243341037457737091 85654549865011556186605637)
            ·
              refine ⟨16060228099689666784988557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85654549865011556186605637 16060228099689666784988557)
              ·
                refine ⟨6022585537383625044370709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16060228099689666784988557 6022585537383625044370709)
                ·
                  refine ⟨282308697064857423954877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6022585537383625044370709 282308697064857423954877)
                  ·
                    rfl

theorem cell22_2474074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_2474074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474074 prefixEnd_2474074 := by exact prefixLift 2474074
  have htrace : WordTrace (prefixWord ++ tailWord_2474074) baseStart_2474074 baseEnd_2474074 := by
    simpa [prefixWord, tailWord_2474074, baseEnd_2474074] using wordTrace_append hprefix tailTrace_2474074
  have hstable : (prefixWord ++ tailWord_2474074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474074).length < 2 ^ (prefixWord ++ tailWord_2474074).sum := by decide
  have hdescent : baseEnd_2474074 < baseStart_2474074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474076 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2474076 : Nat := 118140960795 + 2474076 * 2 ^ 59
def prefixEnd_2474076 : Nat := 4983230072969 + 3 ^ 40 * 2474076 * 2
def baseEnd_2474076 : Nat := 846926775835444933314625

theorem tailTrace_2474076 : CollatzResearch.WordTrace tailWord_2474076 prefixEnd_2474076 846926775835444933314625 := by
  unfold tailWord_2474076
  simp only [CollatzResearch.WordTrace]
  refine ⟨45118482492426332692949041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60157976656568443590598721 45118482492426332692949041)
  ·
    refine ⟨33838861869319749519711781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45118482492426332692949041 33838861869319749519711781)
    ·
      refine ⟨6344786600497453034945959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33838861869319749519711781 6344786600497453034945959)
      ·
        refine ⟨9517179900746179552418939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6344786600497453034945959 9517179900746179552418939)
        ·
          refine ⟨14275769851119269328628409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9517179900746179552418939 14275769851119269328628409)
          ·
            refine ⟨10706827388339451996471307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14275769851119269328628409 10706827388339451996471307)
            ·
              refine ⟨16060241082509177994706961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10706827388339451996471307 16060241082509177994706961)
              ·
                refine ⟨12045180811881883496030221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16060241082509177994706961 12045180811881883496030221)
                ·
                  refine ⟨4516942804455706311011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12045180811881883496030221 4516942804455706311011333)
                  ·
                    refine ⟨846926775835444933314625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4516942804455706311011333 846926775835444933314625)
                    ·
                      rfl

theorem cell22_2474076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2474076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474076 prefixEnd_2474076 := by exact prefixLift 2474076
  have htrace : WordTrace (prefixWord ++ tailWord_2474076) baseStart_2474076 baseEnd_2474076 := by
    simpa [prefixWord, tailWord_2474076, baseEnd_2474076] using wordTrace_append hprefix tailTrace_2474076
  have hstable : (prefixWord ++ tailWord_2474076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474076).length < 2 ^ (prefixWord ++ tailWord_2474076).sum := by decide
  have hdescent : baseEnd_2474076 < baseStart_2474076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474108 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_2474108 : Nat := 118140960795 + 2474108 * 2 ^ 59
def prefixEnd_2474108 : Nat := 4983230072969 + 3 ^ 40 * 2474108 * 2
def baseEnd_2474108 : Nat := 282312576696469172171509

theorem tailTrace_2474108 : CollatzResearch.WordTrace tailWord_2474108 prefixEnd_2474108 282312576696469172171509 := by
  unfold tailWord_2474108
  simp only [CollatzResearch.WordTrace]
  refine ⟨45119066060368367425531489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60158754747157823234041985 45119066060368367425531489)
  ·
    refine ⟨33839299545276275569148617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45119066060368367425531489 33839299545276275569148617)
    ·
      refine ⟨25379474658957206676861463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33839299545276275569148617 25379474658957206676861463)
      ·
        refine ⟨38069211988435810015292195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25379474658957206676861463 38069211988435810015292195)
        ·
          refine ⟨57103817982653715022938293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38069211988435810015292195 57103817982653715022938293)
          ·
            refine ⟨5353482935873785783400465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57103817982653715022938293 5353482935873785783400465)
            ·
              refine ⟨4015112201905339337550349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5353482935873785783400465 4015112201905339337550349)
              ·
                refine ⟨1505667075714502251581381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4015112201905339337550349 1505667075714502251581381)
                ·
                  refine ⟨282312576696469172171509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505667075714502251581381 282312576696469172171509)
                  ·
                    rfl

theorem cell22_2474108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_2474108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474108 prefixEnd_2474108 := by exact prefixLift 2474108
  have htrace : WordTrace (prefixWord ++ tailWord_2474108) baseStart_2474108 baseEnd_2474108 := by
    simpa [prefixWord, tailWord_2474108, baseEnd_2474108] using wordTrace_append hprefix tailTrace_2474108
  have hstable : (prefixWord ++ tailWord_2474108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474108).length < 2 ^ (prefixWord ++ tailWord_2474108).sum := by decide
  have hdescent : baseEnd_2474108 < baseStart_2474108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474140 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2474140 : Nat := 118140960795 + 2474140 * 2 ^ 59
def prefixEnd_2474140 : Nat := 4983230072969 + 3 ^ 40 * 2474140 * 2
def baseEnd_2474140 : Nat := 846948684343370099714429

theorem tailTrace_2474140 : CollatzResearch.WordTrace tailWord_2474140 prefixEnd_2474140 846948684343370099714429 := by
  unfold tailWord_2474140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45119649628310402158113937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60159532837747202877485249 45119649628310402158113937)
  ·
    refine ⟨33839737221232801618585453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45119649628310402158113937 33839737221232801618585453)
    ·
      refine ⟨12689901457962300606969545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33839737221232801618585453 12689901457962300606969545)
      ·
        refine ⟨9517426093471725455227159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12689901457962300606969545 9517426093471725455227159)
        ·
          refine ⟨14276139140207588182840739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9517426093471725455227159 14276139140207588182840739)
          ·
            refine ⟨21414208710311382274261109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14276139140207588182840739 21414208710311382274261109)
            ·
              refine ⟨2007582066591692088211979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21414208710311382274261109 2007582066591692088211979)
              ·
                refine ⟨3011373099887538132317969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007582066591692088211979 3011373099887538132317969)
                ·
                  refine ⟨2258529824915653599238477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3011373099887538132317969 2258529824915653599238477)
                  ·
                    refine ⟨846948684343370099714429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258529824915653599238477 846948684343370099714429)
                    ·
                      rfl

theorem cell22_2474140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2474140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474140 prefixEnd_2474140 := by exact prefixLift 2474140
  have htrace : WordTrace (prefixWord ++ tailWord_2474140) baseStart_2474140 baseEnd_2474140 := by
    simpa [prefixWord, tailWord_2474140, baseEnd_2474140] using wordTrace_append hprefix tailTrace_2474140
  have hstable : (prefixWord ++ tailWord_2474140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474140).length < 2 ^ (prefixWord ++ tailWord_2474140).sum := by decide
  have hdescent : baseEnd_2474140 < baseStart_2474140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474241 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2474241 : Nat := 118140960795 + 2474241 * 2 ^ 59
def prefixEnd_2474241 : Nat := 4983230072969 + 3 ^ 40 * 2474241 * 2
def baseEnd_2474241 : Nat := 846983258707439502939119

theorem tailTrace_2474241 : CollatzResearch.WordTrace tailWord_2474241 prefixEnd_2474241 846983258707439502939119 := by
  unfold tailWord_2474241
  simp only [CollatzResearch.WordTrace]
  refine ⟨90242983029254898565654577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60161988686169932377103051 90242983029254898565654577)
  ·
    refine ⟨67682237271941173924240933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90242983029254898565654577 67682237271941173924240933)
    ·
      refine ⟨12690419488488970110795175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67682237271941173924240933 12690419488488970110795175)
      ·
        refine ⟨19035629232733455166192763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12690419488488970110795175 19035629232733455166192763)
        ·
          refine ⟨28553443849100182749289145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19035629232733455166192763 28553443849100182749289145)
          ·
            refine ⟨21415082886825137061966859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28553443849100182749289145 21415082886825137061966859)
            ·
              refine ⟨32122624330237705592950289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21415082886825137061966859 32122624330237705592950289)
              ·
                refine ⟨24091968247678279194712717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32122624330237705592950289 24091968247678279194712717)
                ·
                  refine ⟨9034488092879354698017269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24091968247678279194712717 9034488092879354698017269)
                  ·
                    refine ⟨846983258707439502939119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9034488092879354698017269 846983258707439502939119)
                    ·
                      rfl

theorem cell22_2474241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2474241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474241 prefixEnd_2474241 := by exact prefixLift 2474241
  have htrace : WordTrace (prefixWord ++ tailWord_2474241) baseStart_2474241 baseEnd_2474241 := by
    simpa [prefixWord, tailWord_2474241, baseEnd_2474241] using wordTrace_append hprefix tailTrace_2474241
  have hstable : (prefixWord ++ tailWord_2474241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474241).length < 2 ^ (prefixWord ++ tailWord_2474241).sum := by decide
  have hdescent : baseEnd_2474241 < baseStart_2474241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474243 : List Nat := [1, 1, 1, 3, 2, 3, 3, 4, 4]
def baseStart_2474243 : Nat := 118140960795 + 2474243 * 2 ^ 59
def prefixEnd_2474243 : Nat := 4983230072969 + 3 ^ 40 * 2474243 * 2
def baseEnd_2474243 : Nat := 282327981116104054796371

theorem tailTrace_2474243 : CollatzResearch.WordTrace tailWord_2474243 prefixEnd_2474243 282327981116104054796371 := by
  unfold tailWord_2474243
  simp only [CollatzResearch.WordTrace]
  refine ⟨90243055975247652907227383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60162037316831768604818255 90243055975247652907227383)
  ·
    refine ⟨135364583962871479360841075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90243055975247652907227383 135364583962871479360841075)
    ·
      refine ⟨203046875944307219041261613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135364583962871479360841075 203046875944307219041261613)
      ·
        refine ⟨76142578479115207140473105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203046875944307219041261613 76142578479115207140473105)
        ·
          refine ⟨57106933859336405355354829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76142578479115207140473105 57106933859336405355354829)
          ·
            refine ⟨21415100197251152008258061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57106933859336405355354829 21415100197251152008258061)
            ·
              refine ⟨8030662573969182003096773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21415100197251152008258061 8030662573969182003096773)
              ·
                refine ⟨1505749232619221625580645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8030662573969182003096773 1505749232619221625580645)
                ·
                  refine ⟨282327981116104054796371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1505749232619221625580645 282327981116104054796371)
                  ·
                    rfl

theorem cell22_2474243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 4, 4].length) (baseStart_2474243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474243 prefixEnd_2474243 := by exact prefixLift 2474243
  have htrace : WordTrace (prefixWord ++ tailWord_2474243) baseStart_2474243 baseEnd_2474243 := by
    simpa [prefixWord, tailWord_2474243, baseEnd_2474243] using wordTrace_append hprefix tailTrace_2474243
  have hstable : (prefixWord ++ tailWord_2474243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474243).length < 2 ^ (prefixWord ++ tailWord_2474243).sum := by decide
  have hdescent : baseEnd_2474243 < baseStart_2474243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474273 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2474273 : Nat := 118140960795 + 2474273 * 2 ^ 59
def prefixEnd_2474273 : Nat := 4983230072969 + 3 ^ 40 * 2474273 * 2
def baseEnd_2474273 : Nat := 846994212961402086139021

theorem tailTrace_2474273 : CollatzResearch.WordTrace tailWord_2474273 prefixEnd_2474273 846994212961402086139021 := by
  unfold tailWord_2474273
  simp only [CollatzResearch.WordTrace]
  refine ⟨90244150165138968030819473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60162766776759312020546315 90244150165138968030819473)
  ·
    refine ⟨67683112623854226023114605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90244150165138968030819473 67683112623854226023114605)
    ·
      refine ⟨25381167233945334758667977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67683112623854226023114605 25381167233945334758667977)
      ·
        refine ⟨19035875425459001069000983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25381167233945334758667977 19035875425459001069000983)
        ·
          refine ⟨28553813138188501603501475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19035875425459001069000983 28553813138188501603501475)
          ·
            refine ⟨42830719707282752405252213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28553813138188501603501475 42830719707282752405252213)
            ·
              refine ⟨4015379972557758037992395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42830719707282752405252213 4015379972557758037992395)
              ·
                refine ⟨6023069958836637056988593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015379972557758037992395 6023069958836637056988593)
                ·
                  refine ⟨4517302469127477792741445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6023069958836637056988593 4517302469127477792741445)
                  ·
                    refine ⟨846994212961402086139021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517302469127477792741445 846994212961402086139021)
                    ·
                      rfl

theorem cell22_2474273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2474273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474273 prefixEnd_2474273 := by exact prefixLift 2474273
  have htrace : WordTrace (prefixWord ++ tailWord_2474273) baseStart_2474273 baseEnd_2474273 := by
    simpa [prefixWord, tailWord_2474273, baseEnd_2474273] using wordTrace_append hprefix tailTrace_2474273
  have hstable : (prefixWord ++ tailWord_2474273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474273).length < 2 ^ (prefixWord ++ tailWord_2474273).sum := by decide
  have hdescent : baseEnd_2474273 < baseStart_2474273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474279 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2474279 : Nat := 118140960795 + 2474279 * 2 ^ 59
def prefixEnd_2474279 : Nat := 4983230072969 + 3 ^ 40 * 2474279 * 2
def baseEnd_2474279 : Nat := 846996266884020070489003

theorem tailTrace_2474279 : CollatzResearch.WordTrace tailWord_2474279 prefixEnd_2474279 846996266884020070489003 := by
  unfold tailWord_2474279
  simp only [CollatzResearch.WordTrace]
  refine ⟨90244369003117231055537891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60162912668744820703691927 90244369003117231055537891)
  ·
    refine ⟨135366553504675846583306837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90244369003117231055537891 135366553504675846583306837)
    ·
      refine ⟨1586326798882920077148127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 135366553504675846583306837 1586326798882920077148127)
      ·
        refine ⟨2379490198324380115722191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586326798882920077148127 2379490198324380115722191)
        ·
          refine ⟨3569235297486570173583287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379490198324380115722191 3569235297486570173583287)
          ·
            refine ⟨5353852946229855260374931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569235297486570173583287 5353852946229855260374931)
            ·
              refine ⟨8030779419344782890562397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5353852946229855260374931 8030779419344782890562397)
              ·
                refine ⟨3011542282254293583960899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8030779419344782890562397 3011542282254293583960899)
                ·
                  refine ⟨4517313423381440375941349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011542282254293583960899 4517313423381440375941349)
                  ·
                    refine ⟨846996266884020070489003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517313423381440375941349 846996266884020070489003)
                    ·
                      rfl

theorem cell22_2474279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2474279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474279 prefixEnd_2474279 := by exact prefixLift 2474279
  have htrace : WordTrace (prefixWord ++ tailWord_2474279) baseStart_2474279 baseEnd_2474279 := by
    simpa [prefixWord, tailWord_2474279, baseEnd_2474279] using wordTrace_append hprefix tailTrace_2474279
  have hstable : (prefixWord ++ tailWord_2474279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474279).length < 2 ^ (prefixWord ++ tailWord_2474279).sum := by decide
  have hdescent : baseEnd_2474279 < baseStart_2474279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474292 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_2474292 : Nat := 118140960795 + 2474292 * 2 ^ 59
def prefixEnd_2474292 : Nat := 4983230072969 + 3 ^ 40 * 2474292 * 2
def baseEnd_2474292 : Nat := 847000717049692369913963

theorem tailTrace_2474292 : CollatzResearch.WordTrace tailWord_2474292 prefixEnd_2474292 847000717049692369913963 := by
  unfold tailWord_2474292
  simp only [CollatzResearch.WordTrace]
  refine ⟨45122421576035067137880565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60163228768046756183840753 45122421576035067137880565)
  ·
    refine ⟨4230227022753287544176303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45122421576035067137880565 4230227022753287544176303)
    ·
      refine ⟨6345340534129931316264455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230227022753287544176303 6345340534129931316264455)
      ·
        refine ⟨9518010801194896974396683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345340534129931316264455 9518010801194896974396683)
        ·
          refine ⟨14277016201792345461595025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518010801194896974396683 14277016201792345461595025)
          ·
            refine ⟨10707762151344259096196269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14277016201792345461595025 10707762151344259096196269)
            ·
              refine ⟨4015410806754097161073601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10707762151344259096196269 4015410806754097161073601)
              ·
                refine ⟨3011558105065572870805201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015410806754097161073601 3011558105065572870805201)
                ·
                  refine ⟨2258668578799179653103901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3011558105065572870805201 2258668578799179653103901)
                  ·
                    refine ⟨847000717049692369913963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258668578799179653103901 847000717049692369913963)
                    ·
                      rfl

theorem cell22_2474292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_2474292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474292 prefixEnd_2474292 := by exact prefixLift 2474292
  have htrace : WordTrace (prefixWord ++ tailWord_2474292) baseStart_2474292 baseEnd_2474292 := by
    simpa [prefixWord, tailWord_2474292, baseEnd_2474292] using wordTrace_append hprefix tailTrace_2474292
  have hstable : (prefixWord ++ tailWord_2474292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474292).length < 2 ^ (prefixWord ++ tailWord_2474292).sum := by decide
  have hdescent : baseEnd_2474292 < baseStart_2474292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474354 : List Nat := [3, 2, 1, 2, 1, 4, 3, 2, 1, 3]
def baseStart_2474354 : Nat := 118140960795 + 2474354 * 2 ^ 59
def prefixEnd_2474354 : Nat := 4983230072969 + 3 ^ 40 * 2474354 * 2
def baseEnd_2474354 : Nat := 847021940916744874863773

theorem tailTrace_2474354 : CollatzResearch.WordTrace tailWord_2474354 prefixEnd_2474354 847021940916744874863773 := by
  unfold tailWord_2474354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561776119461379716129529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60164736318563679243012077 22561776119461379716129529)
  ·
    refine ⟨16921332089596034787097147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22561776119461379716129529 16921332089596034787097147)
    ·
      refine ⟨25381998134394052180645721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16921332089596034787097147 25381998134394052180645721)
      ·
        refine ⟨19036498600795539135484291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25381998134394052180645721 19036498600795539135484291)
        ·
          refine ⟨28554747901193308703226437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19036498600795539135484291 28554747901193308703226437)
          ·
            refine ⟨5354015231473745381854957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28554747901193308703226437 5354015231473745381854957)
            ·
              refine ⟨2007755711802654518195609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5354015231473745381854957 2007755711802654518195609)
              ·
                refine ⟨1505816783851990888646707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007755711802654518195609 1505816783851990888646707)
                ·
                  refine ⟨2258725175777986332970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505816783851990888646707 2258725175777986332970061)
                  ·
                    refine ⟨847021940916744874863773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258725175777986332970061 847021940916744874863773)
                    ·
                      rfl

theorem cell22_2474354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_2474354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474354 prefixEnd_2474354 := by exact prefixLift 2474354
  have htrace : WordTrace (prefixWord ++ tailWord_2474354) baseStart_2474354 baseEnd_2474354 := by
    simpa [prefixWord, tailWord_2474354, baseEnd_2474354] using wordTrace_append hprefix tailTrace_2474354
  have hstable : (prefixWord ++ tailWord_2474354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474354).length < 2 ^ (prefixWord ++ tailWord_2474354).sum := by decide
  have hdescent : baseEnd_2474354 < baseStart_2474354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474380 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_2474380 : Nat := 118140960795 + 2474380 * 2 ^ 59
def prefixEnd_2474380 : Nat := 4983230072969 + 3 ^ 40 * 2474380 * 2
def baseEnd_2474380 : Nat := 847030841248089473713693

theorem tailTrace_2474380 : CollatzResearch.WordTrace tailWord_2474380 prefixEnd_2474380 847030841248089473713693 := by
  unfold tailWord_2474380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45124026387875662652482297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60165368517167550203309729 45124026387875662652482297)
  ·
    refine ⟨33843019790906746989361723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45124026387875662652482297 33843019790906746989361723)
    ·
      refine ⟨50764529686360120484042585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33843019790906746989361723 50764529686360120484042585)
      ·
        refine ⟨38073397264770090363031939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50764529686360120484042585 38073397264770090363031939)
        ·
          refine ⟨57110095897155135544547909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38073397264770090363031939 57110095897155135544547909)
          ·
            refine ⟨10708142980716587914602733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57110095897155135544547909 10708142980716587914602733)
            ·
              refine ⟨4015553617768720467976025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10708142980716587914602733 4015553617768720467976025)
              ·
                refine ⟨3011665213326540350982019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015553617768720467976025 3011665213326540350982019)
                ·
                  refine ⟨4517497819989810526473029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011665213326540350982019 4517497819989810526473029)
                  ·
                    refine ⟨847030841248089473713693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517497819989810526473029 847030841248089473713693)
                    ·
                      rfl

theorem cell22_2474380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_2474380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474380 prefixEnd_2474380 := by exact prefixLift 2474380
  have htrace : WordTrace (prefixWord ++ tailWord_2474380) baseStart_2474380 baseEnd_2474380 := by
    simpa [prefixWord, tailWord_2474380, baseEnd_2474380] using wordTrace_append hprefix tailTrace_2474380
  have hstable : (prefixWord ++ tailWord_2474380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474380).length < 2 ^ (prefixWord ++ tailWord_2474380).sum := by decide
  have hdescent : baseEnd_2474380 < baseStart_2474380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474393 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_2474393 : Nat := 118140960795 + 2474393 * 2 ^ 59
def prefixEnd_2474393 : Nat := 4983230072969 + 3 ^ 40 * 2474393 * 2
def baseEnd_2474393 : Nat := 847035291413761773138653

theorem tailTrace_2474393 : CollatzResearch.WordTrace tailWord_2474393 prefixEnd_2474393 847035291413761773138653 := by
  unfold tailWord_2474393
  simp only [CollatzResearch.WordTrace]
  refine ⟨90248526924704228525187833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60165684616469485683458555 90248526924704228525187833)
  ·
    refine ⟨67686395193528171393890875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90248526924704228525187833 67686395193528171393890875)
    ·
      refine ⟨101529592790292257090836313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67686395193528171393890875 101529592790292257090836313)
      ·
        refine ⟨76147194592719192818127235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101529592790292257090836313 76147194592719192818127235)
        ·
          refine ⟨114220791889078789227190853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76147194592719192818127235 114220791889078789227190853)
          ·
            refine ⟨21416398479202272980098285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114220791889078789227190853 21416398479202272980098285)
            ·
              refine ⟨8031149429700852367536857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21416398479202272980098285 8031149429700852367536857)
              ·
                refine ⟨6023362072275639275652643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8031149429700852367536857 6023362072275639275652643)
                ·
                  refine ⟨9035043108413458913478965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6023362072275639275652643 9035043108413458913478965)
                  ·
                    refine ⟨847035291413761773138653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9035043108413458913478965 847035291413761773138653)
                    ·
                      rfl

theorem cell22_2474393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_2474393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474393 prefixEnd_2474393 := by exact prefixLift 2474393
  have htrace : WordTrace (prefixWord ++ tailWord_2474393) baseStart_2474393 baseEnd_2474393 := by
    simpa [prefixWord, tailWord_2474393, baseEnd_2474393] using wordTrace_append hprefix tailTrace_2474393
  have hstable : (prefixWord ++ tailWord_2474393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474393).length < 2 ^ (prefixWord ++ tailWord_2474393).sum := by decide
  have hdescent : baseEnd_2474393 < baseStart_2474393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474406 : List Nat := [22]
def baseStart_2474406 : Nat := 118140960795 + 2474406 * 2 ^ 59
def prefixEnd_2474406 : Nat := 4983230072969 + 3 ^ 40 * 2474406 * 2
def baseEnd_2474406 : Nat := 43034077202633443711

theorem tailTrace_2474406 : CollatzResearch.WordTrace tailWord_2474406 prefixEnd_2474406 43034077202633443711 := by
  unfold tailWord_2474406
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034077202633443711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 22 60166000715771421163607381 43034077202633443711)
  ·
    rfl

theorem cell22_2474406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 22].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 22].length) (baseStart_2474406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474406 prefixEnd_2474406 := by exact prefixLift 2474406
  have htrace : WordTrace (prefixWord ++ tailWord_2474406) baseStart_2474406 baseEnd_2474406 := by
    simpa [prefixWord, tailWord_2474406, baseEnd_2474406] using wordTrace_append hprefix tailTrace_2474406
  have hstable : (prefixWord ++ tailWord_2474406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474406).length < 2 ^ (prefixWord ++ tailWord_2474406).sum := by decide
  have hdescent : baseEnd_2474406 < baseStart_2474406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474423 : List Nat := [1, 1, 3, 1, 3, 3, 3, 7]
def baseStart_2474423 : Nat := 118140960795 + 2474423 * 2 ^ 59
def prefixEnd_2474423 : Nat := 4983230072969 + 3 ^ 40 * 2474423 * 2
def baseEnd_2474423 : Nat := 94116173447427966098729

theorem tailTrace_2474423 : CollatzResearch.WordTrace tailWord_2474423 prefixEnd_2474423 94116173447427966098729 := by
  unfold tailWord_2474423
  simp only [CollatzResearch.WordTrace]
  refine ⟨90249621114595543648779923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60166414076397029099186615 90249621114595543648779923)
  ·
    refine ⟨135374431671893315473169885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90249621114595543648779923 135374431671893315473169885)
    ·
      refine ⟨50765411876959993302438707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135374431671893315473169885 50765411876959993302438707)
      ·
        refine ⟨76148117815439989953658061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50765411876959993302438707 76148117815439989953658061)
        ·
          refine ⟨28555544180789996232621773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76148117815439989953658061 28555544180789996232621773)
          ·
            refine ⟨10708329067796248587233165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28555544180789996232621773 10708329067796248587233165)
            ·
              refine ⟨4015623400423593220212437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10708329067796248587233165 4015623400423593220212437)
              ·
                refine ⟨94116173447427966098729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4015623400423593220212437 94116173447427966098729)
                ·
                  rfl

theorem cell22_2474423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 7].length) (baseStart_2474423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474423 prefixEnd_2474423 := by exact prefixLift 2474423
  have htrace : WordTrace (prefixWord ++ tailWord_2474423) baseStart_2474423 baseEnd_2474423 := by
    simpa [prefixWord, tailWord_2474423, baseEnd_2474423] using wordTrace_append hprefix tailTrace_2474423
  have hstable : (prefixWord ++ tailWord_2474423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474423).length < 2 ^ (prefixWord ++ tailWord_2474423).sum := by decide
  have hdescent : baseEnd_2474423 < baseStart_2474423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474440 : List Nat := [2, 1, 3, 1, 3, 3, 3, 6]
def baseStart_2474440 : Nat := 118140960795 + 2474440 * 2 ^ 59
def prefixEnd_2474440 : Nat := 4983230072969 + 3 ^ 40 * 2474440 * 2
def baseEnd_2474440 : Nat := 94116820052696590801501

theorem tailTrace_2474440 : CollatzResearch.WordTrace tailWord_2474440 prefixEnd_2474440 94116820052696590801501 := by
  unfold tailWord_2474440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125120577766977776074387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60166827437022637034765849 45125120577766977776074387)
  ·
    refine ⟨67687680866650466664111581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45125120577766977776074387 67687680866650466664111581)
    ·
      refine ⟨25382880324993924999041843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67687680866650466664111581 25382880324993924999041843)
      ·
        refine ⟨38074320487490887498562765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25382880324993924999041843 38074320487490887498562765)
        ·
          refine ⟨14277870182809082811961037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38074320487490887498562765 14277870182809082811961037)
          ·
            refine ⟨5354201318553406054485389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14277870182809082811961037 5354201318553406054485389)
            ·
              refine ⟨2007825494457527270432021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5354201318553406054485389 2007825494457527270432021)
              ·
                refine ⟨94116820052696590801501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2007825494457527270432021 94116820052696590801501)
                ·
                  rfl

theorem cell22_2474440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_2474440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474440 prefixEnd_2474440 := by exact prefixLift 2474440
  have htrace : WordTrace (prefixWord ++ tailWord_2474440) baseStart_2474440 baseEnd_2474440 := by
    simpa [prefixWord, tailWord_2474440, baseEnd_2474440] using wordTrace_append hprefix tailTrace_2474440
  have hstable : (prefixWord ++ tailWord_2474440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474440).length < 2 ^ (prefixWord ++ tailWord_2474440).sum := by decide
  have hdescent : baseEnd_2474440 < baseStart_2474440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474472 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_2474472 : Nat := 118140960795 + 2474472 * 2 ^ 59
def prefixEnd_2474472 : Nat := 4983230072969 + 3 ^ 40 * 2474472 * 2
def baseEnd_2474472 : Nat := 847062334728231900413411

theorem tailTrace_2474472 : CollatzResearch.WordTrace tailWord_2474472 prefixEnd_2474472 847062334728231900413411 := by
  unfold tailWord_2474472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45125704145709012508656835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60167605527612016678209113 45125704145709012508656835)
  ·
    refine ⟨67688556218563518762985253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45125704145709012508656835 67688556218563518762985253)
    ·
      refine ⟨12691604290980659768059735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67688556218563518762985253 12691604290980659768059735)
      ·
        refine ⟨19037406436470989652089603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12691604290980659768059735 19037406436470989652089603)
        ·
          refine ⟨28556109654706484478134405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19037406436470989652089603 28556109654706484478134405)
          ·
            refine ⟨5354270560257465839650201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28556109654706484478134405 5354270560257465839650201)
            ·
              refine ⟨4015702920193099379737651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5354270560257465839650201 4015702920193099379737651)
              ·
                refine ⟨6023554380289649069606477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4015702920193099379737651 6023554380289649069606477)
                ·
                  refine ⟨2258832892608618401102429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6023554380289649069606477 2258832892608618401102429)
                  ·
                    refine ⟨847062334728231900413411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258832892608618401102429 847062334728231900413411)
                    ·
                      rfl

theorem cell22_2474472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_2474472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474472 prefixEnd_2474472 := by exact prefixLift 2474472
  have htrace : WordTrace (prefixWord ++ tailWord_2474472) baseStart_2474472 baseEnd_2474472 := by
    simpa [prefixWord, tailWord_2474472, baseEnd_2474472] using wordTrace_append hprefix tailTrace_2474472
  have hstable : (prefixWord ++ tailWord_2474472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474472).length < 2 ^ (prefixWord ++ tailWord_2474472).sum := by decide
  have hdescent : baseEnd_2474472 < baseStart_2474472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474483 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_2474483 : Nat := 118140960795 + 2474483 * 2 ^ 59
def prefixEnd_2474483 : Nat := 4983230072969 + 3 ^ 40 * 2474483 * 2
def baseEnd_2474483 : Nat := 847066100253031538388377

theorem tailTrace_2474483 : CollatzResearch.WordTrace tailWord_2474483 prefixEnd_2474483 847066100253031538388377 := by
  unfold tailWord_2474483
  simp only [CollatzResearch.WordTrace]
  refine ⟨90251809494378173895964103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60167872996252115930642735 90251809494378173895964103)
  ·
    refine ⟨135377714241567260843946155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90251809494378173895964103 135377714241567260843946155)
    ·
      refine ⟨203066571362350891265919233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135377714241567260843946155 203066571362350891265919233)
      ·
        refine ⟨152299928521763168449439425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203066571362350891265919233 152299928521763168449439425)
        ·
          refine ⟨114224946391322376337079569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152299928521763168449439425 114224946391322376337079569)
          ·
            refine ⟨85668709793491782252809677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114224946391322376337079569 85668709793491782252809677)
            ·
              refine ⟨32125766172559418344803629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85668709793491782252809677 32125766172559418344803629)
              ·
                refine ⟨12047162314709781879301361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32125766172559418344803629 12047162314709781879301361)
                ·
                  refine ⟨9035371736032336409476021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12047162314709781879301361 9035371736032336409476021)
                  ·
                    refine ⟨847066100253031538388377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9035371736032336409476021 847066100253031538388377)
                    ·
                      rfl

theorem cell22_2474483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_2474483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474483 prefixEnd_2474483 := by exact prefixLift 2474483
  have htrace : WordTrace (prefixWord ++ tailWord_2474483) baseStart_2474483 baseEnd_2474483 := by
    simpa [prefixWord, tailWord_2474483, baseEnd_2474483] using wordTrace_append hprefix tailTrace_2474483
  have hstable : (prefixWord ++ tailWord_2474483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474483).length < 2 ^ (prefixWord ++ tailWord_2474483).sum := by decide
  have hdescent : baseEnd_2474483 < baseStart_2474483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474515 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 1, 4]
def baseStart_2474515 : Nat := 118140960795 + 2474515 * 2 ^ 59
def prefixEnd_2474515 : Nat := 4983230072969 + 3 ^ 40 * 2474515 * 2
def baseEnd_2474515 : Nat := 847077054506994121588279

theorem tailTrace_2474515 : CollatzResearch.WordTrace tailWord_2474515 prefixEnd_2474515 847077054506994121588279 := by
  unfold tailWord_2474515
  simp only [CollatzResearch.WordTrace]
  refine ⟨90252976630262243361128999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60168651086841495574085999 90252976630262243361128999)
  ·
    refine ⟨135379464945393365041693499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90252976630262243361128999 135379464945393365041693499)
    ·
      refine ⟨203069197418090047562540249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135379464945393365041693499 203069197418090047562540249)
      ·
        refine ⟨152301898063567535671905187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203069197418090047562540249 152301898063567535671905187)
        ·
          refine ⟨228452847095351303507857781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152301898063567535671905187 228452847095351303507857781)
          ·
            refine ⟨21417454415189184703861667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 228452847095351303507857781 21417454415189184703861667)
            ·
              refine ⟨32126181622783777055792501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21417454415189184703861667 32126181622783777055792501)
              ·
                refine ⟨3011829527135979098980547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32126181622783777055792501 3011829527135979098980547)
                ·
                  refine ⟨4517744290703968648470821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3011829527135979098980547 4517744290703968648470821)
                  ·
                    refine ⟨847077054506994121588279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517744290703968648470821 847077054506994121588279)
                    ·
                      rfl

theorem cell22_2474515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4].length) (baseStart_2474515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474515 prefixEnd_2474515 := by exact prefixLift 2474515
  have htrace : WordTrace (prefixWord ++ tailWord_2474515) baseStart_2474515 baseEnd_2474515 := by
    simpa [prefixWord, tailWord_2474515, baseEnd_2474515] using wordTrace_append hprefix tailTrace_2474515
  have hstable : (prefixWord ++ tailWord_2474515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474515).length < 2 ^ (prefixWord ++ tailWord_2474515).sum := by decide
  have hdescent : baseEnd_2474515 < baseStart_2474515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474560 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_2474560 : Nat := 118140960795 + 2474560 * 2 ^ 59
def prefixEnd_2474560 : Nat := 4983230072969 + 3 ^ 40 * 2474560 * 2
def baseEnd_2474560 : Nat := 847092458926629004213141

theorem tailTrace_2474560 : CollatzResearch.WordTrace tailWord_2474560 prefixEnd_2474560 847092458926629004213141 := by
  unfold tailWord_2474560
  simp only [CollatzResearch.WordTrace]
  refine ⟨45127308957549608023258567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60169745276732810697678089 45127308957549608023258567)
  ·
    refine ⟨67690963436324412034887851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45127308957549608023258567 67690963436324412034887851)
    ·
      refine ⟨101536445154486618052331777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67690963436324412034887851 101536445154486618052331777)
      ·
        refine ⟨76152333865864963539248833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101536445154486618052331777 76152333865864963539248833)
        ·
          refine ⟨57114250399398722654436625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76152333865864963539248833 57114250399398722654436625)
          ·
            refine ⟨42835687799549041990827469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57114250399398722654436625 42835687799549041990827469)
            ·
              refine ⟨16063382924830890746560301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42835687799549041990827469 16063382924830890746560301)
              ·
                refine ⟨6023768596811584029960113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16063382924830890746560301 6023768596811584029960113)
                ·
                  refine ⟨4517826447608688022470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6023768596811584029960113 4517826447608688022470085)
                  ·
                    refine ⟨847092458926629004213141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4517826447608688022470085 847092458926629004213141)
                    ·
                      rfl

theorem cell22_2474560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_2474560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474560 prefixEnd_2474560 := by exact prefixLift 2474560
  have htrace : WordTrace (prefixWord ++ tailWord_2474560) baseStart_2474560 baseEnd_2474560 := by
    simpa [prefixWord, tailWord_2474560, baseEnd_2474560] using wordTrace_append hprefix tailTrace_2474560
  have hstable : (prefixWord ++ tailWord_2474560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474560).length < 2 ^ (prefixWord ++ tailWord_2474560).sum := by decide
  have hdescent : baseEnd_2474560 < baseStart_2474560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474624 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 1, 3]
def baseStart_2474624 : Nat := 118140960795 + 2474624 * 2 ^ 59
def prefixEnd_2474624 : Nat := 4983230072969 + 3 ^ 40 * 2474624 * 2
def baseEnd_2474624 : Nat := 847114367434554170612945

theorem tailTrace_2474624 : CollatzResearch.WordTrace tailWord_2474624 prefixEnd_2474624 847114367434554170612945 := by
  unfold tailWord_2474624
  simp only [CollatzResearch.WordTrace]
  refine ⟨45128476093433677488423463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60171301457911569984564617 45128476093433677488423463)
  ·
    refine ⟨67692714140150516232635195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45128476093433677488423463 67692714140150516232635195)
    ·
      refine ⟨101539071210225774348952793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67692714140150516232635195 101539071210225774348952793)
      ·
        refine ⟨76154303407669330761714595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101539071210225774348952793 76154303407669330761714595)
        ·
          refine ⟨114231455111503996142571893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76154303407669330761714595 114231455111503996142571893)
          ·
            refine ⟨10709198916703499638366115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114231455111503996142571893 10709198916703499638366115)
            ·
              refine ⟨16063798375055249457549173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10709198916703499638366115 16063798375055249457549173)
              ·
                refine ⟨1505981097661429636645235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16063798375055249457549173 1505981097661429636645235)
                ·
                  refine ⟨2258971646492144454967853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505981097661429636645235 2258971646492144454967853)
                  ·
                    refine ⟨847114367434554170612945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2258971646492144454967853 847114367434554170612945)
                    ·
                      rfl

theorem cell22_2474624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_2474624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474624 prefixEnd_2474624 := by exact prefixLift 2474624
  have htrace : WordTrace (prefixWord ++ tailWord_2474624) baseStart_2474624 baseEnd_2474624 := by
    simpa [prefixWord, tailWord_2474624, baseEnd_2474624] using wordTrace_append hprefix tailTrace_2474624
  have hstable : (prefixWord ++ tailWord_2474624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474624).length < 2 ^ (prefixWord ++ tailWord_2474624).sum := by decide
  have hdescent : baseEnd_2474624 < baseStart_2474624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474626 : List Nat := [3, 4, 3, 1, 1, 1, 9]
def baseStart_2474626 : Nat := 118140960795 + 2474626 * 2 ^ 59
def prefixEnd_2474626 : Nat := 4983230072969 + 3 ^ 40 * 2474626 * 2
def baseEnd_2474626 : Nat := 31374631558349141928257

theorem tailTrace_2474626 : CollatzResearch.WordTrace tailWord_2474626 prefixEnd_2474626 31374631558349141928257 := by
  unfold tailWord_2474626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22564256283215027329604933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60171350088573406212279821 22564256283215027329604933)
  ·
    refine ⟨4230798053102817624300925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22564256283215027329604933 4230798053102817624300925)
    ·
      refine ⟨1586549269913556609112847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4230798053102817624300925 1586549269913556609112847)
      ·
        refine ⟨2379823904870334913669271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586549269913556609112847 2379823904870334913669271)
        ·
          refine ⟨3569735857305502370503907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379823904870334913669271 3569735857305502370503907)
          ·
            refine ⟨5354603785958253555755861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569735857305502370503907 5354603785958253555755861)
            ·
              refine ⟨31374631558349141928257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5354603785958253555755861 31374631558349141928257)
              ·
                rfl

theorem cell22_2474626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 9].length) (baseStart_2474626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474626 prefixEnd_2474626 := by exact prefixLift 2474626
  have htrace : WordTrace (prefixWord ++ tailWord_2474626) baseStart_2474626 baseEnd_2474626 := by
    simpa [prefixWord, tailWord_2474626, baseEnd_2474626] using wordTrace_append hprefix tailTrace_2474626
  have hstable : (prefixWord ++ tailWord_2474626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474626).length < 2 ^ (prefixWord ++ tailWord_2474626).sum := by decide
  have hdescent : baseEnd_2474626 < baseStart_2474626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474652 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2474652 : Nat := 118140960795 + 2474652 * 2 ^ 59
def prefixEnd_2474652 : Nat := 4983230072969 + 3 ^ 40 * 2474652 * 2
def baseEnd_2474652 : Nat := 847123952406771430912859

theorem tailTrace_2474652 : CollatzResearch.WordTrace tailWord_2474652 prefixEnd_2474652 847123952406771430912859 := by
  unfold tailWord_2474652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45128986715382957879433105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60171982287177277172577473 45128986715382957879433105)
  ·
    refine ⟨33846740036537218409574829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45128986715382957879433105 33846740036537218409574829)
    ·
      refine ⟨12692527513701456903590561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33846740036537218409574829 12692527513701456903590561)
      ·
        refine ⟨9519395635276092677692921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12692527513701456903590561 9519395635276092677692921)
        ·
          refine ⟨7139546726457069508269691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9519395635276092677692921 7139546726457069508269691)
          ·
            refine ⟨10709320089685604262404537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7139546726457069508269691 10709320089685604262404537)
            ·
              refine ⟨8031990067264203196803403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10709320089685604262404537 8031990067264203196803403)
              ·
                refine ⟨12047985100896304795205105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031990067264203196803403 12047985100896304795205105)
                ·
                  refine ⟨9035988825672228596403829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12047985100896304795205105 9035988825672228596403829)
                  ·
                    refine ⟨847123952406771430912859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9035988825672228596403829 847123952406771430912859)
                    ·
                      rfl

theorem cell22_2474652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2474652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474652 prefixEnd_2474652 := by exact prefixLift 2474652
  have htrace : WordTrace (prefixWord ++ tailWord_2474652) baseStart_2474652 baseEnd_2474652 := by
    simpa [prefixWord, tailWord_2474652, baseEnd_2474652] using wordTrace_append hprefix tailTrace_2474652
  have hstable : (prefixWord ++ tailWord_2474652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474652).length < 2 ^ (prefixWord ++ tailWord_2474652).sum := by decide
  have hdescent : baseEnd_2474652 < baseStart_2474652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474695 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2474695 : Nat := 118140960795 + 2474695 * 2 ^ 59
def prefixEnd_2474695 : Nat := 4983230072969 + 3 ^ 40 * 2474695 * 2
def baseEnd_2474695 : Nat := 847138672185533652087727

theorem tailTrace_2474695 : CollatzResearch.WordTrace tailWord_2474695 prefixEnd_2474695 847138672185533652087727 := by
  unfold tailWord_2474695
  simp only [CollatzResearch.WordTrace]
  refine ⟨90259541769610134102681539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60173027846406756068454359 90259541769610134102681539)
  ·
    refine ⟨135389312654415201154022309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90259541769610134102681539 135389312654415201154022309)
    ·
      refine ⟨25385496122702850216379183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135389312654415201154022309 25385496122702850216379183)
      ·
        refine ⟨38078244184054275324568775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25385496122702850216379183 38078244184054275324568775)
        ·
          refine ⟨57117366276081412986853163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38078244184054275324568775 57117366276081412986853163)
          ·
            refine ⟨85676049414122119480279745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57117366276081412986853163 85676049414122119480279745)
            ·
              refine ⟨64257037060591589610209809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85676049414122119480279745 64257037060591589610209809)
              ·
                refine ⟨48192777795443692207657357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64257037060591589610209809 48192777795443692207657357)
                ·
                  refine ⟨18072291673291384577871509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48192777795443692207657357 18072291673291384577871509)
                  ·
                    refine ⟨847138672185533652087727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18072291673291384577871509 847138672185533652087727)
                    ·
                      rfl

theorem cell22_2474695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2474695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474695 prefixEnd_2474695 := by exact prefixLift 2474695
  have htrace : WordTrace (prefixWord ++ tailWord_2474695) baseStart_2474695 baseEnd_2474695 := by
    simpa [prefixWord, tailWord_2474695, baseEnd_2474695] using wordTrace_append hprefix tailTrace_2474695
  have hstable : (prefixWord ++ tailWord_2474695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474695).length < 2 ^ (prefixWord ++ tailWord_2474695).sum := by decide
  have hdescent : baseEnd_2474695 < baseStart_2474695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474714 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 2, 3]
def baseStart_2474714 : Nat := 118140960795 + 2474714 * 2 ^ 59
def prefixEnd_2474714 : Nat := 4983230072969 + 3 ^ 40 * 2474714 * 2
def baseEnd_2474714 : Nat := 847145176273823935862669

theorem tailTrace_2474714 : CollatzResearch.WordTrace tailWord_2474714 prefixEnd_2474714 847145176273823935862669 := by
  unfold tailWord_2474714
  simp only [CollatzResearch.WordTrace]
  refine ⟨22565058689135325086905799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60173489837694200231748797 22565058689135325086905799)
  ·
    refine ⟨33847588033702987630358699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22565058689135325086905799 33847588033702987630358699)
    ·
      refine ⟨50771382050554481445538049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33847588033702987630358699 50771382050554481445538049)
      ·
        refine ⟨38078536537915861084153537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50771382050554481445538049 38078536537915861084153537)
        ·
          refine ⟨28558902403436895813115153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38078536537915861084153537 28558902403436895813115153)
          ·
            refine ⟨21419176802577671859836365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28558902403436895813115153 21419176802577671859836365)
            ·
              refine ⟨8032191300966626947438637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21419176802577671859836365 8032191300966626947438637)
              ·
                refine ⟨3012071737862485105289489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8032191300966626947438637 3012071737862485105289489)
                ·
                  refine ⟨2259053803396863828967117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012071737862485105289489 2259053803396863828967117)
                  ·
                    refine ⟨847145176273823935862669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259053803396863828967117 847145176273823935862669)
                    ·
                      rfl

theorem cell22_2474714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_2474714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474714 prefixEnd_2474714 := by exact prefixLift 2474714
  have htrace : WordTrace (prefixWord ++ tailWord_2474714) baseStart_2474714 baseEnd_2474714 := by
    simpa [prefixWord, tailWord_2474714, baseEnd_2474714] using wordTrace_append hprefix tailTrace_2474714
  have hstable : (prefixWord ++ tailWord_2474714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474714).length < 2 ^ (prefixWord ++ tailWord_2474714).sum := by decide
  have hdescent : baseEnd_2474714 < baseStart_2474714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474806 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2474806 : Nat := 118140960795 + 2474806 * 2 ^ 59
def prefixEnd_2474806 : Nat := 4983230072969 + 3 ^ 40 * 2474806 * 2
def baseEnd_2474806 : Nat := 282392223251322120854129

theorem tailTrace_2474806 : CollatzResearch.WordTrace tailWord_2474806 prefixEnd_2474806 282392223251322120854129 := by
  unfold tailWord_2474806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641474392013000003748267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60175726848138666706648181 5641474392013000003748267)
  ·
    refine ⟨8462211588019500005622401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641474392013000003748267 8462211588019500005622401)
    ·
      refine ⟨6346658691014625004216801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8462211588019500005622401 6346658691014625004216801)
      ·
        refine ⟨4759994018260968753162601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6346658691014625004216801 4759994018260968753162601)
        ·
          refine ⟨3569995513695726564871951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4759994018260968753162601 3569995513695726564871951)
          ·
            refine ⟨5354993270543589847307927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569995513695726564871951 5354993270543589847307927)
            ·
              refine ⟨8032489905815384770961891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5354993270543589847307927 8032489905815384770961891)
              ·
                refine ⟨12048734858723077156442837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8032489905815384770961891 12048734858723077156442837)
                ·
                  refine ⟨282392223251322120854129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12048734858723077156442837 282392223251322120854129)
                  ·
                    rfl

theorem cell22_2474806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2474806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474806 prefixEnd_2474806 := by exact prefixLift 2474806
  have htrace : WordTrace (prefixWord ++ tailWord_2474806) baseStart_2474806 baseEnd_2474806 := by
    simpa [prefixWord, tailWord_2474806, baseEnd_2474806] using wordTrace_append hprefix tailTrace_2474806
  have hstable : (prefixWord ++ tailWord_2474806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474806).length < 2 ^ (prefixWord ++ tailWord_2474806).sum := by decide
  have hdescent : baseEnd_2474806 < baseStart_2474806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474847 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_2474847 : Nat := 118140960795 + 2474847 * 2 ^ 59
def prefixEnd_2474847 : Nat := 4983230072969 + 3 ^ 40 * 2474847 * 2
def baseEnd_2474847 : Nat := 847190704891855922287261

theorem tailTrace_2474847 : CollatzResearch.WordTrace tailWord_2474847 prefixEnd_2474847 847190704891855922287261 := by
  unfold tailWord_2474847
  simp only [CollatzResearch.WordTrace]
  refine ⟨90265085665059464062214795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60176723776706309374809863 90265085665059464062214795)
  ·
    refine ⟨135397628497589196093322193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90265085665059464062214795 135397628497589196093322193)
    ·
      refine ⟨101548221373191897069991645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135397628497589196093322193 101548221373191897069991645)
      ·
        refine ⟨38080583014946961401246867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101548221373191897069991645 38080583014946961401246867)
        ·
          refine ⟨57120874522420442101870301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38080583014946961401246867 57120874522420442101870301)
          ·
            refine ⟨21420327945907665788201363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57120874522420442101870301 21420327945907665788201363)
            ·
              refine ⟨32130491918861498682302045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21420327945907665788201363 32130491918861498682302045)
              ·
                refine ⟨12048934469573062005863267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32130491918861498682302045 12048934469573062005863267)
                ·
                  refine ⟨18073401704359593008794901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12048934469573062005863267 18073401704359593008794901)
                  ·
                    refine ⟨847190704891855922287261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18073401704359593008794901 847190704891855922287261)
                    ·
                      rfl

theorem cell22_2474847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_2474847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474847 prefixEnd_2474847 := by exact prefixLift 2474847
  have htrace : WordTrace (prefixWord ++ tailWord_2474847) baseStart_2474847 baseEnd_2474847 := by
    simpa [prefixWord, tailWord_2474847, baseEnd_2474847] using wordTrace_append hprefix tailTrace_2474847
  have hstable : (prefixWord ++ tailWord_2474847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474847).length < 2 ^ (prefixWord ++ tailWord_2474847).sum := by decide
  have hdescent : baseEnd_2474847 < baseStart_2474847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474851 : List Nat := [1, 1, 1, 5, 3, 1, 3, 3, 4]
def baseStart_2474851 : Nat := 118140960795 + 2474851 * 2 ^ 59
def prefixEnd_2474851 : Nat := 4983230072969 + 3 ^ 40 * 2474851 * 2
def baseEnd_2474851 : Nat := 282397358057867081729083

theorem tailTrace_2474851 : CollatzResearch.WordTrace tailWord_2474851 prefixEnd_2474851 282397358057867081729083 := by
  unfold tailWord_2474851
  simp only [CollatzResearch.WordTrace]
  refine ⟨90265231557044972745360407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60176821038029981830240271 90265231557044972745360407)
  ·
    refine ⟨135397847335567459118040611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90265231557044972745360407 135397847335567459118040611)
    ·
      refine ⟨203096771003351188677060917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135397847335567459118040611 203096771003351188677060917)
      ·
        refine ⟨19040322281564173938474461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203096771003351188677060917 19040322281564173938474461)
        ·
          refine ⟨7140120855586565226927923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19040322281564173938474461 7140120855586565226927923)
          ·
            refine ⟨10710181283379847840391885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7140120855586565226927923 10710181283379847840391885)
            ·
              refine ⟨4016317981267442940146957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10710181283379847840391885 4016317981267442940146957)
              ·
                refine ⟨1506119242975291102555109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4016317981267442940146957 1506119242975291102555109)
                ·
                  refine ⟨282397358057867081729083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1506119242975291102555109 282397358057867081729083)
                  ·
                    rfl

theorem cell22_2474851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 4].length) (baseStart_2474851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474851 prefixEnd_2474851 := by exact prefixLift 2474851
  have htrace : WordTrace (prefixWord ++ tailWord_2474851) baseStart_2474851 baseEnd_2474851 := by
    simpa [prefixWord, tailWord_2474851, baseEnd_2474851] using wordTrace_append hprefix tailTrace_2474851
  have hstable : (prefixWord ++ tailWord_2474851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474851).length < 2 ^ (prefixWord ++ tailWord_2474851).sum := by decide
  have hdescent : baseEnd_2474851 < baseStart_2474851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474898 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2474898 : Nat := 118140960795 + 2474898 * 2 ^ 59
def prefixEnd_2474898 : Nat := 4983230072969 + 3 ^ 40 * 2474898 * 2
def baseEnd_2474898 : Nat := 847208163234108789262105

theorem tailTrace_2474898 : CollatzResearch.WordTrace tailWord_2474898 prefixEnd_2474898 847208163234108789262105 := by
  unfold tailWord_2474898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566736446968674943080337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60177963858583133181547565 22566736446968674943080337)
  ·
    refine ⟨16925052335226506207310253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22566736446968674943080337 16925052335226506207310253)
    ·
      refine ⟨6346894625709939827741345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16925052335226506207310253 6346894625709939827741345)
      ·
        refine ⟨4760170969282454870806009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6346894625709939827741345 4760170969282454870806009)
        ·
          refine ⟨3570128226961841153104507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4760170969282454870806009 3570128226961841153104507)
          ·
            refine ⟨5355192340442761729656761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570128226961841153104507 5355192340442761729656761)
            ·
              refine ⟨4016394255332071297242571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5355192340442761729656761 4016394255332071297242571)
              ·
                refine ⟨6024591382998106945863857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016394255332071297242571 6024591382998106945863857)
                ·
                  refine ⟨4518443537248580209397893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6024591382998106945863857 4518443537248580209397893)
                  ·
                    refine ⟨847208163234108789262105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518443537248580209397893 847208163234108789262105)
                    ·
                      rfl

theorem cell22_2474898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2474898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474898 prefixEnd_2474898 := by exact prefixLift 2474898
  have htrace : WordTrace (prefixWord ++ tailWord_2474898) baseStart_2474898 baseEnd_2474898 := by
    simpa [prefixWord, tailWord_2474898, baseEnd_2474898] using wordTrace_append hprefix tailTrace_2474898
  have hstable : (prefixWord ++ tailWord_2474898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474898).length < 2 ^ (prefixWord ++ tailWord_2474898).sum := by decide
  have hdescent : baseEnd_2474898 < baseStart_2474898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474984 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2474984 : Nat := 118140960795 + 2474984 * 2 ^ 59
def prefixEnd_2474984 : Nat := 4983230072969 + 3 ^ 40 * 2474984 * 2
def baseEnd_2474984 : Nat := 847237602791633231611841

theorem tailTrace_2474984 : CollatzResearch.WordTrace tailWord_2474984 prefixEnd_2474984 847237602791633231611841 := by
  unfold tailWord_2474984
  simp only [CollatzResearch.WordTrace]
  refine ⟨45135041232781568229976003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60180054977042090973301337 45135041232781568229976003)
  ·
    refine ⟨67702561849172352344964005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45135041232781568229976003 67702561849172352344964005)
    ·
      refine ⟨12694230346719816064680751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67702561849172352344964005 12694230346719816064680751)
      ·
        refine ⟨19041345520079724097021127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694230346719816064680751 19041345520079724097021127)
        ·
          refine ⟨28562018280119586145531691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19041345520079724097021127 28562018280119586145531691)
          ·
            refine ⟨42843027420179379218297537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28562018280119586145531691 42843027420179379218297537)
            ·
              refine ⟨32132270565134534413723153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42843027420179379218297537 32132270565134534413723153)
              ·
                refine ⟨24099202923850900810292365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32132270565134534413723153 24099202923850900810292365)
                ·
                  refine ⟨9037201096444087803859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24099202923850900810292365 9037201096444087803859637)
                  ·
                    refine ⟨847237602791633231611841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9037201096444087803859637 847237602791633231611841)
                    ·
                      rfl

theorem cell22_2474984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2474984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474984 prefixEnd_2474984 := by exact prefixLift 2474984
  have htrace : WordTrace (prefixWord ++ tailWord_2474984) baseStart_2474984 baseEnd_2474984 := by
    simpa [prefixWord, tailWord_2474984, baseEnd_2474984] using wordTrace_append hprefix tailTrace_2474984
  have hstable : (prefixWord ++ tailWord_2474984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474984).length < 2 ^ (prefixWord ++ tailWord_2474984).sum := by decide
  have hdescent : baseEnd_2474984 < baseStart_2474984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2474986 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_2474986 : Nat := 118140960795 + 2474986 * 2 ^ 59
def prefixEnd_2474986 : Nat := 4983230072969 + 3 ^ 40 * 2474986 * 2
def baseEnd_2474986 : Nat := 282412762477501964353945

theorem tailTrace_2474986 : CollatzResearch.WordTrace tailWord_2474986 prefixEnd_2474986 282412762477501964353945 := by
  unfold tailWord_2474986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22567538852888972700381203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60180103607703927201016541 22567538852888972700381203)
  ·
    refine ⟨33851308279333459050571805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22567538852888972700381203 33851308279333459050571805)
    ·
      refine ⟨12694240604750047143964427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33851308279333459050571805 12694240604750047143964427)
      ·
        refine ⟨19041360907125070715946641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12694240604750047143964427 19041360907125070715946641)
        ·
          refine ⟨14281020680343803036959981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19041360907125070715946641 14281020680343803036959981)
          ·
            refine ⟨5355382755128926138859993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14281020680343803036959981 5355382755128926138859993)
            ·
              refine ⟨4016537066346694604144995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5355382755128926138859993 4016537066346694604144995)
              ·
                refine ⟨6024805599520041906217493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016537066346694604144995 6024805599520041906217493)
                ·
                  refine ⟨282412762477501964353945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6024805599520041906217493 282412762477501964353945)
                  ·
                    rfl

theorem cell22_2474986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_2474986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2474986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2474986 prefixEnd_2474986 := by exact prefixLift 2474986
  have htrace : WordTrace (prefixWord ++ tailWord_2474986) baseStart_2474986 baseEnd_2474986 := by
    simpa [prefixWord, tailWord_2474986, baseEnd_2474986] using wordTrace_append hprefix tailTrace_2474986
  have hstable : (prefixWord ++ tailWord_2474986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2474986).length < 2 ^ (prefixWord ++ tailWord_2474986).sum := by decide
  have hdescent : baseEnd_2474986 < baseStart_2474986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2474986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475031 : List Nat := [1, 1, 3, 5, 1, 3, 8]
def baseStart_2475031 : Nat := 118140960795 + 2475031 * 2 ^ 59
def prefixEnd_2475031 : Nat := 4983230072969 + 3 ^ 40 * 2475031 * 2
def baseEnd_2475031 : Nat := 31379766364894102803211

theorem tailTrace_2475031 : CollatzResearch.WordTrace tailWord_2475031 prefixEnd_2475031 31379766364894102803211 := by
  unfold tailWord_2475031
  simp only [CollatzResearch.WordTrace]
  refine ⟨90271796696392863486912947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60181197797595242324608631 90271796696392863486912947)
  ·
    refine ⟨135407695044589295230369421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90271796696392863486912947 135407695044589295230369421)
    ·
      refine ⟨50777885641720985711388533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135407695044589295230369421 50777885641720985711388533)
      ·
        refine ⟨4760426778911342410442675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50777885641720985711388533 4760426778911342410442675)
        ·
          refine ⟨7140640168367013615664013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760426778911342410442675 7140640168367013615664013)
          ·
            refine ⟨2677740063137630105874005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7140640168367013615664013 2677740063137630105874005)
            ·
              refine ⟨31379766364894102803211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2677740063137630105874005 31379766364894102803211)
              ·
                rfl

theorem cell22_2475031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 8].length) (baseStart_2475031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475031 prefixEnd_2475031 := by exact prefixLift 2475031
  have htrace : WordTrace (prefixWord ++ tailWord_2475031) baseStart_2475031 baseEnd_2475031 := by
    simpa [prefixWord, tailWord_2475031, baseEnd_2475031] using wordTrace_append hprefix tailTrace_2475031
  have hstable : (prefixWord ++ tailWord_2475031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475031).length < 2 ^ (prefixWord ++ tailWord_2475031).sum := by decide
  have hdescent : baseEnd_2475031 < baseStart_2475031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475136 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_2475136 : Nat := 118140960795 + 2475136 * 2 ^ 59
def prefixEnd_2475136 : Nat := 4983230072969 + 3 ^ 40 * 2475136 * 2
def baseEnd_2475136 : Nat := 847289635497955501811375

theorem tailTrace_2475136 : CollatzResearch.WordTrace tailWord_2475136 prefixEnd_2475136 847289635497955501811375 := by
  unfold tailWord_2475136
  simp only [CollatzResearch.WordTrace]
  refine ⟨45137813180506233209742631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60183750907341644279656841 45137813180506233209742631)
  ·
    refine ⟨67706719770759349814613947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45137813180506233209742631 67706719770759349814613947)
    ·
      refine ⟨101560079656139024721920921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67706719770759349814613947 101560079656139024721920921)
      ·
        refine ⟨76170059742104268541440691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101560079656139024721920921 76170059742104268541440691)
        ·
          refine ⟨114255089613156402812161037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76170059742104268541440691 114255089613156402812161037)
          ·
            refine ⟨42845658604933651054560389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114255089613156402812161037 42845658604933651054560389)
            ·
              refine ⟨8033560988425059572730073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42845658604933651054560389 8033560988425059572730073)
              ·
                refine ⟨6025170741318794679547555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8033560988425059572730073 6025170741318794679547555)
                ·
                  refine ⟨9037756111978192019321333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6025170741318794679547555 9037756111978192019321333)
                  ·
                    refine ⟨847289635497955501811375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9037756111978192019321333 847289635497955501811375)
                    ·
                      rfl

theorem cell22_2475136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_2475136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475136 prefixEnd_2475136 := by exact prefixLift 2475136
  have htrace : WordTrace (prefixWord ++ tailWord_2475136) baseStart_2475136 baseEnd_2475136 := by
    simpa [prefixWord, tailWord_2475136, baseEnd_2475136] using wordTrace_append hprefix tailTrace_2475136
  have hstable : (prefixWord ++ tailWord_2475136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475136).length < 2 ^ (prefixWord ++ tailWord_2475136).sum := by decide
  have hdescent : baseEnd_2475136 < baseStart_2475136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475140 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2475140 : Nat := 118140960795 + 2475140 * 2 ^ 59
def prefixEnd_2475140 : Nat := 4983230072969 + 3 ^ 40 * 2475140 * 2
def baseEnd_2475140 : Nat := 847291004779700824711363

theorem tailTrace_2475140 : CollatzResearch.WordTrace tailWord_2475140 prefixEnd_2475140 847291004779700824711363 := by
  unfold tailWord_2475140
  simp only [CollatzResearch.WordTrace]
  refine ⟨45137886126498987551315437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60183848168665316735087249 45137886126498987551315437)
  ·
    refine ⟨16926707297437120331743289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45137886126498987551315437 16926707297437120331743289)
    ·
      refine ⟨12695030473077840248807467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16926707297437120331743289 12695030473077840248807467)
      ·
        refine ⟨19042545709616760373211201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12695030473077840248807467 19042545709616760373211201)
        ·
          refine ⟨14281909282212570279908401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19042545709616760373211201 14281909282212570279908401)
          ·
            refine ⟨10711431961659427709931301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14281909282212570279908401 10711431961659427709931301)
            ·
              refine ⟨2008393492811142695612119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10711431961659427709931301 2008393492811142695612119)
              ·
                refine ⟨3012590239216714043418179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008393492811142695612119 3012590239216714043418179)
                ·
                  refine ⟨4518885358825071065127269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012590239216714043418179 4518885358825071065127269)
                  ·
                    refine ⟨847291004779700824711363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4518885358825071065127269 847291004779700824711363)
                    ·
                      rfl

theorem cell22_2475140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2475140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475140 prefixEnd_2475140 := by exact prefixLift 2475140
  have htrace : WordTrace (prefixWord ++ tailWord_2475140) baseStart_2475140 baseEnd_2475140 := by
    simpa [prefixWord, tailWord_2475140, baseEnd_2475140] using wordTrace_append hprefix tailTrace_2475140
  have hstable : (prefixWord ++ tailWord_2475140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475140).length < 2 ^ (prefixWord ++ tailWord_2475140).sum := by decide
  have hdescent : baseEnd_2475140 < baseStart_2475140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475206 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2475206 : Nat := 118140960795 + 2475206 * 2 ^ 59
def prefixEnd_2475206 : Nat := 4983230072969 + 3 ^ 40 * 2475206 * 2
def baseEnd_2475206 : Nat := 282437865976166217520387

theorem tailTrace_2475206 : CollatzResearch.WordTrace tailWord_2475206 prefixEnd_2475206 282437865976166217520387 := by
  unfold tailWord_2475206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821193108461214636704171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60185452980505912249688981 2821193108461214636704171)
  ·
    refine ⟨4231789662691821955056257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2821193108461214636704171 4231789662691821955056257)
    ·
      refine ⟨3173842247018866466292193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4231789662691821955056257 3173842247018866466292193)
      ·
        refine ⟨2380381685264149849719145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3173842247018866466292193 2380381685264149849719145)
        ·
          refine ⟨1785286263948112387289359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380381685264149849719145 1785286263948112387289359)
          ·
            refine ⟨2677929395922168580934039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785286263948112387289359 2677929395922168580934039)
            ·
              refine ⟨4016894093883252871401059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677929395922168580934039 4016894093883252871401059)
              ·
                refine ⟨6025341140824879307101589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4016894093883252871401059 6025341140824879307101589)
                ·
                  refine ⟨282437865976166217520387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6025341140824879307101589 282437865976166217520387)
                  ·
                    rfl

theorem cell22_2475206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2475206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475206 prefixEnd_2475206 := by exact prefixLift 2475206
  have htrace : WordTrace (prefixWord ++ tailWord_2475206) baseStart_2475206 baseEnd_2475206 := by
    simpa [prefixWord, tailWord_2475206, baseEnd_2475206] using wordTrace_append hprefix tailTrace_2475206
  have hstable : (prefixWord ++ tailWord_2475206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475206).length < 2 ^ (prefixWord ++ tailWord_2475206).sum := by decide
  have hdescent : baseEnd_2475206 < baseStart_2475206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475226 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_2475226 : Nat := 118140960795 + 2475226 * 2 ^ 59
def prefixEnd_2475226 : Nat := 4983230072969 + 3 ^ 40 * 2475226 * 2
def baseEnd_2475226 : Nat := 847320444337225267061099

theorem tailTrace_2475226 : CollatzResearch.WordTrace tailWord_2475226 prefixEnd_2475226 847320444337225267061099 := by
  unfold tailWord_2475226
  simp only [CollatzResearch.WordTrace]
  refine ⟨22569727232671602947565383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60185939287124274526841021 22569727232671602947565383)
  ·
    refine ⟨33854590849007404421348075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22569727232671602947565383 33854590849007404421348075)
    ·
      refine ⟨50781886273511106632022113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33854590849007404421348075 50781886273511106632022113)
      ·
        refine ⟨38086414705133329974016585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50781886273511106632022113 38086414705133329974016585)
        ·
          refine ⟨28564811028849997480512439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38086414705133329974016585 28564811028849997480512439)
          ·
            refine ⟨42847216543274996220768659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28564811028849997480512439 42847216543274996220768659)
            ·
              refine ⟨64270824814912494331152989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42847216543274996220768659 64270824814912494331152989)
              ·
                refine ⟨24101559305592185374182371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64270824814912494331152989 24101559305592185374182371)
                ·
                  refine ⟨36152338958388278061273557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24101559305592185374182371 36152338958388278061273557)
                  ·
                    refine ⟨847320444337225267061099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36152338958388278061273557 847320444337225267061099)
                    ·
                      rfl

theorem cell22_2475226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2475226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475226 prefixEnd_2475226 := by exact prefixLift 2475226
  have htrace : WordTrace (prefixWord ++ tailWord_2475226) baseStart_2475226 baseEnd_2475226 := by
    simpa [prefixWord, tailWord_2475226, baseEnd_2475226] using wordTrace_append hprefix tailTrace_2475226
  have hstable : (prefixWord ++ tailWord_2475226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475226).length < 2 ^ (prefixWord ++ tailWord_2475226).sum := by decide
  have hdescent : baseEnd_2475226 < baseStart_2475226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475288 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_2475288 : Nat := 118140960795 + 2475288 * 2 ^ 59
def prefixEnd_2475288 : Nat := 4983230072969 + 3 ^ 40 * 2475288 * 2
def baseEnd_2475288 : Nat := 847341668204277772010909

theorem tailTrace_2475288 : CollatzResearch.WordTrace tailWord_2475288 prefixEnd_2475288 847341668204277772010909 := by
  unfold tailWord_2475288
  simp only [CollatzResearch.WordTrace]
  refine ⟨45140585128230898189509259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60187446837641197586012345 45140585128230898189509259)
  ·
    refine ⟨67710877692346347284263889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45140585128230898189509259 67710877692346347284263889)
    ·
      refine ⟨50783158269259760463197917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67710877692346347284263889 50783158269259760463197917)
      ·
        refine ⟨19043684350972410173699219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50783158269259760463197917 19043684350972410173699219)
        ·
          refine ⟨28565526526458615260548829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19043684350972410173699219 28565526526458615260548829)
          ·
            refine ⟨10712072447421980722705811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28565526526458615260548829 10712072447421980722705811)
            ·
              refine ⟨16068108671132971084058717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10712072447421980722705811 16068108671132971084058717)
              ·
                refine ⟨6025540751674864156522019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16068108671132971084058717 6025540751674864156522019)
                ·
                  refine ⟨9038311127512296234783029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6025540751674864156522019 9038311127512296234783029)
                  ·
                    refine ⟨847341668204277772010909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9038311127512296234783029 847341668204277772010909)
                    ·
                      rfl

theorem cell22_2475288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_2475288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475288 prefixEnd_2475288 := by exact prefixLift 2475288
  have htrace : WordTrace (prefixWord ++ tailWord_2475288) baseStart_2475288 baseEnd_2475288 := by
    simpa [prefixWord, tailWord_2475288, baseEnd_2475288] using wordTrace_append hprefix tailTrace_2475288
  have hstable : (prefixWord ++ tailWord_2475288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475288).length < 2 ^ (prefixWord ++ tailWord_2475288).sum := by decide
  have hdescent : baseEnd_2475288 < baseStart_2475288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475309 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2475309 : Nat := 118140960795 + 2475309 * 2 ^ 59
def prefixEnd_2475309 : Nat := 4983230072969 + 3 ^ 40 * 2475309 * 2
def baseEnd_2475309 : Nat := 847348856933440717235845

theorem tailTrace_2475309 : CollatzResearch.WordTrace tailWord_2475309 prefixEnd_2475309 847348856933440717235845 := by
  unfold tailWord_2475309
  simp only [CollatzResearch.WordTrace]
  refine ⟨90281936189385716965532981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60187957459590477977021987 90281936189385716965532981)
  ·
    refine ⟨8463931517754910965518717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90281936189385716965532981 8463931517754910965518717)
    ·
      refine ⟨3173974319158091612069519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8463931517754910965518717 3173974319158091612069519)
      ·
        refine ⟨4760961478737137418104279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3173974319158091612069519 4760961478737137418104279)
        ·
          refine ⟨7141442218105706127156419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4760961478737137418104279 7141442218105706127156419)
          ·
            refine ⟨10712163327158559190734629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141442218105706127156419 10712163327158559190734629)
            ·
              refine ⟨2008530623842229848262743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10712163327158559190734629 2008530623842229848262743)
              ·
                refine ⟨3012795935763344772394115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008530623842229848262743 3012795935763344772394115)
                ·
                  refine ⟨4519193903645017158591173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012795935763344772394115 4519193903645017158591173)
                  ·
                    refine ⟨847348856933440717235845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519193903645017158591173 847348856933440717235845)
                    ·
                      rfl

theorem cell22_2475309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2475309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475309 prefixEnd_2475309 := by exact prefixLift 2475309
  have htrace : WordTrace (prefixWord ++ tailWord_2475309) baseStart_2475309 baseEnd_2475309 := by
    simpa [prefixWord, tailWord_2475309, baseEnd_2475309] using wordTrace_append hprefix tailTrace_2475309
  have hstable : (prefixWord ++ tailWord_2475309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475309).length < 2 ^ (prefixWord ++ tailWord_2475309).sum := by decide
  have hdescent : baseEnd_2475309 < baseStart_2475309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475363 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 7]
def baseStart_2475363 : Nat := 118140960795 + 2475363 * 2 ^ 59
def prefixEnd_2475363 : Nat := 4983230072969 + 3 ^ 40 * 2475363 * 2
def baseEnd_2475363 : Nat := 282455780745667525461893

theorem tailTrace_2475363 : CollatzResearch.WordTrace tailWord_2475363 prefixEnd_2475363 282455780745667525461893 := by
  unfold tailWord_2475363
  simp only [CollatzResearch.WordTrace]
  refine ⟨90283905731190084187998743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60189270487460056125332495 90283905731190084187998743)
  ·
    refine ⟨135425858596785126281998115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90283905731190084187998743 135425858596785126281998115)
    ·
      refine ⟨203138787895177689422997173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135425858596785126281998115 203138787895177689422997173)
      ·
        refine ⟨19044261365172908383405985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203138787895177689422997173 19044261365172908383405985)
        ·
          refine ⟨14283196023879681287554489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19044261365172908383405985 14283196023879681287554489)
          ·
            refine ⟨10712397017909760965665867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14283196023879681287554489 10712397017909760965665867)
            ·
              refine ⟨16068595526864641448498801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10712397017909760965665867 16068595526864641448498801)
              ·
                refine ⟨12051446645148481086374101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16068595526864641448498801 12051446645148481086374101)
                ·
                  refine ⟨282455780745667525461893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12051446645148481086374101 282455780745667525461893)
                  ·
                    rfl

theorem cell22_2475363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_2475363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475363 prefixEnd_2475363 := by exact prefixLift 2475363
  have htrace : WordTrace (prefixWord ++ tailWord_2475363) baseStart_2475363 baseEnd_2475363 := by
    simpa [prefixWord, tailWord_2475363, baseEnd_2475363] using wordTrace_append hprefix tailTrace_2475363
  have hstable : (prefixWord ++ tailWord_2475363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475363).length < 2 ^ (prefixWord ++ tailWord_2475363).sum := by decide
  have hdescent : baseEnd_2475363 < baseStart_2475363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475390 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2475390 : Nat := 118140960795 + 2475390 * 2 ^ 59
def prefixEnd_2475390 : Nat := 4983230072969 + 3 ^ 40 * 2475390 * 2
def baseEnd_2475390 : Nat := 847376584888783505960597

theorem tailTrace_2475390 : CollatzResearch.WordTrace tailWord_2475390 prefixEnd_2475390 847376584888783505960597 := by
  unfold tailWord_2475390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285611312761533474903953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60189927001394845199487749 11285611312761533474903953)
  ·
    refine ⟨8464208484571150106177965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11285611312761533474903953 8464208484571150106177965)
    ·
      refine ⟨3174078181714181289816737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8464208484571150106177965 3174078181714181289816737)
      ·
        refine ⟨2380558636285635967362553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3174078181714181289816737 2380558636285635967362553)
        ·
          refine ⟨1785418977214226975521915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380558636285635967362553 1785418977214226975521915)
          ·
            refine ⟨2678128465821340463282873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785418977214226975521915 2678128465821340463282873)
            ·
              refine ⟨2008596349366005347462155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678128465821340463282873 2008596349366005347462155)
              ·
                refine ⟨3012894524049008021193233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008596349366005347462155 3012894524049008021193233)
                ·
                  refine ⟨2259670893036756015894925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3012894524049008021193233 2259670893036756015894925)
                  ·
                    refine ⟨847376584888783505960597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259670893036756015894925 847376584888783505960597)
                    ·
                      rfl

theorem cell22_2475390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2475390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475390 prefixEnd_2475390 := by exact prefixLift 2475390
  have htrace : WordTrace (prefixWord ++ tailWord_2475390) baseStart_2475390 baseEnd_2475390 := by
    simpa [prefixWord, tailWord_2475390, baseEnd_2475390] using wordTrace_append hprefix tailTrace_2475390
  have hstable : (prefixWord ++ tailWord_2475390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475390).length < 2 ^ (prefixWord ++ tailWord_2475390).sum := by decide
  have hdescent : baseEnd_2475390 < baseStart_2475390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475427 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 1, 4]
def baseStart_2475427 : Nat := 118140960795 + 2475427 * 2 ^ 59
def prefixEnd_2475427 : Nat := 4983230072969 + 3 ^ 40 * 2475427 * 2
def baseEnd_2475427 : Nat := 847389250744927742785483

theorem tailTrace_2475427 : CollatzResearch.WordTrace tailWord_2475427 prefixEnd_2475427 847389250744927742785483 := by
  unfold tailWord_2475427
  simp only [CollatzResearch.WordTrace]
  refine ⟨90286240002958223118328535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60190826668638815412219023 90286240002958223118328535)
  ·
    refine ⟨135429360004437334677492803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90286240002958223118328535 135429360004437334677492803)
    ·
      refine ⟨203144040006656002016239205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135429360004437334677492803 203144040006656002016239205)
      ·
        refine ⟨38089507501248000378044851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203144040006656002016239205 38089507501248000378044851)
        ·
          refine ⟨57134261251872000567067277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38089507501248000378044851 57134261251872000567067277)
          ·
            refine ⟨21425347969452000212650229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57134261251872000567067277 21425347969452000212650229)
            ·
              refine ⟨2008626372136125019935959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21425347969452000212650229 2008626372136125019935959)
              ·
                refine ⟨3012939558204187529903939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008626372136125019935959 3012939558204187529903939)
                ·
                  refine ⟨4519409337306281294855909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012939558204187529903939 4519409337306281294855909)
                  ·
                    refine ⟨847389250744927742785483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519409337306281294855909 847389250744927742785483)
                    ·
                      rfl

theorem cell22_2475427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 4].length) (baseStart_2475427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475427 prefixEnd_2475427 := by exact prefixLift 2475427
  have htrace : WordTrace (prefixWord ++ tailWord_2475427) baseStart_2475427 baseEnd_2475427 := by
    simpa [prefixWord, tailWord_2475427, baseEnd_2475427] using wordTrace_append hprefix tailTrace_2475427
  have hstable : (prefixWord ++ tailWord_2475427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475427).length < 2 ^ (prefixWord ++ tailWord_2475427).sum := by decide
  have hdescent : baseEnd_2475427 < baseStart_2475427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475562 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2475562 : Nat := 118140960795 + 2475562 * 2 ^ 59
def prefixEnd_2475562 : Nat := 4983230072969 + 3 ^ 40 * 2475562 * 2
def baseEnd_2475562 : Nat := 847435464003832390660069

theorem tailTrace_2475562 : CollatzResearch.WordTrace tailWord_2475562 prefixEnd_2475562 847435464003832390660069 := by
  unfold tailWord_2475562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572790964367285293623235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60194109238312760782995293 22572790964367285293623235)
  ·
    refine ⟨33859186446550927940434853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22572790964367285293623235 33859186446550927940434853)
    ·
      refine ⟨6348597458728298988831535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33859186446550927940434853 6348597458728298988831535)
      ·
        refine ⟨9522896188092448483247303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6348597458728298988831535 9522896188092448483247303)
        ·
          refine ⟨14284344282138672724870955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9522896188092448483247303 14284344282138672724870955)
          ·
            refine ⟨21426516423208009087306433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14284344282138672724870955 21426516423208009087306433)
            ·
              refine ⟨16069887317406006815479825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21426516423208009087306433 16069887317406006815479825)
              ·
                refine ⟨12052415488054505111609869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16069887317406006815479825 12052415488054505111609869)
                ·
                  refine ⟨4519655808020439416853701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12052415488054505111609869 4519655808020439416853701)
                  ·
                    refine ⟨847435464003832390660069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519655808020439416853701 847435464003832390660069)
                    ·
                      rfl

theorem cell22_2475562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2475562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475562 prefixEnd_2475562 := by exact prefixLift 2475562
  have htrace : WordTrace (prefixWord ++ tailWord_2475562) baseStart_2475562 baseEnd_2475562 := by
    simpa [prefixWord, tailWord_2475562, baseEnd_2475562] using wordTrace_append hprefix tailTrace_2475562
  have hstable : (prefixWord ++ tailWord_2475562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475562).length < 2 ^ (prefixWord ++ tailWord_2475562).sum := by decide
  have hdescent : baseEnd_2475562 < baseStart_2475562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475566 : List Nat := [4, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_2475566 : Nat := 118140960795 + 2475566 * 2 ^ 59
def prefixEnd_2475566 : Nat := 4983230072969 + 3 ^ 40 * 2475566 * 2
def baseEnd_2475566 : Nat := 282478944428525904520019

theorem tailTrace_2475566 : CollatzResearch.WordTrace tailWord_2475566 prefixEnd_2475566 282478944428525904520019 := by
  unfold tailWord_2475566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11286413718681831232204819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60194206499636433238425701 11286413718681831232204819)
  ·
    refine ⟨16929620578022746848307229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11286413718681831232204819 16929620578022746848307229)
    ·
      refine ⟨6348607716758530068115211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16929620578022746848307229 6348607716758530068115211)
      ·
        refine ⟨9522911575137795102172817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6348607716758530068115211 9522911575137795102172817)
        ·
          refine ⟨7142183681353346326629613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9522911575137795102172817 7142183681353346326629613)
          ·
            refine ⟨2678318880507504872486105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7142183681353346326629613 2678318880507504872486105)
            ·
              refine ⟨2008739160380628654364579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678318880507504872486105 2008739160380628654364579)
              ·
                refine ⟨3013108740570942981546869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2008739160380628654364579 3013108740570942981546869)
                ·
                  refine ⟨282478944428525904520019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013108740570942981546869 282478944428525904520019)
                  ·
                    rfl

theorem cell22_2475566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_2475566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475566 prefixEnd_2475566 := by exact prefixLift 2475566
  have htrace : WordTrace (prefixWord ++ tailWord_2475566) baseStart_2475566 baseEnd_2475566 := by
    simpa [prefixWord, tailWord_2475566, baseEnd_2475566] using wordTrace_append hprefix tailTrace_2475566
  have hstable : (prefixWord ++ tailWord_2475566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475566).length < 2 ^ (prefixWord ++ tailWord_2475566).sum := by decide
  have hdescent : baseEnd_2475566 < baseStart_2475566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475607 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2475607 : Nat := 118140960795 + 2475607 * 2 ^ 59
def prefixEnd_2475607 : Nat := 4983230072969 + 3 ^ 40 * 2475607 * 2
def baseEnd_2475607 : Nat := 847450868423467273284931

theorem tailTrace_2475607 : CollatzResearch.WordTrace tailWord_2475607 prefixEnd_2475607 847450868423467273284931 := by
  unfold tailWord_2475607
  simp only [CollatzResearch.WordTrace]
  refine ⟨90292805142306113859881075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60195203428204075906587383 90292805142306113859881075)
  ·
    refine ⟨135439207713459170789821613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90292805142306113859881075 135439207713459170789821613)
    ·
      refine ⟨50789702892547189046183105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135439207713459170789821613 50789702892547189046183105)
      ·
        refine ⟨38092277169410391784637329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50789702892547189046183105 38092277169410391784637329)
        ·
          refine ⟨28569207877057793838477997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38092277169410391784637329 28569207877057793838477997)
          ·
            refine ⟨10713452953896672689429249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28569207877057793838477997 10713452953896672689429249)
            ·
              refine ⟨8035089715422504517071937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10713452953896672689429249 8035089715422504517071937)
              ·
                refine ⟨6026317286566878387803953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8035089715422504517071937 6026317286566878387803953)
                ·
                  refine ⟨4519737964925158790852965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026317286566878387803953 4519737964925158790852965)
                  ·
                    refine ⟨847450868423467273284931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4519737964925158790852965 847450868423467273284931)
                    ·
                      rfl

theorem cell22_2475607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2475607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475607 prefixEnd_2475607 := by exact prefixLift 2475607
  have htrace : WordTrace (prefixWord ++ tailWord_2475607) baseStart_2475607 baseEnd_2475607 := by
    simpa [prefixWord, tailWord_2475607, baseEnd_2475607] using wordTrace_append hprefix tailTrace_2475607
  have hstable : (prefixWord ++ tailWord_2475607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475607).length < 2 ^ (prefixWord ++ tailWord_2475607).sum := by decide
  have hdescent : baseEnd_2475607 < baseStart_2475607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475671 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 1, 3]
def baseStart_2475671 : Nat := 118140960795 + 2475671 * 2 ^ 59
def prefixEnd_2475671 : Nat := 4983230072969 + 3 ^ 40 * 2475671 * 2
def baseEnd_2475671 : Nat := 847472776931392439684735

theorem tailTrace_2475671 : CollatzResearch.WordTrace tailWord_2475671 prefixEnd_2475671 847472776931392439684735 := by
  unfold tailWord_2475671
  simp only [CollatzResearch.WordTrace]
  refine ⟨90295139414074252790210867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60196759609382835193473911 90295139414074252790210867)
  ·
    refine ⟨135442709121111379185316301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90295139414074252790210867 135442709121111379185316301)
    ·
      refine ⟨50791015920416767194493613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135442709121111379185316301 50791015920416767194493613)
      ·
        refine ⟨19046630970156287697935105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50791015920416767194493613 19046630970156287697935105)
        ·
          refine ⟨14284973227617215773451329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19046630970156287697935105 14284973227617215773451329)
          ·
            refine ⟨10713729920712911830088497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14284973227617215773451329 10713729920712911830088497)
            ·
              refine ⟨8035297440534683872566373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10713729920712911830088497 8035297440534683872566373)
              ·
                refine ⟨1506618270100253226106195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8035297440534683872566373 1506618270100253226106195)
                ·
                  refine ⟨2259927405150379839159293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506618270100253226106195 2259927405150379839159293)
                  ·
                    refine ⟨847472776931392439684735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2259927405150379839159293 847472776931392439684735)
                    ·
                      rfl

theorem cell22_2475671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_2475671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475671 prefixEnd_2475671 := by exact prefixLift 2475671
  have htrace : WordTrace (prefixWord ++ tailWord_2475671) baseStart_2475671 baseEnd_2475671 := by
    simpa [prefixWord, tailWord_2475671, baseEnd_2475671] using wordTrace_append hprefix tailTrace_2475671
  have hstable : (prefixWord ++ tailWord_2475671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475671).length < 2 ^ (prefixWord ++ tailWord_2475671).sum := by decide
  have hdescent : baseEnd_2475671 < baseStart_2475671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475729 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 6]
def baseStart_2475729 : Nat := 118140960795 + 2475729 * 2 ^ 59
def prefixEnd_2475729 : Nat := 4983230072969 + 3 ^ 40 * 2475729 * 2
def baseEnd_2475729 : Nat := 282497543838899873911519

theorem tailTrace_2475729 : CollatzResearch.WordTrace tailWord_2475729 prefixEnd_2475729 282497543838899873911519 := by
  unfold tailWord_2475729
  simp only [CollatzResearch.WordTrace]
  refine ⟨90297254847864128695822241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60198169898576085797214827 90297254847864128695822241)
  ·
    refine ⟨67722941135898096521866681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90297254847864128695822241 67722941135898096521866681)
    ·
      refine ⟨50792205851923572391400011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67722941135898096521866681 50792205851923572391400011)
      ·
        refine ⟨76188308777885358587100017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50792205851923572391400011 76188308777885358587100017)
        ·
          refine ⟨57141231583414018940325013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76188308777885358587100017 57141231583414018940325013)
          ·
            refine ⟨2678495230472532137827735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57141231583414018940325013 2678495230472532137827735)
            ·
              refine ⟨4017742845708798206741603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2678495230472532137827735 4017742845708798206741603)
              ·
                refine ⟨6026614268563197310112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017742845708798206741603 6026614268563197310112405)
                ·
                  refine ⟨282497543838899873911519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6026614268563197310112405 282497543838899873911519)
                  ·
                    rfl

theorem cell22_2475729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_2475729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475729 prefixEnd_2475729 := by exact prefixLift 2475729
  have htrace : WordTrace (prefixWord ++ tailWord_2475729) baseStart_2475729 baseEnd_2475729 := by
    simpa [prefixWord, tailWord_2475729, baseEnd_2475729] using wordTrace_append hprefix tailTrace_2475729
  have hstable : (prefixWord ++ tailWord_2475729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475729).length < 2 ^ (prefixWord ++ tailWord_2475729).sum := by decide
  have hdescent : baseEnd_2475729 < baseStart_2475729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475759 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 2, 4]
def baseStart_2475759 : Nat := 118140960795 + 2475759 * 2 ^ 59
def prefixEnd_2475759 : Nat := 4983230072969 + 3 ^ 40 * 2475759 * 2
def baseEnd_2475759 : Nat := 847502901129789543484465

theorem tailTrace_2475759 : CollatzResearch.WordTrace tailWord_2475759 prefixEnd_2475759 847502901129789543484465 := by
  unfold tailWord_2475759
  simp only [CollatzResearch.WordTrace]
  refine ⟨90298349037755443819414331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60198899358503629212942887 90298349037755443819414331)
  ·
    refine ⟨135447523556633165729121497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90298349037755443819414331 135447523556633165729121497)
    ·
      refine ⟨101585642667474874296841123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135447523556633165729121497 101585642667474874296841123)
      ·
        refine ⟨152378464001212311445261685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101585642667474874296841123 152378464001212311445261685)
        ·
          refine ⟨14285481000113654197993283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152378464001212311445261685 14285481000113654197993283)
          ·
            refine ⟨21428221500170481296989925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14285481000113654197993283 21428221500170481296989925)
            ·
              refine ⟨4017791531281965243185611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21428221500170481296989925 4017791531281965243185611)
              ·
                refine ⟨6026687296922947864778417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4017791531281965243185611 6026687296922947864778417)
                ·
                  refine ⟨4520015472692210898583813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6026687296922947864778417 4520015472692210898583813)
                  ·
                    refine ⟨847502901129789543484465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4520015472692210898583813 847502901129789543484465)
                    ·
                      rfl

theorem cell22_2475759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_2475759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475759 prefixEnd_2475759 := by exact prefixLift 2475759
  have htrace : WordTrace (prefixWord ++ tailWord_2475759) baseStart_2475759 baseEnd_2475759 := by
    simpa [prefixWord, tailWord_2475759, baseEnd_2475759] using wordTrace_append hprefix tailTrace_2475759
  have hstable : (prefixWord ++ tailWord_2475759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475759).length < 2 ^ (prefixWord ++ tailWord_2475759).sum := by decide
  have hdescent : baseEnd_2475759 < baseStart_2475759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475774 : List Nat := [4, 2, 2, 1, 3, 10]
def baseStart_2475774 : Nat := 118140960795 + 2475774 * 2 ^ 59
def prefixEnd_2475774 : Nat := 4983230072969 + 3 ^ 40 * 2475774 * 2
def baseEnd_2475774 : Nat := 10463062172053512399499

theorem tailTrace_2475774 : CollatzResearch.WordTrace tailWord_2475774 prefixEnd_2475774 10463062172053512399499 := by
  unfold tailWord_2475774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11287362016587637672651297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60199264088467400920806917 11287362016587637672651297)
  ·
    refine ⟨8465521512440728254488473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11287362016587637672651297 8465521512440728254488473)
    ·
      refine ⟨6349141134330546190866355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8465521512440728254488473 6349141134330546190866355)
      ·
        refine ⟨9523711701495819286299533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349141134330546190866355 9523711701495819286299533)
        ·
          refine ⟨3571391888060932232362325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9523711701495819286299533 3571391888060932232362325)
          ·
            refine ⟨10463062172053512399499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3571391888060932232362325 10463062172053512399499)
            ·
              rfl

theorem cell22_2475774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 10].length) (baseStart_2475774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475774 prefixEnd_2475774 := by exact prefixLift 2475774
  have htrace : WordTrace (prefixWord ++ tailWord_2475774) baseStart_2475774 baseEnd_2475774 := by
    simpa [prefixWord, tailWord_2475774, baseEnd_2475774] using wordTrace_append hprefix tailTrace_2475774
  have hstable : (prefixWord ++ tailWord_2475774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475774).length < 2 ^ (prefixWord ++ tailWord_2475774).sum := by decide
  have hdescent : baseEnd_2475774 < baseStart_2475774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475778 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2475778 : Nat := 118140960795 + 2475778 * 2 ^ 59
def prefixEnd_2475778 : Nat := 4983230072969 + 3 ^ 40 * 2475778 * 2
def baseEnd_2475778 : Nat := 847509405218079827259407

theorem tailTrace_2475778 : CollatzResearch.WordTrace tailWord_2475778 prefixEnd_2475778 847509405218079827259407 := by
  unfold tailWord_2475778
  simp only [CollatzResearch.WordTrace]
  refine ⟨22574760506171652516088997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60199361349791073376237325 22574760506171652516088997)
  ·
    refine ⟨4232767594907184846766687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22574760506171652516088997 4232767594907184846766687)
    ·
      refine ⟨6349151392360777270150031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4232767594907184846766687 6349151392360777270150031)
      ·
        refine ⟨9523727088541165905225047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349151392360777270150031 9523727088541165905225047)
        ·
          refine ⟨14285590632811748857837571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9523727088541165905225047 14285590632811748857837571)
          ·
            refine ⟨21428385949217623286756357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14285590632811748857837571 21428385949217623286756357)
            ·
              refine ⟨4017822365478304366266817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21428385949217623286756357 4017822365478304366266817)
              ·
                refine ⟨3013366774108728274700113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4017822365478304366266817 3013366774108728274700113)
                ·
                  refine ⟨2260025080581546206025085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3013366774108728274700113 2260025080581546206025085)
                  ·
                    refine ⟨847509405218079827259407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260025080581546206025085 847509405218079827259407)
                    ·
                      rfl

theorem cell22_2475778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2475778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475778 prefixEnd_2475778 := by exact prefixLift 2475778
  have htrace : WordTrace (prefixWord ++ tailWord_2475778) baseStart_2475778 baseEnd_2475778 := by
    simpa [prefixWord, tailWord_2475778, baseEnd_2475778] using wordTrace_append hprefix tailTrace_2475778
  have hstable : (prefixWord ++ tailWord_2475778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475778).length < 2 ^ (prefixWord ++ tailWord_2475778).sum := by decide
  have hdescent : baseEnd_2475778 < baseStart_2475778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475787 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_2475787 : Nat := 118140960795 + 2475787 * 2 ^ 59
def prefixEnd_2475787 : Nat := 4983230072969 + 3 ^ 40 * 2475787 * 2
def baseEnd_2475787 : Nat := 847512486102006803784379

theorem tailTrace_2475787 : CollatzResearch.WordTrace tailWord_2475787 prefixEnd_2475787 847512486102006803784379 := by
  unfold tailWord_2475787
  simp only [CollatzResearch.WordTrace]
  refine ⟨90299370281654004601433615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60199580187769336400955743 90299370281654004601433615)
  ·
    refine ⟨135449055422481006902150423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90299370281654004601433615 135449055422481006902150423)
    ·
      refine ⟨203173583133721510353225635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135449055422481006902150423 203173583133721510353225635)
      ·
        refine ⟨304760374700582265529838453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203173583133721510353225635 304760374700582265529838453)
        ·
          refine ⟨28571285128179587393422355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 304760374700582265529838453 28571285128179587393422355)
          ·
            refine ⟨42856927692269381090133533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28571285128179587393422355 42856927692269381090133533)
            ·
              refine ⟨16071347884601017908800075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42856927692269381090133533 16071347884601017908800075)
              ·
                refine ⟨24107021826901526863200113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16071347884601017908800075 24107021826901526863200113)
                ·
                  refine ⟨18080266370176145147400085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24107021826901526863200113 18080266370176145147400085)
                  ·
                    refine ⟨847512486102006803784379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18080266370176145147400085 847512486102006803784379)
                    ·
                      rfl

theorem cell22_2475787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_2475787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475787 prefixEnd_2475787 := by exact prefixLift 2475787
  have htrace : WordTrace (prefixWord ++ tailWord_2475787) baseStart_2475787 baseEnd_2475787 := by
    simpa [prefixWord, tailWord_2475787, baseEnd_2475787] using wordTrace_append hprefix tailTrace_2475787
  have hstable : (prefixWord ++ tailWord_2475787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475787).length < 2 ^ (prefixWord ++ tailWord_2475787).sum := by decide
  have hdescent : baseEnd_2475787 < baseStart_2475787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2475817 : Nat := 118140960795 + 2475817 * 2 ^ 59
def prefixEnd_2475817 : Nat := 4983230072969 + 3 ^ 40 * 2475817 * 2
def baseEnd_2475817 : Nat := 847522755715096725534287

theorem tailTrace_2475817 : CollatzResearch.WordTrace tailWord_2475817 prefixEnd_2475817 847522755715096725534287 := by
  unfold tailWord_2475817
  simp only [CollatzResearch.WordTrace]
  refine ⟨90300464471545319725025705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60200309647696879816683803 90300464471545319725025705)
  ·
    refine ⟨67725348353658989793769279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90300464471545319725025705 67725348353658989793769279)
    ·
      refine ⟨101588022530488484690653919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67725348353658989793769279 101588022530488484690653919)
      ·
        refine ⟨152382033795732727035980879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101588022530488484690653919 152382033795732727035980879)
        ·
          refine ⟨228573050693599090553971319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152382033795732727035980879 228573050693599090553971319)
          ·
            refine ⟨342859576040398635830956979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228573050693599090553971319 342859576040398635830956979)
            ·
              refine ⟨514289364060597953746435469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342859576040398635830956979 514289364060597953746435469)
              ·
                refine ⟨192858511522724232654913301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 514289364060597953746435469 192858511522724232654913301)
                ·
                  refine ⟨9040242727627698405699061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 192858511522724232654913301 9040242727627698405699061)
                  ·
                    refine ⟨847522755715096725534287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9040242727627698405699061 847522755715096725534287)
                    ·
                      rfl

theorem cell22_2475817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2475817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475817 prefixEnd_2475817 := by exact prefixLift 2475817
  have htrace : WordTrace (prefixWord ++ tailWord_2475817) baseStart_2475817 baseEnd_2475817 := by
    simpa [prefixWord, tailWord_2475817, baseEnd_2475817] using wordTrace_append hprefix tailTrace_2475817
  have hstable : (prefixWord ++ tailWord_2475817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475817).length < 2 ^ (prefixWord ++ tailWord_2475817).sum := by decide
  have hdescent : baseEnd_2475817 < baseStart_2475817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475834 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_2475834 : Nat := 118140960795 + 2475834 * 2 ^ 59
def prefixEnd_2475834 : Nat := 4983230072969 + 3 ^ 40 * 2475834 * 2
def baseEnd_2475834 : Nat := 847528575162514347859235

theorem tailTrace_2475834 : CollatzResearch.WordTrace tailWord_2475834 prefixEnd_2475834 847528575162514347859235 := by
  unfold tailWord_2475834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575271128120932907098639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60200723008322487752263037 22575271128120932907098639)
  ·
    refine ⟨33862906692181399360647959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22575271128120932907098639 33862906692181399360647959)
    ·
      refine ⟨50794360038272099040971939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33862906692181399360647959 50794360038272099040971939)
      ·
        refine ⟨76191540057408148561457909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50794360038272099040971939 76191540057408148561457909)
        ·
          refine ⟨7142956880382013927636679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76191540057408148561457909 7142956880382013927636679)
          ·
            refine ⟨10714435320573020891455019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7142956880382013927636679 10714435320573020891455019)
            ·
              refine ⟨16071652980859531337182529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10714435320573020891455019 16071652980859531337182529)
              ·
                refine ⟨12053739735644648502886897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16071652980859531337182529 12053739735644648502886897)
                ·
                  refine ⟨9040304801733486377165173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12053739735644648502886897 9040304801733486377165173)
                  ·
                    refine ⟨847528575162514347859235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9040304801733486377165173 847528575162514347859235)
                    ·
                      rfl

theorem cell22_2475834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_2475834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475834 prefixEnd_2475834 := by exact prefixLift 2475834
  have htrace : WordTrace (prefixWord ++ tailWord_2475834) baseStart_2475834 baseEnd_2475834 := by
    simpa [prefixWord, tailWord_2475834, baseEnd_2475834] using wordTrace_append hprefix tailTrace_2475834
  have hstable : (prefixWord ++ tailWord_2475834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475834).length < 2 ^ (prefixWord ++ tailWord_2475834).sum := by decide
  have hdescent : baseEnd_2475834 < baseStart_2475834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475866 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_2475866 : Nat := 118140960795 + 2475866 * 2 ^ 59
def prefixEnd_2475866 : Nat := 4983230072969 + 3 ^ 40 * 2475866 * 2
def baseEnd_2475866 : Nat := 847539529416476931059137

theorem tailTrace_2475866 : CollatzResearch.WordTrace tailWord_2475866 prefixEnd_2475866 847539529416476931059137 := by
  unfold tailWord_2475866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575562912091950273389863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60201501098911867395706301 22575562912091950273389863)
  ·
    refine ⟨33863344368137925410084795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22575562912091950273389863 33863344368137925410084795)
    ·
      refine ⟨50795016552206888115127193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33863344368137925410084795 50795016552206888115127193)
      ·
        refine ⟨38096262414155166086345395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50795016552206888115127193 38096262414155166086345395)
        ·
          refine ⟨57144393621232749129518093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38096262414155166086345395 57144393621232749129518093)
          ·
            refine ⟨21429147607962280923569285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57144393621232749129518093 21429147607962280923569285)
            ·
              refine ⟨4017965176492927673169241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21429147607962280923569285 4017965176492927673169241)
              ·
                refine ⟨3013473882369695754876931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4017965176492927673169241 3013473882369695754876931)
                ·
                  refine ⟨4520210823554543632315397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013473882369695754876931 4520210823554543632315397)
                  ·
                    refine ⟨847539529416476931059137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4520210823554543632315397 847539529416476931059137)
                    ·
                      rfl

theorem cell22_2475866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_2475866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475866 prefixEnd_2475866 := by exact prefixLift 2475866
  have htrace : WordTrace (prefixWord ++ tailWord_2475866) baseStart_2475866 baseEnd_2475866 := by
    simpa [prefixWord, tailWord_2475866, baseEnd_2475866] using wordTrace_append hprefix tailTrace_2475866
  have hstable : (prefixWord ++ tailWord_2475866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475866).length < 2 ^ (prefixWord ++ tailWord_2475866).sum := by decide
  have hdescent : baseEnd_2475866 < baseStart_2475866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475879 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2475879 : Nat := 118140960795 + 2475879 * 2 ^ 59
def prefixEnd_2475879 : Nat := 4983230072969 + 3 ^ 40 * 2475879 * 2
def baseEnd_2475879 : Nat := 847543979582149230484097

theorem tailTrace_2475879 : CollatzResearch.WordTrace tailWord_2475879 prefixEnd_2475879 847543979582149230484097 := by
  unfold tailWord_2475879
  simp only [CollatzResearch.WordTrace]
  refine ⟨90302725797320704313782691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60201817198213802875855127 90302725797320704313782691)
  ·
    refine ⟨135454088695981056470674037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90302725797320704313782691 135454088695981056470674037)
    ·
      refine ⟨12698820815248224044125691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135454088695981056470674037 12698820815248224044125691)
      ·
        refine ⟨19048231222872336066188537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12698820815248224044125691 19048231222872336066188537)
        ·
          refine ⟨14286173417154252049641403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19048231222872336066188537 14286173417154252049641403)
          ·
            refine ⟨21429260125731378074462105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14286173417154252049641403 21429260125731378074462105)
            ·
              refine ⟨16071945094298533555846579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21429260125731378074462105 16071945094298533555846579)
              ·
                refine ⟨24107917641447800333769869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16071945094298533555846579 24107917641447800333769869)
                ·
                  refine ⟨9040469115542925125163701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24107917641447800333769869 9040469115542925125163701)
                  ·
                    refine ⟨847543979582149230484097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9040469115542925125163701 847543979582149230484097)
                    ·
                      rfl

theorem cell22_2475879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2475879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475879 prefixEnd_2475879 := by exact prefixLift 2475879
  have htrace : WordTrace (prefixWord ++ tailWord_2475879) baseStart_2475879 baseEnd_2475879 := by
    simpa [prefixWord, tailWord_2475879, baseEnd_2475879] using wordTrace_append hprefix tailTrace_2475879
  have hstable : (prefixWord ++ tailWord_2475879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475879).length < 2 ^ (prefixWord ++ tailWord_2475879).sum := by decide
  have hdescent : baseEnd_2475879 < baseStart_2475879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475909 : List Nat := [1, 3, 1, 1, 3, 2, 4, 7]
def baseStart_2475909 : Nat := 118140960795 + 2475909 * 2 ^ 59
def prefixEnd_2475909 : Nat := 4983230072969 + 3 ^ 40 * 2475909 * 2
def baseEnd_2475909 : Nat := 94172694355026572470445

theorem tailTrace_2475909 : CollatzResearch.WordTrace tailWord_2475909 prefixEnd_2475909 94172694355026572470445 := by
  unfold tailWord_2475909
  simp only [CollatzResearch.WordTrace]
  refine ⟨90303819987212019437374781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60202546658141346291583187 90303819987212019437374781)
  ·
    refine ⟨33863932495204507289015543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90303819987212019437374781 33863932495204507289015543)
    ·
      refine ⟨50795898742806760933523315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33863932495204507289015543 50795898742806760933523315)
      ·
        refine ⟨76193848114210141400284973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50795898742806760933523315 76193848114210141400284973)
        ·
          refine ⟨28572693042828803025106865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76193848114210141400284973 28572693042828803025106865)
          ·
            refine ⟨21429519782121602268830149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28572693042828803025106865 21429519782121602268830149)
            ·
              refine ⟨4018034959147800425405653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21429519782121602268830149 4018034959147800425405653)
              ·
                refine ⟨94172694355026572470445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4018034959147800425405653 94172694355026572470445)
                ·
                  rfl

theorem cell22_2475909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 7].length) (baseStart_2475909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475909 prefixEnd_2475909 := by exact prefixLift 2475909
  have htrace : WordTrace (prefixWord ++ tailWord_2475909) baseStart_2475909 baseEnd_2475909 := by
    simpa [prefixWord, tailWord_2475909, baseEnd_2475909] using wordTrace_append hprefix tailTrace_2475909
  have hstable : (prefixWord ++ tailWord_2475909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475909).length < 2 ^ (prefixWord ++ tailWord_2475909).sum := by decide
  have hdescent : baseEnd_2475909 < baseStart_2475909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2475954 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_2475954 : Nat := 118140960795 + 2475954 * 2 ^ 59
def prefixEnd_2475954 : Nat := 4983230072969 + 3 ^ 40 * 2475954 * 2
def baseEnd_2475954 : Nat := 282523217871624678286289

theorem tailTrace_2475954 : CollatzResearch.WordTrace tailWord_2475954 prefixEnd_2475954 282523217871624678286289 := by
  unfold tailWord_2475954
  simp only [CollatzResearch.WordTrace]
  refine ⟨22576365318012248030690729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60203640848032661415175277 22576365318012248030690729)
  ·
    refine ⟨16932273988509186023018047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22576365318012248030690729 16932273988509186023018047)
    ·
      refine ⟨25398410982763779034527071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16932273988509186023018047 25398410982763779034527071)
      ·
        refine ⟨38097616474145668551790607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25398410982763779034527071 38097616474145668551790607)
        ·
          refine ⟨57146424711218502827685911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38097616474145668551790607 57146424711218502827685911)
          ·
            refine ⟨85719637066827754241528867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57146424711218502827685911 85719637066827754241528867)
            ·
              refine ⟨128579455600241631362293301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85719637066827754241528867 128579455600241631362293301)
              ·
                refine ⟨12054323962522652940214997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128579455600241631362293301 12054323962522652940214997)
                ·
                  refine ⟨282523217871624678286289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12054323962522652940214997 282523217871624678286289)
                  ·
                    rfl

theorem cell22_2475954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_2475954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2475954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2475954 prefixEnd_2475954 := by exact prefixLift 2475954
  have htrace : WordTrace (prefixWord ++ tailWord_2475954) baseStart_2475954 baseEnd_2475954 := by
    simpa [prefixWord, tailWord_2475954, baseEnd_2475954] using wordTrace_append hprefix tailTrace_2475954
  have hstable : (prefixWord ++ tailWord_2475954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2475954).length < 2 ^ (prefixWord ++ tailWord_2475954).sum := by decide
  have hdescent : baseEnd_2475954 < baseStart_2475954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2475954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476046 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2476046 : Nat := 118140960795 + 2476046 * 2 ^ 59
def prefixEnd_2476046 : Nat := 4983230072969 + 3 ^ 40 * 2476046 * 2
def baseEnd_2476046 : Nat := 847601147095016461558585

theorem tailTrace_2476046 : CollatzResearch.WordTrace tailWord_2476046 prefixEnd_2476046 847601147095016461558585 := by
  unfold tailWord_2476046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288602098464461479388999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60205877858477127890074661 11288602098464461479388999)
  ·
    refine ⟨16932903147696692219083499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11288602098464461479388999 16932903147696692219083499)
    ·
      refine ⟨25399354721545038328625249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16932903147696692219083499 25399354721545038328625249)
      ·
        refine ⟨19049516041158778746468937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25399354721545038328625249 19049516041158778746468937)
        ·
          refine ⟨14287137030869084059851703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19049516041158778746468937 14287137030869084059851703)
          ·
            refine ⟨21430705546303626089777555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14287137030869084059851703 21430705546303626089777555)
            ·
              refine ⟨32146058319455439134666333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21430705546303626089777555 32146058319455439134666333)
              ·
                refine ⟨12054771869795789675499875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32146058319455439134666333 12054771869795789675499875)
                ·
                  refine ⟨18082157804693684513249813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12054771869795789675499875 18082157804693684513249813)
                  ·
                    refine ⟨847601147095016461558585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18082157804693684513249813 847601147095016461558585)
                    ·
                      rfl

theorem cell22_2476046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2476046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476046 prefixEnd_2476046 := by exact prefixLift 2476046
  have htrace : WordTrace (prefixWord ++ tailWord_2476046) baseStart_2476046 baseEnd_2476046 := by
    simpa [prefixWord, tailWord_2476046, baseEnd_2476046] using wordTrace_append hprefix tailTrace_2476046
  have hstable : (prefixWord ++ tailWord_2476046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476046).length < 2 ^ (prefixWord ++ tailWord_2476046).sum := by decide
  have hdescent : baseEnd_2476046 < baseStart_2476046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476061 : List Nat := [1, 4, 2, 2, 2, 1, 10]
def baseStart_2476061 : Nat := 118140960795 + 2476061 * 2 ^ 59
def prefixEnd_2476061 : Nat := 4983230072969 + 3 ^ 40 * 2476061 * 2
def baseEnd_2476061 : Nat := 31392825255613386016057

theorem tailTrace_2476061 : CollatzResearch.WordTrace tailWord_2476061 prefixEnd_2476061 31392825255613386016057 := by
  unfold tailWord_2476061
  simp only [CollatzResearch.WordTrace]
  refine ⟨90309363882661349396908037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60206242588440899597938691 90309363882661349396908037)
  ·
    refine ⟨16933005727999003011920257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90309363882661349396908037 16933005727999003011920257)
    ·
      refine ⟨12699754295999252258940193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16933005727999003011920257 12699754295999252258940193)
      ·
        refine ⟨9524815721999439194205145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12699754295999252258940193 9524815721999439194205145)
        ·
          refine ⟨7143611791499579395653859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9524815721999439194205145 7143611791499579395653859)
          ·
            refine ⟨10715417687249369093480789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143611791499579395653859 10715417687249369093480789)
            ·
              refine ⟨31392825255613386016057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10715417687249369093480789 31392825255613386016057)
              ·
                rfl

theorem cell22_2476061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 10].length) (baseStart_2476061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476061 prefixEnd_2476061 := by exact prefixLift 2476061
  have htrace : WordTrace (prefixWord ++ tailWord_2476061) baseStart_2476061 baseEnd_2476061 := by
    simpa [prefixWord, tailWord_2476061, baseEnd_2476061] using wordTrace_append hprefix tailTrace_2476061
  have hstable : (prefixWord ++ tailWord_2476061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476061).length < 2 ^ (prefixWord ++ tailWord_2476061).sum := by decide
  have hdescent : baseEnd_2476061 < baseStart_2476061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476078 : List Nat := [4, 1, 3, 1, 1, 3, 2, 7]
def baseStart_2476078 : Nat := 118140960795 + 2476078 * 2 ^ 59
def prefixEnd_2476078 : Nat := 4983230072969 + 3 ^ 40 * 2476078 * 2
def baseEnd_2476078 : Nat := 94179122372108782750943

theorem tailTrace_2476078 : CollatzResearch.WordTrace tailWord_2476078 prefixEnd_2476078 94179122372108782750943 := by
  unfold tailWord_2476078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288747990449970162534611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60206655949066507533517925 11288747990449970162534611)
  ·
    refine ⟨16933121985674955243801917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11288747990449970162534611 16933121985674955243801917)
    ·
      refine ⟨6349920744628108216425719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16933121985674955243801917 6349920744628108216425719)
      ·
        refine ⟨9524881116942162324638579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349920744628108216425719 9524881116942162324638579)
        ·
          refine ⟨14287321675413243486957869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524881116942162324638579 14287321675413243486957869)
          ·
            refine ⟨5357745628279966307609201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14287321675413243486957869 5357745628279966307609201)
            ·
              refine ⟨4018309221209974730706901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5357745628279966307609201 4018309221209974730706901)
              ·
                refine ⟨94179122372108782750943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4018309221209974730706901 94179122372108782750943)
                ·
                  rfl

theorem cell22_2476078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_2476078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476078 prefixEnd_2476078 := by exact prefixLift 2476078
  have htrace : WordTrace (prefixWord ++ tailWord_2476078) baseStart_2476078 baseEnd_2476078 := by
    simpa [prefixWord, tailWord_2476078, baseEnd_2476078] using wordTrace_append hprefix tailTrace_2476078
  have hstable : (prefixWord ++ tailWord_2476078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476078).length < 2 ^ (prefixWord ++ tailWord_2476078).sum := by decide
  have hdescent : baseEnd_2476078 < baseStart_2476078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476082 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_2476082 : Nat := 118140960795 + 2476082 * 2 ^ 59
def prefixEnd_2476082 : Nat := 4983230072969 + 3 ^ 40 * 2476082 * 2
def baseEnd_2476082 : Nat := 847613470630724367658475

theorem tailTrace_2476082 : CollatzResearch.WordTrace tailWord_2476082 prefixEnd_2476082 847613470630724367658475 := by
  unfold tailWord_2476082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22577532453896317495855625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60206753210390179988948333 22577532453896317495855625)
  ·
    refine ⟨16933149340422238121891719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22577532453896317495855625 16933149340422238121891719)
    ·
      refine ⟨25399724010633357182837579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16933149340422238121891719 25399724010633357182837579)
      ·
        refine ⟨38099586015950035774256369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25399724010633357182837579 38099586015950035774256369)
        ·
          refine ⟨28574689511962526830692277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38099586015950035774256369 28574689511962526830692277)
          ·
            refine ⟨2678877141746486890377401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28574689511962526830692277 2678877141746486890377401)
            ·
              refine ⟨2009157856309865167783051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678877141746486890377401 2009157856309865167783051)
              ·
                refine ⟨3013736784464797751674577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009157856309865167783051 3013736784464797751674577)
                ·
                  refine ⟨2260302588348598313755933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3013736784464797751674577 2260302588348598313755933)
                  ·
                    refine ⟨847613470630724367658475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260302588348598313755933 847613470630724367658475)
                    ·
                      rfl

theorem cell22_2476082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_2476082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476082 prefixEnd_2476082 := by exact prefixLift 2476082
  have htrace : WordTrace (prefixWord ++ tailWord_2476082) baseStart_2476082 baseEnd_2476082 := by
    simpa [prefixWord, tailWord_2476082, baseEnd_2476082] using wordTrace_append hprefix tailTrace_2476082
  have hstable : (prefixWord ++ tailWord_2476082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476082).length < 2 ^ (prefixWord ++ tailWord_2476082).sum := by decide
  have hdescent : baseEnd_2476082 < baseStart_2476082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476093 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_2476093 : Nat := 118140960795 + 2476093 * 2 ^ 59
def prefixEnd_2476093 : Nat := 4983230072969 + 3 ^ 40 * 2476093 * 2
def baseEnd_2476093 : Nat := 847617236155524005633441

theorem tailTrace_2476093 : CollatzResearch.WordTrace tailWord_2476093 prefixEnd_2476093 847617236155524005633441 := by
  unfold tailWord_2476093
  simp only [CollatzResearch.WordTrace]
  refine ⟨90310531018545418862072933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60207020679030279241381955 90310531018545418862072933)
  ·
    refine ⟨16933224565977266036638675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90310531018545418862072933 16933224565977266036638675)
    ·
      refine ⟨25399836848965899054958013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16933224565977266036638675 25399836848965899054958013)
      ·
        refine ⟨9524938818362212145609255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25399836848965899054958013 9524938818362212145609255)
        ·
          refine ⟨14287408227543318218413883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524938818362212145609255 14287408227543318218413883)
          ·
            refine ⟨21431112341314977327620825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14287408227543318218413883 21431112341314977327620825)
            ·
              refine ⟨16073334255986232995715619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21431112341314977327620825 16073334255986232995715619)
              ·
                refine ⟨24110001383979349493573429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16073334255986232995715619 24110001383979349493573429)
                ·
                  refine ⟨2260312629748064015022509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24110001383979349493573429 2260312629748064015022509)
                  ·
                    refine ⟨847617236155524005633441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260312629748064015022509 847617236155524005633441)
                    ·
                      rfl

theorem cell22_2476093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_2476093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476093 prefixEnd_2476093 := by exact prefixLift 2476093
  have htrace : WordTrace (prefixWord ++ tailWord_2476093) baseStart_2476093 baseEnd_2476093 := by
    simpa [prefixWord, tailWord_2476093, baseEnd_2476093] using wordTrace_append hprefix tailTrace_2476093
  have hstable : (prefixWord ++ tailWord_2476093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476093).length < 2 ^ (prefixWord ++ tailWord_2476093).sum := by decide
  have hdescent : baseEnd_2476093 < baseStart_2476093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476121 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_2476121 : Nat := 118140960795 + 2476121 * 2 ^ 59
def prefixEnd_2476121 : Nat := 4983230072969 + 3 ^ 40 * 2476121 * 2
def baseEnd_2476121 : Nat := 847626821127741265933355

theorem tailTrace_2476121 : CollatzResearch.WordTrace tailWord_2476121 prefixEnd_2476121 847626821127741265933355 := by
  unfold tailWord_2476121
  simp only [CollatzResearch.WordTrace]
  refine ⟨90311552262443979644092217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60207701508295986429394811 90311552262443979644092217)
  ·
    refine ⟨67733664196832984733069163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90311552262443979644092217 67733664196832984733069163)
    ·
      refine ⟨101600496295249477099603745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67733664196832984733069163 101600496295249477099603745)
      ·
        refine ⟨76200372221437107824702809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101600496295249477099603745 76200372221437107824702809)
        ·
          refine ⟨57150279166077830868527107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76200372221437107824702809 57150279166077830868527107)
          ·
            refine ⟨85725418749116746302790661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57150279166077830868527107 85725418749116746302790661)
            ·
              refine ⟨16073516015459389931773249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85725418749116746302790661 16073516015459389931773249)
              ·
                refine ⟨12055137011594542448829937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16073516015459389931773249 12055137011594542448829937)
                ·
                  refine ⟨9041352758695906836622453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12055137011594542448829937 9041352758695906836622453)
                  ·
                    refine ⟨847626821127741265933355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9041352758695906836622453 847626821127741265933355)
                    ·
                      rfl

theorem cell22_2476121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_2476121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476121 prefixEnd_2476121 := by exact prefixLift 2476121
  have htrace : WordTrace (prefixWord ++ tailWord_2476121) baseStart_2476121 baseEnd_2476121 := by
    simpa [prefixWord, tailWord_2476121, baseEnd_2476121] using wordTrace_append hprefix tailTrace_2476121
  have hstable : (prefixWord ++ tailWord_2476121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476121).length < 2 ^ (prefixWord ++ tailWord_2476121).sum := by decide
  have hdescent : baseEnd_2476121 < baseStart_2476121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476151 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 8]
def baseStart_2476151 : Nat := 118140960795 + 2476151 * 2 ^ 59
def prefixEnd_2476151 : Nat := 4983230072969 + 3 ^ 40 * 2476151 * 2
def baseEnd_2476151 : Nat := 282545696913610395894421

theorem tailTrace_2476151 : CollatzResearch.WordTrace tailWord_2476151 prefixEnd_2476151 282545696913610395894421 := by
  unfold tailWord_2476151
  simp only [CollatzResearch.WordTrace]
  refine ⟨90312646452335294767684307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60208430968223529845122871 90312646452335294767684307)
  ·
    refine ⟨135468969678502942151526461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90312646452335294767684307 135468969678502942151526461)
    ·
      refine ⟨50800863629438603306822423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135468969678502942151526461 50800863629438603306822423)
      ·
        refine ⟨76201295444157904960233635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50800863629438603306822423 76201295444157904960233635)
        ·
          refine ⟨114301943166236857440350453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76201295444157904960233635 114301943166236857440350453)
          ·
            refine ⟨10715807171834705385032855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114301943166236857440350453 10715807171834705385032855)
            ·
              refine ⟨16073710757752058077549283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715807171834705385032855 16073710757752058077549283)
              ·
                refine ⟨24110566136628087116323925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16073710757752058077549283 24110566136628087116323925)
                ·
                  refine ⟨282545696913610395894421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24110566136628087116323925 282545696913610395894421)
                  ·
                    rfl

theorem cell22_2476151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_2476151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476151 prefixEnd_2476151 := by exact prefixLift 2476151
  have htrace : WordTrace (prefixWord ++ tailWord_2476151) baseStart_2476151 baseEnd_2476151 := by
    simpa [prefixWord, tailWord_2476151, baseEnd_2476151] using wordTrace_append hprefix tailTrace_2476151
  have hstable : (prefixWord ++ tailWord_2476151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476151).length < 2 ^ (prefixWord ++ tailWord_2476151).sum := by decide
  have hdescent : baseEnd_2476151 < baseStart_2476151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476153 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_2476153 : Nat := 118140960795 + 2476153 * 2 ^ 59
def prefixEnd_2476153 : Nat := 4983230072969 + 3 ^ 40 * 2476153 * 2
def baseEnd_2476153 : Nat := 847637775381703849133257

theorem tailTrace_2476153 : CollatzResearch.WordTrace tailWord_2476153 prefixEnd_2476153 847637775381703849133257 := by
  unfold tailWord_2476153
  simp only [CollatzResearch.WordTrace]
  refine ⟨90312719398328049109257113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60208479598885366072838075 90312719398328049109257113)
  ·
    refine ⟨67734539548746036831942835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90312719398328049109257113 67734539548746036831942835)
    ·
      refine ⟨101601809323119055247914253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67734539548746036831942835 101601809323119055247914253)
      ·
        refine ⟨38100678496169645717967845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101601809323119055247914253 38100678496169645717967845)
        ·
          refine ⟨7143877218031808572118971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38100678496169645717967845 7143877218031808572118971)
          ·
            refine ⟨10715815827047712858178457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143877218031808572118971 10715815827047712858178457)
            ·
              refine ⟨8036861870285784643633843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10715815827047712858178457 8036861870285784643633843)
              ·
                refine ⟨12055292805428676965450765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036861870285784643633843 12055292805428676965450765)
                ·
                  refine ⟨4520734802035753862044037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12055292805428676965450765 4520734802035753862044037)
                  ·
                    refine ⟨847637775381703849133257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4520734802035753862044037 847637775381703849133257)
                    ·
                      rfl

theorem cell22_2476153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_2476153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476153 prefixEnd_2476153 := by exact prefixLift 2476153
  have htrace : WordTrace (prefixWord ++ tailWord_2476153) baseStart_2476153 baseEnd_2476153 := by
    simpa [prefixWord, tailWord_2476153, baseEnd_2476153] using wordTrace_append hprefix tailTrace_2476153
  have hstable : (prefixWord ++ tailWord_2476153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476153).length < 2 ^ (prefixWord ++ tailWord_2476153).sum := by decide
  have hdescent : baseEnd_2476153 < baseStart_2476153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476170 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2476170 : Nat := 118140960795 + 2476170 * 2 ^ 59
def prefixEnd_2476170 : Nat := 4983230072969 + 3 ^ 40 * 2476170 * 2
def baseEnd_2476170 : Nat := 847643594829121471458205

theorem tailTrace_2476170 : CollatzResearch.WordTrace tailWord_2476170 prefixEnd_2476170 847643594829121471458205 := by
  unfold tailWord_2476170
  simp only [CollatzResearch.WordTrace]
  refine ⟨22578334859816615253156491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60208892959510974008417309 22578334859816615253156491)
  ·
    refine ⟨33867502289724922879734737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22578334859816615253156491 33867502289724922879734737)
    ·
      refine ⟨25400626717293692159801053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33867502289724922879734737 25400626717293692159801053)
      ·
        refine ⟨9525235018985134559925395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25400626717293692159801053 9525235018985134559925395)
        ·
          refine ⟨14287852528477701839888093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9525235018985134559925395 14287852528477701839888093)
          ·
            refine ⟨5357944698179138189958035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14287852528477701839888093 5357944698179138189958035)
            ·
              refine ⟨8036917047268707284937053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357944698179138189958035 8036917047268707284937053)
              ·
                refine ⟨3013843892725765231851395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8036917047268707284937053 3013843892725765231851395)
                ·
                  refine ⟨4520765839088647847777093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3013843892725765231851395 4520765839088647847777093)
                  ·
                    refine ⟨847643594829121471458205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4520765839088647847777093 847643594829121471458205)
                    ·
                      rfl

theorem cell22_2476170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2476170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476170 prefixEnd_2476170 := by exact prefixLift 2476170
  have htrace : WordTrace (prefixWord ++ tailWord_2476170) baseStart_2476170 baseEnd_2476170 := by
    simpa [prefixWord, tailWord_2476170, baseEnd_2476170] using wordTrace_append hprefix tailTrace_2476170
  have hstable : (prefixWord ++ tailWord_2476170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476170).length < 2 ^ (prefixWord ++ tailWord_2476170).sum := by decide
  have hdescent : baseEnd_2476170 < baseStart_2476170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476211 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_2476211 : Nat := 118140960795 + 2476211 * 2 ^ 59
def prefixEnd_2476211 : Nat := 4983230072969 + 3 ^ 40 * 2476211 * 2
def baseEnd_2476211 : Nat := 847657629967011031183079

theorem tailTrace_2476211 : CollatzResearch.WordTrace tailWord_2476211 prefixEnd_2476211 847657629967011031183079 := by
  unfold tailWord_2476211
  simp only [CollatzResearch.WordTrace]
  refine ⟨90314834832117925014868487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60209889888078616676578991 90314834832117925014868487)
  ·
    refine ⟨135472252248176887522302731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90314834832117925014868487 135472252248176887522302731)
    ·
      refine ⟨203208378372265331283454097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135472252248176887522302731 203208378372265331283454097)
      ·
        refine ⟨152406283779198998462590573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203208378372265331283454097 152406283779198998462590573)
        ·
          refine ⟨57152356417199624423471465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152406283779198998462590573 57152356417199624423471465)
          ·
            refine ⟨42864267312899718317603599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57152356417199624423471465 42864267312899718317603599)
            ·
              refine ⟨64296400969349577476405399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42864267312899718317603599 64296400969349577476405399)
              ·
                refine ⟨96444601454024366214608099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64296400969349577476405399 96444601454024366214608099)
                ·
                  refine ⟨144666902181036549321912149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96444601454024366214608099 144666902181036549321912149)
                  ·
                    refine ⟨847657629967011031183079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 144666902181036549321912149 847657629967011031183079)
                    ·
                      rfl

theorem cell22_2476211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_2476211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476211 prefixEnd_2476211 := by exact prefixLift 2476211
  have htrace : WordTrace (prefixWord ++ tailWord_2476211) baseStart_2476211 baseEnd_2476211 := by
    simpa [prefixWord, tailWord_2476211, baseEnd_2476211] using wordTrace_append hprefix tailTrace_2476211
  have hstable : (prefixWord ++ tailWord_2476211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476211).length < 2 ^ (prefixWord ++ tailWord_2476211).sum := by decide
  have hdescent : baseEnd_2476211 < baseStart_2476211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476292 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_2476292 : Nat := 118140960795 + 2476292 * 2 ^ 59
def prefixEnd_2476292 : Nat := 4983230072969 + 3 ^ 40 * 2476292 * 2
def baseEnd_2476292 : Nat := 282561785974117939969277

theorem tailTrace_2476292 : CollatzResearch.WordTrace tailWord_2476292 prefixEnd_2476292 282561785974117939969277 := by
  unfold tailWord_2476292
  simp only [CollatzResearch.WordTrace]
  refine ⟨45158894572412237924283565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60211859429882983899044753 45158894572412237924283565)
  ·
    refine ⟨16934585464654589221606337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45158894572412237924283565 16934585464654589221606337)
    ·
      refine ⟨12700939098490941916204753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16934585464654589221606337 12700939098490941916204753)
      ·
        refine ⟨9525704323868206437153565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12700939098490941916204753 9525704323868206437153565)
        ·
          refine ⟨3572139121450577413932587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9525704323868206437153565 3572139121450577413932587)
          ·
            refine ⟨5358208682175866120898881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572139121450577413932587 5358208682175866120898881)
            ·
              refine ⟨4018656511631899590674161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5358208682175866120898881 4018656511631899590674161)
              ·
                refine ⟨3013992383723924693005621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4018656511631899590674161 3013992383723924693005621)
                ·
                  refine ⟨282561785974117939969277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3013992383723924693005621 282561785974117939969277)
                  ·
                    rfl

theorem cell22_2476292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_2476292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476292 prefixEnd_2476292 := by exact prefixLift 2476292
  have htrace : WordTrace (prefixWord ++ tailWord_2476292) baseStart_2476292 baseEnd_2476292 := by
    simpa [prefixWord, tailWord_2476292, baseEnd_2476292] using wordTrace_append hprefix tailTrace_2476292
  have hstable : (prefixWord ++ tailWord_2476292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476292).length < 2 ^ (prefixWord ++ tailWord_2476292).sum := by decide
  have hdescent : baseEnd_2476292 < baseStart_2476292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476296 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 1, 3]
def baseStart_2476296 : Nat := 118140960795 + 2476296 * 2 ^ 59
def prefixEnd_2476296 : Nat := 4983230072969 + 3 ^ 40 * 2476296 * 2
def baseEnd_2476296 : Nat := 847686727204099142807819

theorem tailTrace_2476296 : CollatzResearch.WordTrace tailWord_2476296 prefixEnd_2476296 847686727204099142807819 := by
  unfold tailWord_2476296
  simp only [CollatzResearch.WordTrace]
  refine ⟨45158967518404992265856371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60211956691206656354475161 45158967518404992265856371)
  ·
    refine ⟨67738451277607488398784557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45158967518404992265856371 67738451277607488398784557)
    ·
      refine ⟨25401919229102808149544209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67738451277607488398784557 25401919229102808149544209)
      ·
        refine ⟨19051439421827106112158157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25401919229102808149544209 19051439421827106112158157)
        ·
          refine ⟨7144289783185164792059309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19051439421827106112158157 7144289783185164792059309)
          ·
            refine ⟨2679108668694436797022241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7144289783185164792059309 2679108668694436797022241)
            ·
              refine ⟨2009331501520827597766681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679108668694436797022241 2009331501520827597766681)
              ·
                refine ⟨1506998626140620698325011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009331501520827597766681 1506998626140620698325011)
                ·
                  refine ⟨2260497939210931047487517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506998626140620698325011 2260497939210931047487517)
                  ·
                    refine ⟨847686727204099142807819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260497939210931047487517 847686727204099142807819)
                    ·
                      rfl

theorem cell22_2476296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_2476296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476296 prefixEnd_2476296 := by exact prefixLift 2476296
  have htrace : WordTrace (prefixWord ++ tailWord_2476296) baseStart_2476296 baseEnd_2476296 := by
    simpa [prefixWord, tailWord_2476296, baseEnd_2476296] using wordTrace_append hprefix tailTrace_2476296
  have hstable : (prefixWord ++ tailWord_2476296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476296).length < 2 ^ (prefixWord ++ tailWord_2476296).sum := by decide
  have hdescent : baseEnd_2476296 < baseStart_2476296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476320 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_2476320 : Nat := 118140960795 + 2476320 * 2 ^ 59
def prefixEnd_2476320 : Nat := 4983230072969 + 3 ^ 40 * 2476320 * 2
def baseEnd_2476320 : Nat := 282564980964857026735915

theorem tailTrace_2476320 : CollatzResearch.WordTrace tailWord_2476320 prefixEnd_2476320 282564980964857026735915 := by
  unfold tailWord_2476320
  simp only [CollatzResearch.WordTrace]
  refine ⟨45159405194361518315293207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60212540259148691087057609 45159405194361518315293207)
  ·
    refine ⟨67739107791542277472939811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45159405194361518315293207 67739107791542277472939811)
    ·
      refine ⟨101608661687313416209409717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67739107791542277472939811 101608661687313416209409717)
      ·
        refine ⟨9525812033185632769632161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101608661687313416209409717 9525812033185632769632161)
        ·
          refine ⟨7144359024889224577224121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9525812033185632769632161 7144359024889224577224121)
          ·
            refine ⟨5358269268666918432918091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144359024889224577224121 5358269268666918432918091)
            ·
              refine ⟨8037403903000377649377137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358269268666918432918091 8037403903000377649377137)
              ·
                refine ⟨6028052927250283237032853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8037403903000377649377137 6028052927250283237032853)
                ·
                  refine ⟨282564980964857026735915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6028052927250283237032853 282564980964857026735915)
                  ·
                    rfl

theorem cell22_2476320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_2476320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476320 prefixEnd_2476320 := by exact prefixLift 2476320
  have htrace : WordTrace (prefixWord ++ tailWord_2476320) baseStart_2476320 baseEnd_2476320 := by
    simpa [prefixWord, tailWord_2476320, baseEnd_2476320] using wordTrace_append hprefix tailTrace_2476320
  have hstable : (prefixWord ++ tailWord_2476320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476320).length < 2 ^ (prefixWord ++ tailWord_2476320).sum := by decide
  have hdescent : baseEnd_2476320 < baseStart_2476320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476348 : List Nat := [2, 2, 2, 2, 1, 2, 11]
def baseStart_2476348 : Nat := 118140960795 + 2476348 * 2 ^ 59
def prefixEnd_2476348 : Nat := 4983230072969 + 3 ^ 40 * 2476348 * 2
def baseEnd_2476348 : Nat := 31396463995066234833617

theorem tailTrace_2476348 : CollatzResearch.WordTrace tailWord_2476348 prefixEnd_2476348 31396463995066234833617 := by
  unfold tailWord_2476348
  simp only [CollatzResearch.WordTrace]
  refine ⟨45159915816310798706302849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60213221088414398275070465 45159915816310798706302849)
  ·
    refine ⟨33869936862233099029727137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45159915816310798706302849 33869936862233099029727137)
    ·
      refine ⟨25402452646674824272295353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33869936862233099029727137 25402452646674824272295353)
      ·
        refine ⟨19051839485006118204221515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25402452646674824272295353 19051839485006118204221515)
        ·
          refine ⟨28577759227509177306332273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19051839485006118204221515 28577759227509177306332273)
          ·
            refine ⟨21433319420631882979749205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28577759227509177306332273 21433319420631882979749205)
            ·
              refine ⟨31396463995066234833617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21433319420631882979749205 31396463995066234833617)
              ·
                rfl

theorem cell22_2476348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 11].length) (baseStart_2476348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476348 prefixEnd_2476348 := by exact prefixLift 2476348
  have htrace : WordTrace (prefixWord ++ tailWord_2476348) baseStart_2476348 baseEnd_2476348 := by
    simpa [prefixWord, tailWord_2476348, baseEnd_2476348] using wordTrace_append hprefix tailTrace_2476348
  have hstable : (prefixWord ++ tailWord_2476348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476348).length < 2 ^ (prefixWord ++ tailWord_2476348).sum := by decide
  have hdescent : baseEnd_2476348 < baseStart_2476348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476369 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_2476369 : Nat := 118140960795 + 2476369 * 2 ^ 59
def prefixEnd_2476369 : Nat := 4983230072969 + 3 ^ 40 * 2476369 * 2
def baseEnd_2476369 : Nat := 847711716595951285732595

theorem tailTrace_2476369 : CollatzResearch.WordTrace tailWord_2476369 prefixEnd_2476369 847711716595951285732595 := by
  unfold tailWord_2476369
  simp only [CollatzResearch.WordTrace]
  refine ⟨90320597565545517999120161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60213731710363678666080107 90320597565545517999120161)
  ·
    refine ⟨67740448174159138499340121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90320597565545517999120161 67740448174159138499340121)
    ·
      refine ⟨50805336130619353874505091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67740448174159138499340121 50805336130619353874505091)
      ·
        refine ⟨76208004195929030811757637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50805336130619353874505091 76208004195929030811757637)
        ·
          refine ⟨14289000786736693277204557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76208004195929030811757637 14289000786736693277204557)
          ·
            refine ⟨5358375295026259978951709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14289000786736693277204557 5358375295026259978951709)
            ·
              refine ⟨2009390735634847492106891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5358375295026259978951709 2009390735634847492106891)
              ·
                refine ⟨3014086103452271238160337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009390735634847492106891 3014086103452271238160337)
                ·
                  refine ⟨2260564577589203428620253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014086103452271238160337 2260564577589203428620253)
                  ·
                    refine ⟨847711716595951285732595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260564577589203428620253 847711716595951285732595)
                    ·
                      rfl

theorem cell22_2476369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_2476369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476369 prefixEnd_2476369 := by exact prefixLift 2476369
  have htrace : WordTrace (prefixWord ++ tailWord_2476369) baseStart_2476369 baseEnd_2476369 := by
    simpa [prefixWord, tailWord_2476369, baseEnd_2476369] using wordTrace_append hprefix tailTrace_2476369
  have hstable : (prefixWord ++ tailWord_2476369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476369).length < 2 ^ (prefixWord ++ tailWord_2476369).sum := by decide
  have hdescent : baseEnd_2476369 < baseStart_2476369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476393 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 9]
def baseStart_2476393 : Nat := 118140960795 + 2476393 * 2 ^ 59
def prefixEnd_2476393 : Nat := 4983230072969 + 3 ^ 40 * 2476393 * 2
def baseEnd_2476393 : Nat := 282573310762141074377507

theorem tailTrace_2476393 : CollatzResearch.WordTrace tailWord_2476393 prefixEnd_2476393 282573310762141074377507 := by
  unfold tailWord_2476393
  simp only [CollatzResearch.WordTrace]
  refine ⟨90321472917458570097993833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60214315278305713398662555 90321472917458570097993833)
  ·
    refine ⟨67741104688093927573495375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90321472917458570097993833 67741104688093927573495375)
    ·
      refine ⟨101611657032140891360243063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67741104688093927573495375 101611657032140891360243063)
      ·
        refine ⟨152417485548211337040364595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101611657032140891360243063 152417485548211337040364595)
        ·
          refine ⟨228626228322317005560546893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152417485548211337040364595 228626228322317005560546893)
          ·
            refine ⟨85734835620868877085205085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228626228322317005560546893 85734835620868877085205085)
            ·
              refine ⟨32150563357825828906951907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85734835620868877085205085 32150563357825828906951907)
              ·
                refine ⟨48225845036738743360427861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32150563357825828906951907 48225845036738743360427861)
                ·
                  refine ⟨282573310762141074377507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48225845036738743360427861 282573310762141074377507)
                  ·
                    rfl

theorem cell22_2476393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_2476393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476393 prefixEnd_2476393 := by exact prefixLift 2476393
  have htrace : WordTrace (prefixWord ++ tailWord_2476393) baseStart_2476393 baseEnd_2476393 := by
    simpa [prefixWord, tailWord_2476393, baseEnd_2476393] using wordTrace_append hprefix tailTrace_2476393
  have hstable : (prefixWord ++ tailWord_2476393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476393).length < 2 ^ (prefixWord ++ tailWord_2476393).sum := by decide
  have hdescent : baseEnd_2476393 < baseStart_2476393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476427 : List Nat := [1, 1, 1, 1, 4, 4, 4, 1, 5]
def baseStart_2476427 : Nat := 118140960795 + 2476427 * 2 ^ 59
def prefixEnd_2476427 : Nat := 4983230072969 + 3 ^ 40 * 2476427 * 2
def baseEnd_2476427 : Nat := 282577190393752822594139

theorem tailTrace_2476427 : CollatzResearch.WordTrace tailWord_2476427 prefixEnd_2476427 282577190393752822594139 := by
  unfold tailWord_2476427
  simp only [CollatzResearch.WordTrace]
  refine ⟨90322712999335393904731535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60215141999556929269821023 90322712999335393904731535)
  ·
    refine ⟨135484069499003090857097303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90322712999335393904731535 135484069499003090857097303)
    ·
      refine ⟨203226104248504636285645955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135484069499003090857097303 203226104248504636285645955)
      ·
        refine ⟨304839156372756954428468933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203226104248504636285645955 304839156372756954428468933)
        ·
          refine ⟨57157341819891928955337925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304839156372756954428468933 57157341819891928955337925)
          ·
            refine ⟨10717001591229736679125861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57157341819891928955337925 10717001591229736679125861)
            ·
              refine ⟨2009437798355575627336099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10717001591229736679125861 2009437798355575627336099)
              ·
                refine ⟨3014156697533363441004149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009437798355575627336099 3014156697533363441004149)
                ·
                  refine ⟨282577190393752822594139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3014156697533363441004149 282577190393752822594139)
                  ·
                    rfl

theorem cell22_2476427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 5].length) (baseStart_2476427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476427 prefixEnd_2476427 := by exact prefixLift 2476427
  have htrace : WordTrace (prefixWord ++ tailWord_2476427) baseStart_2476427 baseEnd_2476427 := by
    simpa [prefixWord, tailWord_2476427, baseEnd_2476427] using wordTrace_append hprefix tailTrace_2476427
  have hstable : (prefixWord ++ tailWord_2476427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476427).length < 2 ^ (prefixWord ++ tailWord_2476427).sum := by decide
  have hdescent : baseEnd_2476427 < baseStart_2476427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476487 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2476487 : Nat := 118140960795 + 2476487 * 2 ^ 59
def prefixEnd_2476487 : Nat := 4983230072969 + 3 ^ 40 * 2476487 * 2
def baseEnd_2476487 : Nat := 847752110407438311282233

theorem tailTrace_2476487 : CollatzResearch.WordTrace tailWord_2476487 prefixEnd_2476487 847752110407438311282233 := by
  unfold tailWord_2476487
  simp only [CollatzResearch.WordTrace]
  refine ⟨90324901379118024151915715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60216600919412016101277143 90324901379118024151915715)
  ·
    refine ⟨135487352068677036227873573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90324901379118024151915715 135487352068677036227873573)
    ·
      refine ⟨25403878512876944292726295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135487352068677036227873573 25403878512876944292726295)
      ·
        refine ⟨38105817769315416439089443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25403878512876944292726295 38105817769315416439089443)
        ·
          refine ⟨57158726653973124658634165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38105817769315416439089443 57158726653973124658634165)
          ·
            refine ⟨5358630623809980436746953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57158726653973124658634165 5358630623809980436746953)
            ·
              refine ⟨4018972967857485327560215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5358630623809980436746953 4018972967857485327560215)
              ·
                refine ⟨6028459451786227991340323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4018972967857485327560215 6028459451786227991340323)
                ·
                  refine ⟨9042689177679341987010485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6028459451786227991340323 9042689177679341987010485)
                  ·
                    refine ⟨847752110407438311282233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9042689177679341987010485 847752110407438311282233)
                    ·
                      rfl

theorem cell22_2476487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2476487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476487 prefixEnd_2476487 := by exact prefixLift 2476487
  have htrace : WordTrace (prefixWord ++ tailWord_2476487) baseStart_2476487 baseEnd_2476487 := by
    simpa [prefixWord, tailWord_2476487, baseEnd_2476487] using wordTrace_append hprefix tailTrace_2476487
  have hstable : (prefixWord ++ tailWord_2476487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476487).length < 2 ^ (prefixWord ++ tailWord_2476487).sum := by decide
  have hdescent : baseEnd_2476487 < baseStart_2476487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476517 : List Nat := [1, 3, 1, 5, 2, 1, 9]
def baseStart_2476517 : Nat := 118140960795 + 2476517 * 2 ^ 59
def prefixEnd_2476517 : Nat := 4983230072969 + 3 ^ 40 * 2476517 * 2
def baseEnd_2476517 : Nat := 31398606667426971593783

theorem tailTrace_2476517 : CollatzResearch.WordTrace tailWord_2476517 prefixEnd_2476517 31398606667426971593783 := by
  unfold tailWord_2476517
  simp only [CollatzResearch.WordTrace]
  refine ⟨90325995569009339275507805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60217330379339559517005203 90325995569009339275507805)
  ·
    refine ⟨33872248338378502228315427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90325995569009339275507805 33872248338378502228315427)
    ·
      refine ⟨50808372507567753342473141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33872248338378502228315427 50808372507567753342473141)
      ·
        refine ⟨4763284922584476875856857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50808372507567753342473141 4763284922584476875856857)
        ·
          refine ⟨3572463691938357656892643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4763284922584476875856857 3572463691938357656892643)
          ·
            refine ⟨5358695537907536485338965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572463691938357656892643 5358695537907536485338965)
            ·
              refine ⟨31398606667426971593783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5358695537907536485338965 31398606667426971593783)
              ·
                rfl

theorem cell22_2476517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 9].length) (baseStart_2476517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476517 prefixEnd_2476517 := by exact prefixLift 2476517
  have htrace : WordTrace (prefixWord ++ tailWord_2476517) baseStart_2476517 baseEnd_2476517 := by
    simpa [prefixWord, tailWord_2476517, baseEnd_2476517] using wordTrace_append hprefix tailTrace_2476517
  have hstable : (prefixWord ++ tailWord_2476517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476517).length < 2 ^ (prefixWord ++ tailWord_2476517).sum := by decide
  have hdescent : baseEnd_2476517 < baseStart_2476517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476551 : List Nat := [1, 1, 4, 3, 4, 1, 2, 6]
def baseStart_2476551 : Nat := 118140960795 + 2476551 * 2 ^ 59
def prefixEnd_2476551 : Nat := 4983230072969 + 3 ^ 40 * 2476551 * 2
def baseEnd_2476551 : Nat := 94197113212818164186893

theorem tailTrace_2476551 : CollatzResearch.WordTrace tailWord_2476551 prefixEnd_2476551 94197113212818164186893 := by
  unfold tailWord_2476551
  simp only [CollatzResearch.WordTrace]
  refine ⟨90327235650886163082245507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60218157100590775388163671 90327235650886163082245507)
  ·
    refine ⟨135490853476329244623368261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90327235650886163082245507 135490853476329244623368261)
    ·
      refine ⟨25404535026811733366881549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135490853476329244623368261 25404535026811733366881549)
      ·
        refine ⟨9526700635054400012580581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25404535026811733366881549 9526700635054400012580581)
        ·
          refine ⟨1786256369072700002358859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9526700635054400012580581 1786256369072700002358859)
          ·
            refine ⟨2679384553609050003538289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786256369072700002358859 2679384553609050003538289)
            ·
              refine ⟨2009538415206787502653717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679384553609050003538289 2009538415206787502653717)
              ·
                refine ⟨94197113212818164186893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2009538415206787502653717 94197113212818164186893)
                ·
                  rfl

theorem cell22_2476551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 6].length) (baseStart_2476551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476551 prefixEnd_2476551 := by exact prefixLift 2476551
  have htrace : WordTrace (prefixWord ++ tailWord_2476551) baseStart_2476551 baseEnd_2476551 := by
    simpa [prefixWord, tailWord_2476551, baseEnd_2476551] using wordTrace_append hprefix tailTrace_2476551
  have hstable : (prefixWord ++ tailWord_2476551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476551).length < 2 ^ (prefixWord ++ tailWord_2476551).sum := by decide
  have hdescent : baseEnd_2476551 < baseStart_2476551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476589 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2476589 : Nat := 118140960795 + 2476589 * 2 ^ 59
def prefixEnd_2476589 : Nat := 4983230072969 + 3 ^ 40 * 2476589 * 2
def baseEnd_2476589 : Nat := 847787027091944045231921

theorem tailTrace_2476589 : CollatzResearch.WordTrace tailWord_2476589 prefixEnd_2476589 847787027091944045231921 := by
  unfold tailWord_2476589
  simp only [CollatzResearch.WordTrace]
  refine ⟨90328621624748495572128821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60219081083165663714752547 90328621624748495572128821)
  ·
    refine ⟨8468308277320171459887077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90328621624748495572128821 8468308277320171459887077)
    ·
      refine ⟨1587807801997532148728827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8468308277320171459887077 1587807801997532148728827)
      ·
        refine ⟨2381711702996298223093241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587807801997532148728827 2381711702996298223093241)
        ·
          refine ⟨1786283777247223667319931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2381711702996298223093241 1786283777247223667319931)
          ·
            refine ⟨2679425665870835500979897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786283777247223667319931 2679425665870835500979897)
            ·
              refine ⟨2009569249403126625734923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679425665870835500979897 2009569249403126625734923)
              ·
                refine ⟨3014353874104689938602385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009569249403126625734923 3014353874104689938602385)
                ·
                  refine ⟨2260765405578517453951789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014353874104689938602385 2260765405578517453951789)
                  ·
                    refine ⟨847787027091944045231921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260765405578517453951789 847787027091944045231921)
                    ·
                      rfl

theorem cell22_2476589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2476589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476589 prefixEnd_2476589 := by exact prefixLift 2476589
  have htrace : WordTrace (prefixWord ++ tailWord_2476589) baseStart_2476589 baseEnd_2476589 := by
    simpa [prefixWord, tailWord_2476589, baseEnd_2476589] using wordTrace_append hprefix tailTrace_2476589
  have hstable : (prefixWord ++ tailWord_2476589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476589).length < 2 ^ (prefixWord ++ tailWord_2476589).sum := by decide
  have hdescent : baseEnd_2476589 < baseStart_2476589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476609 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2476609 : Nat := 118140960795 + 2476609 * 2 ^ 59
def prefixEnd_2476609 : Nat := 4983230072969 + 3 ^ 40 * 2476609 * 2
def baseEnd_2476609 : Nat := 847793873500670659731859

theorem tailTrace_2476609 : CollatzResearch.WordTrace tailWord_2476609 prefixEnd_2476609 847793873500670659731859 := by
  unfold tailWord_2476609
  simp only [CollatzResearch.WordTrace]
  refine ⟨90329351084676038987856881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60219567389784025991904587 90329351084676038987856881)
  ·
    refine ⟨67747013313507029240892661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90329351084676038987856881 67747013313507029240892661)
    ·
      refine ⟨6351282498141283991333687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67747013313507029240892661 6351282498141283991333687)
      ·
        refine ⟨9526923747211925987000531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6351282498141283991333687 9526923747211925987000531)
        ·
          refine ⟨14290385620817888980500797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9526923747211925987000531 14290385620817888980500797)
          ·
            refine ⟨5358894607806708367687799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14290385620817888980500797 5358894607806708367687799)
            ·
              refine ⟨8038341911710062551531699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358894607806708367687799 8038341911710062551531699)
              ·
                refine ⟨12057512867565093827297549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038341911710062551531699 12057512867565093827297549)
                ·
                  refine ⟨4521567325336910185236581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12057512867565093827297549 4521567325336910185236581)
                  ·
                    refine ⟨847793873500670659731859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4521567325336910185236581 847793873500670659731859)
                    ·
                      rfl

theorem cell22_2476609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2476609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476609 prefixEnd_2476609 := by exact prefixLift 2476609
  have htrace : WordTrace (prefixWord ++ tailWord_2476609) baseStart_2476609 baseEnd_2476609 := by
    simpa [prefixWord, tailWord_2476609, baseEnd_2476609] using wordTrace_append hprefix tailTrace_2476609
  have hstable : (prefixWord ++ tailWord_2476609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476609).length < 2 ^ (prefixWord ++ tailWord_2476609).sum := by decide
  have hdescent : baseEnd_2476609 < baseStart_2476609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476622 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2476622 : Nat := 118140960795 + 2476622 * 2 ^ 59
def prefixEnd_2476622 : Nat := 4983230072969 + 3 ^ 40 * 2476622 * 2
def baseEnd_2476622 : Nat := 847798323666342959156819

theorem tailTrace_2476622 : CollatzResearch.WordTrace tailWord_2476622 prefixEnd_2476622 847798323666342959156819 := by
  unfold tailWord_2476622
  simp only [CollatzResearch.WordTrace]
  refine ⟨11291228154203617776010015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60219883489085961472053413 11291228154203617776010015)
  ·
    refine ⟨16936842231305426664015023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11291228154203617776010015 16936842231305426664015023)
    ·
      refine ⟨25405263346958139996022535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16936842231305426664015023 25405263346958139996022535)
      ·
        refine ⟨38107895020437209994033803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25405263346958139996022535 38107895020437209994033803)
        ·
          refine ⟨57161842530655814991050705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38107895020437209994033803 57161842530655814991050705)
          ·
            refine ⟨42871381897991861243288029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57161842530655814991050705 42871381897991861243288029)
            ·
              refine ⟨16076768211746947966233011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42871381897991861243288029 16076768211746947966233011)
              ·
                refine ⟨24115152317620421949349517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16076768211746947966233011 24115152317620421949349517)
                ·
                  refine ⟨9043182119107658231006069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24115152317620421949349517 9043182119107658231006069)
                  ·
                    refine ⟨847798323666342959156819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9043182119107658231006069 847798323666342959156819)
                    ·
                      rfl

theorem cell22_2476622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2476622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476622 prefixEnd_2476622 := by exact prefixLift 2476622
  have htrace : WordTrace (prefixWord ++ tailWord_2476622) baseStart_2476622 baseEnd_2476622 := by
    simpa [prefixWord, tailWord_2476622, baseEnd_2476622] using wordTrace_append hprefix tailTrace_2476622
  have hstable : (prefixWord ++ tailWord_2476622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476622).length < 2 ^ (prefixWord ++ tailWord_2476622).sum := by decide
  have hdescent : baseEnd_2476622 < baseStart_2476622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476626 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_2476626 : Nat := 118140960795 + 2476626 * 2 ^ 59
def prefixEnd_2476626 : Nat := 4983230072969 + 3 ^ 40 * 2476626 * 2
def baseEnd_2476626 : Nat := 847799692948088282056807

theorem tailTrace_2476626 : CollatzResearch.WordTrace tailWord_2476626 prefixEnd_2476626 847799692948088282056807 := by
  unfold tailWord_2476626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22582492781403612722806433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60219980750409633927483821 22582492781403612722806433)
  ·
    refine ⟨16936869586052709542104825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22582492781403612722806433 16936869586052709542104825)
    ·
      refine ⟨12702652189539532156578619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16936869586052709542104825 12702652189539532156578619)
      ·
        refine ⟨19053978284309298234867929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12702652189539532156578619 19053978284309298234867929)
        ·
          refine ⟨14290483713231973676150947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19053978284309298234867929 14290483713231973676150947)
          ·
            refine ⟨21435725569847960514226421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14290483713231973676150947 21435725569847960514226421)
            ·
              refine ⟨2009599272173246298208727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21435725569847960514226421 2009599272173246298208727)
              ·
                refine ⟨3014398908259869447313091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009599272173246298208727 3014398908259869447313091)
                ·
                  refine ⟨4521598362389804170969637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3014398908259869447313091 4521598362389804170969637)
                  ·
                    refine ⟨847799692948088282056807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4521598362389804170969637 847799692948088282056807)
                    ·
                      rfl

theorem cell22_2476626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_2476626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476626 prefixEnd_2476626 := by exact prefixLift 2476626
  have htrace : WordTrace (prefixWord ++ tailWord_2476626) baseStart_2476626 baseEnd_2476626 := by
    simpa [prefixWord, tailWord_2476626, baseEnd_2476626] using wordTrace_append hprefix tailTrace_2476626
  have hstable : (prefixWord ++ tailWord_2476626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476626).length < 2 ^ (prefixWord ++ tailWord_2476626).sum := by decide
  have hdescent : baseEnd_2476626 < baseStart_2476626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476641 : List Nat := [1, 2, 3, 1, 1, 4, 4, 2, 4]
def baseStart_2476641 : Nat := 118140960795 + 2476641 * 2 ^ 59
def prefixEnd_2476641 : Nat := 4983230072969 + 3 ^ 40 * 2476641 * 2
def baseEnd_2476641 : Nat := 282601609251544414310587

theorem tailTrace_2476641 : CollatzResearch.WordTrace tailWord_2476641 prefixEnd_2476641 282601609251544414310587 := by
  unfold tailWord_2476641
  simp only [CollatzResearch.WordTrace]
  refine ⟨90330518220560108453021777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60220345480373405635347851 90330518220560108453021777)
  ·
    refine ⟨67747888665420081339766333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90330518220560108453021777 67747888665420081339766333)
    ·
      refine ⟨25405458249532530502412375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67747888665420081339766333 25405458249532530502412375)
      ·
        refine ⟨38108187374298795753618563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25405458249532530502412375 38108187374298795753618563)
        ·
          refine ⟨57162281061448193630427845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38108187374298795753618563 57162281061448193630427845)
          ·
            refine ⟨10717927699021536305705221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57162281061448193630427845 10717927699021536305705221)
            ·
              refine ⟨2009611443566538057319729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10717927699021536305705221 2009611443566538057319729)
              ·
                refine ⟨1507208582674903542989797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009611443566538057319729 1507208582674903542989797)
                ·
                  refine ⟨282601609251544414310587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507208582674903542989797 282601609251544414310587)
                  ·
                    rfl

theorem cell22_2476641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_2476641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476641 prefixEnd_2476641 := by exact prefixLift 2476641
  have htrace : WordTrace (prefixWord ++ tailWord_2476641) baseStart_2476641 baseEnd_2476641 := by
    simpa [prefixWord, tailWord_2476641, baseEnd_2476641] using wordTrace_append hprefix tailTrace_2476641
  have hstable : (prefixWord ++ tailWord_2476641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476641).length < 2 ^ (prefixWord ++ tailWord_2476641).sum := by decide
  have hdescent : baseEnd_2476641 < baseStart_2476641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476652 : List Nat := [2, 2, 1, 1, 3, 1, 5, 7]
def baseStart_2476652 : Nat := 118140960795 + 2476652 * 2 ^ 59
def prefixEnd_2476652 : Nat := 4983230072969 + 3 ^ 40 * 2476652 * 2
def baseEnd_2476652 : Nat := 94200954808825875656303

theorem tailTrace_2476652 : CollatzResearch.WordTrace tailWord_2476652 prefixEnd_2476652 94200954808825875656303 := by
  unfold tailWord_2476652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45165459711760128665836105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60220612949013504887781473 45165459711760128665836105)
  ·
    refine ⟨33874094783820096499377079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45165459711760128665836105 33874094783820096499377079)
    ·
      refine ⟨50811142175730144749065619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33874094783820096499377079 50811142175730144749065619)
      ·
        refine ⟨76216713263595217123598429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50811142175730144749065619 76216713263595217123598429)
        ·
          refine ⟨28581267473848206421349411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76216713263595217123598429 28581267473848206421349411)
          ·
            refine ⟨42871901210772309632024117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28581267473848206421349411 42871901210772309632024117)
            ·
              refine ⟨4019240738509904028002261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42871901210772309632024117 4019240738509904028002261)
              ·
                refine ⟨94200954808825875656303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4019240738509904028002261 94200954808825875656303)
                ·
                  rfl

theorem cell22_2476652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_2476652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476652 prefixEnd_2476652 := by exact prefixLift 2476652
  have htrace : WordTrace (prefixWord ++ tailWord_2476652) baseStart_2476652 baseEnd_2476652 := by
    simpa [prefixWord, tailWord_2476652, baseEnd_2476652] using wordTrace_append hprefix tailTrace_2476652
  have hstable : (prefixWord ++ tailWord_2476652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476652).length < 2 ^ (prefixWord ++ tailWord_2476652).sum := by decide
  have hdescent : baseEnd_2476652 < baseStart_2476652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476697 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 7]
def baseStart_2476697 : Nat := 118140960795 + 2476697 * 2 ^ 59
def prefixEnd_2476697 : Nat := 4983230072969 + 3 ^ 40 * 2476697 * 2
def baseEnd_2476697 : Nat := 282607999233022587843863

theorem tailTrace_2476697 : CollatzResearch.WordTrace tailWord_2476697 prefixEnd_2476697 282607999233022587843863 := by
  unfold tailWord_2476697
  simp only [CollatzResearch.WordTrace]
  refine ⟨90332560708357230017060345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60221707138904820011373563 90332560708357230017060345)
  ·
    refine ⟨67749420531267922512795259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90332560708357230017060345 67749420531267922512795259)
    ·
      refine ⟨101624130796901883769192889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67749420531267922512795259 101624130796901883769192889)
      ·
        refine ⟨76218098097676412826894667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101624130796901883769192889 76218098097676412826894667)
        ·
          refine ⟨114327147146514619240342001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76218098097676412826894667 114327147146514619240342001)
          ·
            refine ⟨85745360359885964430256501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114327147146514619240342001 85745360359885964430256501)
            ·
              refine ⟨8038627533739309165336547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85745360359885964430256501 8038627533739309165336547)
              ·
                refine ⟨12057941300608963748004821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8038627533739309165336547 12057941300608963748004821)
                ·
                  refine ⟨282607999233022587843863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12057941300608963748004821 282607999233022587843863)
                  ·
                    rfl

theorem cell22_2476697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_2476697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476697 prefixEnd_2476697 := by exact prefixLift 2476697
  have htrace : WordTrace (prefixWord ++ tailWord_2476697) baseStart_2476697 baseEnd_2476697 := by
    simpa [prefixWord, tailWord_2476697, baseEnd_2476697] using wordTrace_append hprefix tailTrace_2476697
  have hstable : (prefixWord ++ tailWord_2476697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476697).length < 2 ^ (prefixWord ++ tailWord_2476697).sum := by decide
  have hdescent : baseEnd_2476697 < baseStart_2476697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476718 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2476718 : Nat := 118140960795 + 2476718 * 2 ^ 59
def prefixEnd_2476718 : Nat := 4983230072969 + 3 ^ 40 * 2476718 * 2
def baseEnd_2476718 : Nat := 847831186428230708756525

theorem tailTrace_2476718 : CollatzResearch.WordTrace tailWord_2476718 prefixEnd_2476718 847831186428230708756525 := by
  unfold tailWord_2476718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11291665830160143825446851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60222217760854100402383205 11291665830160143825446851)
  ·
    refine ⟨16937498745240215738170277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11291665830160143825446851 16937498745240215738170277)
    ·
      refine ⟨3175781014732540450906927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16937498745240215738170277 3175781014732540450906927)
      ·
        refine ⟨4763671522098810676360391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3175781014732540450906927 4763671522098810676360391)
        ·
          refine ⟨7145507283148216014540587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4763671522098810676360391 7145507283148216014540587)
          ·
            refine ⟨10718260924722324021810881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7145507283148216014540587 10718260924722324021810881)
            ·
              refine ⟨8038695693541743016358161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10718260924722324021810881 8038695693541743016358161)
              ·
                refine ⟨6029021770156307262268621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8038695693541743016358161 6029021770156307262268621)
                ·
                  refine ⟨2260883163808615223350733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6029021770156307262268621 2260883163808615223350733)
                  ·
                    refine ⟨847831186428230708756525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260883163808615223350733 847831186428230708756525)
                    ·
                      rfl

theorem cell22_2476718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2476718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476718 prefixEnd_2476718 := by exact prefixLift 2476718
  have htrace : WordTrace (prefixWord ++ tailWord_2476718) baseStart_2476718 baseEnd_2476718 := by
    simpa [prefixWord, tailWord_2476718, baseEnd_2476718] using wordTrace_append hprefix tailTrace_2476718
  have hstable : (prefixWord ++ tailWord_2476718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476718).length < 2 ^ (prefixWord ++ tailWord_2476718).sum := by decide
  have hdescent : baseEnd_2476718 < baseStart_2476718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476759 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 6]
def baseStart_2476759 : Nat := 118140960795 + 2476759 * 2 ^ 59
def prefixEnd_2476759 : Nat := 4983230072969 + 3 ^ 40 * 2476759 * 2
def baseEnd_2476759 : Nat := 282615073855373422827133

theorem tailTrace_2476759 : CollatzResearch.WordTrace tailWord_2476759 prefixEnd_2476759 282615073855373422827133 := by
  unfold tailWord_2476759
  simp only [CollatzResearch.WordTrace]
  refine ⟨90334822034132614605817331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60223214689421743070544887 90334822034132614605817331)
  ·
    refine ⟨135502233051198921908725997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90334822034132614605817331 135502233051198921908725997)
    ·
      refine ⟨50813337394199595715772249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135502233051198921908725997 50813337394199595715772249)
      ·
        refine ⟨38110003045649696786829187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50813337394199595715772249 38110003045649696786829187)
        ·
          refine ⟨57165004568474545180243781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38110003045649696786829187 57165004568474545180243781)
          ·
            refine ⟨10718438356588977221295709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57165004568474545180243781 10718438356588977221295709)
            ·
              refine ⟨4019414383720866457985891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10718438356588977221295709 4019414383720866457985891)
              ·
                refine ⟨6029121575581299686978837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019414383720866457985891 6029121575581299686978837)
                ·
                  refine ⟨282615073855373422827133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6029121575581299686978837 282615073855373422827133)
                  ·
                    rfl

theorem cell22_2476759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 6].length) (baseStart_2476759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476759 prefixEnd_2476759 := by exact prefixLift 2476759
  have htrace : WordTrace (prefixWord ++ tailWord_2476759) baseStart_2476759 baseEnd_2476759 := by
    simpa [prefixWord, tailWord_2476759, baseEnd_2476759] using wordTrace_append hprefix tailTrace_2476759
  have hstable : (prefixWord ++ tailWord_2476759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476759).length < 2 ^ (prefixWord ++ tailWord_2476759).sum := by decide
  have hdescent : baseEnd_2476759 < baseStart_2476759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476808 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_2476808 : Nat := 118140960795 + 2476808 * 2 ^ 59
def prefixEnd_2476808 : Nat := 4983230072969 + 3 ^ 40 * 2476808 * 2
def baseEnd_2476808 : Nat := 847861995267500474006249

theorem tailTrace_2476808 : CollatzResearch.WordTrace tailWord_2476808 prefixEnd_2476808 847861995267500474006249 := by
  unfold tailWord_2476808
  simp only [CollatzResearch.WordTrace]
  refine ⟨45168304605477547987175539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60224406140636730649567385 45168304605477547987175539)
  ·
    refine ⟨67752456908216321980763309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45168304605477547987175539 67752456908216321980763309)
    ·
      refine ⟨25407171340581120742786241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67752456908216321980763309 25407171340581120742786241)
      ·
        refine ⟨19055378505435840557089681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25407171340581120742786241 19055378505435840557089681)
        ·
          refine ⟨14291533879076880417817261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19055378505435840557089681 14291533879076880417817261)
          ·
            refine ⟨5359325204653830156681473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14291533879076880417817261 5359325204653830156681473)
            ·
              refine ⟨4019493903490372617511105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5359325204653830156681473 4019493903490372617511105)
              ·
                refine ⟨3014620427617779463133329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4019493903490372617511105 3014620427617779463133329)
                ·
                  refine ⟨2260965320713334597349997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014620427617779463133329 2260965320713334597349997)
                  ·
                    refine ⟨847861995267500474006249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2260965320713334597349997 847861995267500474006249)
                    ·
                      rfl

theorem cell22_2476808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_2476808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476808 prefixEnd_2476808 := by exact prefixLift 2476808
  have htrace : WordTrace (prefixWord ++ tailWord_2476808) baseStart_2476808 baseEnd_2476808 := by
    simpa [prefixWord, tailWord_2476808, baseEnd_2476808] using wordTrace_append hprefix tailTrace_2476808
  have hstable : (prefixWord ++ tailWord_2476808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476808).length < 2 ^ (prefixWord ++ tailWord_2476808).sum := by decide
  have hdescent : baseEnd_2476808 < baseStart_2476808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476849 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 7]
def baseStart_2476849 : Nat := 118140960795 + 2476849 * 2 ^ 59
def prefixEnd_2476849 : Nat := 4983230072969 + 3 ^ 40 * 2476849 * 2
def baseEnd_2476849 : Nat := 282625343468463344577041

theorem tailTrace_2476849 : CollatzResearch.WordTrace tailWord_2476849 prefixEnd_2476849 282625343468463344577041 := by
  unfold tailWord_2476849
  simp only [CollatzResearch.WordTrace]
  refine ⟨90338104603806559976593601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60225403069204373317729067 90338104603806559976593601)
  ·
    refine ⟨67753578452854919982445201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90338104603806559976593601 67753578452854919982445201)
    ·
      refine ⟨50815183839641189986833901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67753578452854919982445201 50815183839641189986833901)
      ·
        refine ⟨19055693939865446245062713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50815183839641189986833901 19055693939865446245062713)
        ·
          refine ⟨14291770454899084683797035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19055693939865446245062713 14291770454899084683797035)
          ·
            refine ⟨21437655682348627025695553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14291770454899084683797035 21437655682348627025695553)
            ·
              refine ⟨16078241761761470269271665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21437655682348627025695553 16078241761761470269271665)
              ·
                refine ⟨12058681321321102701953749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16078241761761470269271665 12058681321321102701953749)
                ·
                  refine ⟨282625343468463344577041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12058681321321102701953749 282625343468463344577041)
                  ·
                    rfl

theorem cell22_2476849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_2476849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476849 prefixEnd_2476849 := by exact prefixLift 2476849
  have htrace : WordTrace (prefixWord ++ tailWord_2476849) baseStart_2476849 baseEnd_2476849 := by
    simpa [prefixWord, tailWord_2476849, baseEnd_2476849] using wordTrace_append hprefix tailTrace_2476849
  have hstable : (prefixWord ++ tailWord_2476849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476849).length < 2 ^ (prefixWord ++ tailWord_2476849).sum := by decide
  have hdescent : baseEnd_2476849 < baseStart_2476849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476939 : List Nat := [1, 1, 1, 1, 4, 2, 3, 9]
def baseStart_2476939 : Nat := 118140960795 + 2476939 * 2 ^ 59
def prefixEnd_2476939 : Nat := 4983230072969 + 3 ^ 40 * 2476939 * 2
def baseEnd_2476939 : Nat := 94211871027184422108983

theorem tailTrace_2476939 : CollatzResearch.WordTrace tailWord_2476939 prefixEnd_2476939 94211871027184422108983 := by
  unfold tailWord_2476939
  simp only [CollatzResearch.WordTrace]
  refine ⟨90341387173480505347369871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60227591448987003564913247 90341387173480505347369871)
  ·
    refine ⟨135512080760220758021054807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90341387173480505347369871 135512080760220758021054807)
    ·
      refine ⟨203268121140331137031582211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135512080760220758021054807 203268121140331137031582211)
      ·
        refine ⟨304902181710496705547373317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203268121140331137031582211 304902181710496705547373317)
        ·
          refine ⟨57169159070718132290132497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 304902181710496705547373317 57169159070718132290132497)
          ·
            refine ⟨42876869303038599217599373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57169159070718132290132497 42876869303038599217599373)
            ·
              refine ⟨16078825988639474706599765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42876869303038599217599373 16078825988639474706599765)
              ·
                refine ⟨94211871027184422108983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16078825988639474706599765 94211871027184422108983)
                ·
                  rfl

theorem cell22_2476939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 9].length) (baseStart_2476939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476939 prefixEnd_2476939 := by exact prefixLift 2476939
  have htrace : WordTrace (prefixWord ++ tailWord_2476939) baseStart_2476939 baseEnd_2476939 := by
    simpa [prefixWord, tailWord_2476939, baseEnd_2476939] using wordTrace_append hprefix tailTrace_2476939
  have hstable : (prefixWord ++ tailWord_2476939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476939).length < 2 ^ (prefixWord ++ tailWord_2476939).sum := by decide
  have hdescent : baseEnd_2476939 < baseStart_2476939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476971 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 5, 3]
def baseStart_2476971 : Nat := 118140960795 + 2476971 * 2 ^ 59
def prefixEnd_2476971 : Nat := 4983230072969 + 3 ^ 40 * 2476971 * 2
def baseEnd_2476971 : Nat := 847917793498622382180749

theorem tailTrace_2476971 : CollatzResearch.WordTrace tailWord_2476971 prefixEnd_2476971 847917793498622382180749 := by
  unfold tailWord_2476971
  simp only [CollatzResearch.WordTrace]
  refine ⟨90342554309364574812534767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60228369539576383208356511 90342554309364574812534767)
  ·
    refine ⟨135513831464046862218802151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90342554309364574812534767 135513831464046862218802151)
    ·
      refine ⟨203270747196070293328203227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135513831464046862218802151 203270747196070293328203227)
      ·
        refine ⟨304906120794105439992304841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203270747196070293328203227 304906120794105439992304841)
        ·
          refine ⟨228679590595579079994228631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304906120794105439992304841 228679590595579079994228631)
          ·
            refine ⟨343019385893368619991342947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228679590595579079994228631 343019385893368619991342947)
            ·
              refine ⟨514529078840052929987014421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343019385893368619991342947 514529078840052929987014421)
              ·
                refine ⟨24118550570627481093141301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 514529078840052929987014421 24118550570627481093141301)
                ·
                  refine ⟨2261114115996326352481997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24118550570627481093141301 2261114115996326352481997)
                  ·
                    refine ⟨847917793498622382180749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261114115996326352481997 847917793498622382180749)
                    ·
                      rfl

theorem cell22_2476971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3].length) (baseStart_2476971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476971 prefixEnd_2476971 := by exact prefixLift 2476971
  have htrace : WordTrace (prefixWord ++ tailWord_2476971) baseStart_2476971 baseEnd_2476971 := by
    simpa [prefixWord, tailWord_2476971, baseEnd_2476971] using wordTrace_append hprefix tailTrace_2476971
  have hstable : (prefixWord ++ tailWord_2476971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476971).length < 2 ^ (prefixWord ++ tailWord_2476971).sum := by decide
  have hdescent : baseEnd_2476971 < baseStart_2476971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2476973 : List Nat := [1, 5, 2, 3, 1, 10]
def baseStart_2476973 : Nat := 118140960795 + 2476973 * 2 ^ 59
def prefixEnd_2476973 : Nat := 4983230072969 + 3 ^ 40 * 2476973 * 2
def baseEnd_2476973 : Nat := 10468129359746852390503

theorem tailTrace_2476973 : CollatzResearch.WordTrace tailWord_2476973 prefixEnd_2476973 10468129359746852390503 := by
  unfold tailWord_2476973
  simp only [CollatzResearch.WordTrace]
  refine ⟨90342627255357329154107573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60228418170238219436071715 90342627255357329154107573)
  ·
    refine ⟨8469621305189749608197585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90342627255357329154107573 8469621305189749608197585)
    ·
      refine ⟨6352215978892312206148189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8469621305189749608197585 6352215978892312206148189)
      ·
        refine ⟨2382080992084617077305571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6352215978892312206148189 2382080992084617077305571)
        ·
          refine ⟨3573121488126925615958357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382080992084617077305571 3573121488126925615958357)
          ·
            refine ⟨10468129359746852390503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3573121488126925615958357 10468129359746852390503)
            ·
              rfl

theorem cell22_2476973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 10].length) (baseStart_2476973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2476973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2476973 prefixEnd_2476973 := by exact prefixLift 2476973
  have htrace : WordTrace (prefixWord ++ tailWord_2476973) baseStart_2476973 baseEnd_2476973 := by
    simpa [prefixWord, tailWord_2476973, baseEnd_2476973] using wordTrace_append hprefix tailTrace_2476973
  have hstable : (prefixWord ++ tailWord_2476973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2476973).length < 2 ^ (prefixWord ++ tailWord_2476973).sum := by decide
  have hdescent : baseEnd_2476973 < baseStart_2476973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2476973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477080 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_2477080 : Nat := 118140960795 + 2477080 * 2 ^ 59
def prefixEnd_2477080 : Nat := 4983230072969 + 3 ^ 40 * 2477080 * 2
def baseEnd_2477080 : Nat := 282651702142060810401805

theorem tailTrace_2477080 : CollatzResearch.WordTrace tailWord_2477080 prefixEnd_2477080 282651702142060810401805 := by
  unfold tailWord_2477080
  simp only [CollatzResearch.WordTrace]
  refine ⟨45173264932984843214126347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60231019910646457618835129 45173264932984843214126347)
  ·
    refine ⟨67759897399477264821189521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45173264932984843214126347 67759897399477264821189521)
    ·
      refine ⟨50819923049607948615892141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67759897399477264821189521 50819923049607948615892141)
      ·
        refine ⟨19057471143602980730959553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50819923049607948615892141 19057471143602980730959553)
        ·
          refine ⟨14293103357702235548219665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19057471143602980730959553 14293103357702235548219665)
          ·
            refine ⟨10719827518276676661164749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14293103357702235548219665 10719827518276676661164749)
            ·
              refine ⟨4019935319353753747936781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10719827518276676661164749 4019935319353753747936781)
              ·
                refine ⟨1507475744757657655476293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4019935319353753747936781 1507475744757657655476293)
                ·
                  refine ⟨282651702142060810401805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507475744757657655476293 282651702142060810401805)
                  ·
                    rfl

theorem cell22_2477080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_2477080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477080 prefixEnd_2477080 := by exact prefixLift 2477080
  have htrace : WordTrace (prefixWord ++ tailWord_2477080) baseStart_2477080 baseEnd_2477080 := by
    simpa [prefixWord, tailWord_2477080, baseEnd_2477080] using wordTrace_append hprefix tailTrace_2477080
  have hstable : (prefixWord ++ tailWord_2477080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477080).length < 2 ^ (prefixWord ++ tailWord_2477080).sum := by decide
  have hdescent : baseEnd_2477080 < baseStart_2477080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477091 : List Nat := [1, 1, 1, 4, 3, 2, 10]
def baseStart_2477091 : Nat := 118140960795 + 2477091 * 2 ^ 59
def prefixEnd_2477091 : Nat := 4983230072969 + 3 ^ 40 * 2477091 * 2
def baseEnd_2477091 : Nat := 31405884146332669228903

theorem tailTrace_2477091 : CollatzResearch.WordTrace tailWord_2477091 prefixEnd_2477091 31405884146332669228903 := by
  unfold tailWord_2477091
  simp only [CollatzResearch.WordTrace]
  refine ⟨90346931068929835306903127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60231287379286556871268751 90346931068929835306903127)
  ·
    refine ⟨135520396603394752960354691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90346931068929835306903127 135520396603394752960354691)
    ·
      refine ⟨203280594905092129440532037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135520396603394752960354691 203280594905092129440532037)
      ·
        refine ⟨38115111544704774270099757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203280594905092129440532037 38115111544704774270099757)
        ·
          refine ⟨14293166829264290351287409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38115111544704774270099757 14293166829264290351287409)
          ·
            refine ⟨10719875121948217763465557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14293166829264290351287409 10719875121948217763465557)
            ·
              refine ⟨31405884146332669228903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10719875121948217763465557 31405884146332669228903)
              ·
                rfl

theorem cell22_2477091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 10].length) (baseStart_2477091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477091 prefixEnd_2477091 := by exact prefixLift 2477091
  have htrace : WordTrace (prefixWord ++ tailWord_2477091) baseStart_2477091 baseEnd_2477091 := by
    simpa [prefixWord, tailWord_2477091, baseEnd_2477091] using wordTrace_append hprefix tailTrace_2477091
  have hstable : (prefixWord ++ tailWord_2477091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477091).length < 2 ^ (prefixWord ++ tailWord_2477091).sum := by decide
  have hdescent : baseEnd_2477091 < baseStart_2477091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477093 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_2477093 : Nat := 118140960795 + 2477093 * 2 ^ 59
def prefixEnd_2477093 : Nat := 4983230072969 + 3 ^ 40 * 2477093 * 2
def baseEnd_2477093 : Nat := 847959556591854730630375

theorem tailTrace_2477093 : CollatzResearch.WordTrace tailWord_2477093 prefixEnd_2477093 847959556591854730630375 := by
  unfold tailWord_2477093
  simp only [CollatzResearch.WordTrace]
  refine ⟨90347004014922589648475933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60231336009948393098983955 90347004014922589648475933)
  ·
    refine ⟨33880126505595971118178475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90347004014922589648475933 33880126505595971118178475)
    ·
      refine ⟨50820189758393956677267713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33880126505595971118178475 50820189758393956677267713)
      ·
        refine ⟨38115142318795467507950785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50820189758393956677267713 38115142318795467507950785)
        ·
          refine ⟨28586356739096600630963089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38115142318795467507950785 28586356739096600630963089)
          ·
            refine ⟨21439767554322450473222317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28586356739096600630963089 21439767554322450473222317)
            ·
              refine ⟨8039912832870918927458369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21439767554322450473222317 8039912832870918927458369)
              ·
                refine ⟨6029934624653189195593777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8039912832870918927458369 6029934624653189195593777)
                ·
                  refine ⟨4522450968489891896695333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6029934624653189195593777 4522450968489891896695333)
                  ·
                    refine ⟨847959556591854730630375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4522450968489891896695333 847959556591854730630375)
                    ·
                      rfl

theorem cell22_2477093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_2477093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477093 prefixEnd_2477093 := by exact prefixLift 2477093
  have htrace : WordTrace (prefixWord ++ tailWord_2477093) baseStart_2477093 baseEnd_2477093 := by
    simpa [prefixWord, tailWord_2477093, baseEnd_2477093] using wordTrace_append hprefix tailTrace_2477093
  have hstable : (prefixWord ++ tailWord_2477093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477093).length < 2 ^ (prefixWord ++ tailWord_2477093).sum := by decide
  have hdescent : baseEnd_2477093 < baseStart_2477093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2477112 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_2477112 : Nat := 118140960795 + 2477112 * 2 ^ 59
def prefixEnd_2477112 : Nat := 4983230072969 + 3 ^ 40 * 2477112 * 2
def baseEnd_2477112 : Nat := 847966060680145014405317

theorem tailTrace_2477112 : CollatzResearch.WordTrace tailWord_2477112 prefixEnd_2477112 847966060680145014405317 := by
  unfold tailWord_2477112
  simp only [CollatzResearch.WordTrace]
  refine ⟨45173848500926877946708795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60231798001235837262278393 45173848500926877946708795)
  ·
    refine ⟨67760772751390316920063193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45173848500926877946708795 67760772751390316920063193)
    ·
      refine ⟨50820579563542737690047395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67760772751390316920063193 50820579563542737690047395)
      ·
        refine ⟨76230869345314106535071093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50820579563542737690047395 76230869345314106535071093)
        ·
          refine ⟨7146644001123197487662915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76230869345314106535071093 7146644001123197487662915)
          ·
            refine ⟨10719966001684796231494373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146644001123197487662915 10719966001684796231494373)
            ·
              refine ⟨2009993625315899293405195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10719966001684796231494373 2009993625315899293405195)
              ·
                refine ⟨3014990437973848940107793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009993625315899293405195 3014990437973848940107793)
                ·
                  refine ⟨2261242828480386705080845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3014990437973848940107793 2261242828480386705080845)
                  ·
                    refine ⟨847966060680145014405317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2261242828480386705080845 847966060680145014405317)
                    ·
                      rfl

theorem cell22_2477112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_2477112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2477112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2477112 prefixEnd_2477112 := by exact prefixLift 2477112
  have htrace : WordTrace (prefixWord ++ tailWord_2477112) baseStart_2477112 baseEnd_2477112 := by
    simpa [prefixWord, tailWord_2477112, baseEnd_2477112] using wordTrace_append hprefix tailTrace_2477112
  have hstable : (prefixWord ++ tailWord_2477112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2477112).length < 2 ^ (prefixWord ++ tailWord_2477112).sum := by decide
  have hdescent : baseEnd_2477112 < baseStart_2477112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2477112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
