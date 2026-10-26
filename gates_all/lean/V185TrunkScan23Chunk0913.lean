import V185TrunkScan23Chunk0912

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5403572 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5403572 : Nat := 118140960795 + 5403572 * 2 ^ 59
def prefixEnd_5403572 : Nat := 4983230072969 + 3 ^ 40 * 5403572 * 2
def baseEnd_5403572 : Nat := 924876562392279244466477

theorem tailTrace_5403572 : CollatzResearch.WordTrace tailWord_5403572 prefixEnd_5403572 924876562392279244466477 := by
  unfold tailWord_5403572
  simp only [CollatzResearch.WordTrace]
  refine ⟨98542230989894487735170485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131389641319859316980227313 98542230989894487735170485)
  ·
    refine ⟨9238334155302608225172233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98542230989894487735170485 9238334155302608225172233)
    ·
      refine ⟨6928750616476956168879175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9238334155302608225172233 6928750616476956168879175)
      ·
        refine ⟨10393125924715434253318763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928750616476956168879175 10393125924715434253318763)
        ·
          refine ⟨15589688887073151379978145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393125924715434253318763 15589688887073151379978145)
          ·
            refine ⟨11692266665304863534983609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15589688887073151379978145 11692266665304863534983609)
            ·
              refine ⟨8769199998978647651237707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11692266665304863534983609 8769199998978647651237707)
              ·
                refine ⟨13153799998467971476856561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769199998978647651237707 13153799998467971476856561)
                ·
                  refine ⟨9865349998850978607642421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13153799998467971476856561 9865349998850978607642421)
                  ·
                    refine ⟨924876562392279244466477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9865349998850978607642421 924876562392279244466477)
                    ·
                      rfl

theorem cell23_5403572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5403572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403572 prefixEnd_5403572 := by exact prefixLift 5403572
  have htrace : WordTrace (prefixWord ++ tailWord_5403572) baseStart_5403572 baseEnd_5403572 := by
    simpa [prefixWord, tailWord_5403572, baseEnd_5403572] using wordTrace_append hprefix tailTrace_5403572
  have hstable : (prefixWord ++ tailWord_5403572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403572).length < 2 ^ (prefixWord ++ tailWord_5403572).sum := by decide
  have hdescent : baseEnd_5403572 < baseStart_5403572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403598 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_5403598 : Nat := 118140960795 + 5403598 * 2 ^ 59
def prefixEnd_5403598 : Nat := 4983230072969 + 3 ^ 40 * 5403598 * 2
def baseEnd_5403598 : Nat := 308293670852650514630479

theorem tailTrace_5403598 : CollatzResearch.WordTrace tailWord_5403598 prefixEnd_5403598 308293670852650514630479 := by
  unfold tailWord_5403598
  simp only [CollatzResearch.WordTrace]
  refine ⟨24635676284711847738848431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131390273518463187940524965 24635676284711847738848431)
  ·
    refine ⟨36953514427067771608272647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24635676284711847738848431 36953514427067771608272647)
    ·
      refine ⟨55430271640601657412408971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36953514427067771608272647 55430271640601657412408971)
      ·
        refine ⟨83145407460902486118613457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55430271640601657412408971 83145407460902486118613457)
        ·
          refine ⟨62359055595676864588960093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83145407460902486118613457 62359055595676864588960093)
          ·
            refine ⟨23384645848378824220860035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62359055595676864588960093 23384645848378824220860035)
            ·
              refine ⟨35076968772568236331290053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23384645848378824220860035 35076968772568236331290053)
              ·
                refine ⟨6576931644856544312116885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35076968772568236331290053 6576931644856544312116885)
                ·
                  refine ⟨308293670852650514630479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6576931644856544312116885 308293670852650514630479)
                  ·
                    rfl

theorem cell23_5403598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_5403598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403598 prefixEnd_5403598 := by exact prefixLift 5403598
  have htrace : WordTrace (prefixWord ++ tailWord_5403598) baseStart_5403598 baseEnd_5403598 := by
    simpa [prefixWord, tailWord_5403598, baseEnd_5403598] using wordTrace_append hprefix tailTrace_5403598
  have hstable : (prefixWord ++ tailWord_5403598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403598).length < 2 ^ (prefixWord ++ tailWord_5403598).sum := by decide
  have hdescent : baseEnd_5403598 < baseStart_5403598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403601 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_5403601 : Nat := 118140960795 + 5403601 * 2 ^ 59
def prefixEnd_5403601 : Nat := 4983230072969 + 3 ^ 40 * 5403601 * 2
def baseEnd_5403601 : Nat := 2774644578115818119936797

theorem tailTrace_5403601 : CollatzResearch.WordTrace tailWord_5403601 prefixEnd_5403601 2774644578115818119936797 := by
  unfold tailWord_5403601
  simp only [CollatzResearch.WordTrace]
  refine ⟨197085519696683913423146657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131390346464455942282097771 197085519696683913423146657)
  ·
    refine ⟨147814139772512935067359993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197085519696683913423146657 147814139772512935067359993)
    ·
      refine ⟨110860604829384701300519995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147814139772512935067359993 110860604829384701300519995)
      ·
        refine ⟨166290907244077051950779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110860604829384701300519995 166290907244077051950779993)
        ·
          refine ⟨124718180433057788963084995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166290907244077051950779993 124718180433057788963084995)
          ·
            refine ⟨187077270649586683444627493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124718180433057788963084995 187077270649586683444627493)
            ·
              refine ⟨35076988246797503145867655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187077270649586683444627493 35076988246797503145867655)
              ·
                refine ⟨52615482370196254718801483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35076988246797503145867655 52615482370196254718801483)
                ·
                  refine ⟨78923223555294382078202225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52615482370196254718801483 78923223555294382078202225)
                  ·
                    refine ⟨59192417666470786558651669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78923223555294382078202225 59192417666470786558651669)
                    ·
                      refine ⟨2774644578115818119936797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59192417666470786558651669 2774644578115818119936797)
                      ·
                        rfl

theorem cell23_5403601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_5403601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403601 prefixEnd_5403601 := by exact prefixLift 5403601
  have htrace : WordTrace (prefixWord ++ tailWord_5403601) baseStart_5403601 baseEnd_5403601 := by
    simpa [prefixWord, tailWord_5403601, baseEnd_5403601] using wordTrace_append hprefix tailTrace_5403601
  have hstable : (prefixWord ++ tailWord_5403601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403601).length < 2 ^ (prefixWord ++ tailWord_5403601).sum := by decide
  have hdescent : baseEnd_5403601 < baseStart_5403601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403666 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_5403666 : Nat := 118140960795 + 5403666 * 2 ^ 59
def prefixEnd_5403666 : Nat := 4983230072969 + 3 ^ 40 * 5403666 * 2
def baseEnd_5403666 : Nat := 308297550484262262847111

theorem tailTrace_5403666 : CollatzResearch.WordTrace tailWord_5403666 prefixEnd_5403666 308297550484262262847111 := by
  unfold tailWord_5403666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49271972610362107381065713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131391926960965619682841901 49271972610362107381065713)
  ·
    refine ⟨36953979457771580535799285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49271972610362107381065713 36953979457771580535799285)
    ·
      refine ⟨3464435574166085675231183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36953979457771580535799285 3464435574166085675231183)
      ·
        refine ⟨5196653361249128512846775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464435574166085675231183 5196653361249128512846775)
        ·
          refine ⟨7794980041873692769270163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196653361249128512846775 7794980041873692769270163)
          ·
            refine ⟨11692470062810539153905245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794980041873692769270163 11692470062810539153905245)
            ·
              refine ⟨4384676273553952182714467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11692470062810539153905245 4384676273553952182714467)
              ·
                refine ⟨6577014410330928274071701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384676273553952182714467 6577014410330928274071701)
                ·
                  refine ⟨308297550484262262847111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6577014410330928274071701 308297550484262262847111)
                  ·
                    rfl

theorem cell23_5403666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_5403666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403666 prefixEnd_5403666 := by exact prefixLift 5403666
  have htrace : WordTrace (prefixWord ++ tailWord_5403666) baseStart_5403666 baseEnd_5403666 := by
    simpa [prefixWord, tailWord_5403666, baseEnd_5403666] using wordTrace_append hprefix tailTrace_5403666
  have hstable : (prefixWord ++ tailWord_5403666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403666).length < 2 ^ (prefixWord ++ tailWord_5403666).sum := by decide
  have hdescent : baseEnd_5403666 < baseStart_5403666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403682 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_5403682 : Nat := 118140960795 + 5403682 * 2 ^ 59
def prefixEnd_5403682 : Nat := 4983230072969 + 3 ^ 40 * 5403682 * 2
def baseEnd_5403682 : Nat := 2774686170048832303023925

theorem tailTrace_5403682 : CollatzResearch.WordTrace tailWord_5403682 prefixEnd_5403682 2774686170048832303023925 := by
  unfold tailWord_5403682
  simp only [CollatzResearch.WordTrace]
  refine ⟨49272118502347616064211325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131392316006260309504563533 49272118502347616064211325)
  ·
    refine ⟨18477044438380356024079247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49272118502347616064211325 18477044438380356024079247)
    ·
      refine ⟨27715566657570534036118871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18477044438380356024079247 27715566657570534036118871)
      ·
        refine ⟨41573349986355801054178307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27715566657570534036118871 41573349986355801054178307)
        ·
          refine ⟨62360024979533701581267461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41573349986355801054178307 62360024979533701581267461)
          ·
            refine ⟨11692504683662569046487649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62360024979533701581267461 11692504683662569046487649)
            ·
              refine ⟨8769378512746926784865737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11692504683662569046487649 8769378512746926784865737)
              ·
                refine ⟨6577033884560195088649303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8769378512746926784865737 6577033884560195088649303)
                ·
                  refine ⟨9865550826840292632973955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577033884560195088649303 9865550826840292632973955)
                  ·
                    refine ⟨14798326240260438949460933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9865550826840292632973955 14798326240260438949460933)
                    ·
                      refine ⟨2774686170048832303023925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14798326240260438949460933 2774686170048832303023925)
                      ·
                        rfl

theorem cell23_5403682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_5403682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403682 prefixEnd_5403682 := by exact prefixLift 5403682
  have htrace : WordTrace (prefixWord ++ tailWord_5403682) baseStart_5403682 baseEnd_5403682 := by
    simpa [prefixWord, tailWord_5403682, baseEnd_5403682] using wordTrace_append hprefix tailTrace_5403682
  have hstable : (prefixWord ++ tailWord_5403682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403682).length < 2 ^ (prefixWord ++ tailWord_5403682).sum := by decide
  have hdescent : baseEnd_5403682 < baseStart_5403682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403702 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5403702 : Nat := 118140960795 + 5403702 * 2 ^ 59
def prefixEnd_5403702 : Nat := 4983230072969 + 3 ^ 40 * 5403702 * 2
def baseEnd_5403702 : Nat := 2774696439661922224773833

theorem tailTrace_5403702 : CollatzResearch.WordTrace tailWord_5403702 prefixEnd_5403702 2774696439661922224773833 := by
  unfold tailWord_5403702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318075216832375479535835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131392802312878671781715573 12318075216832375479535835)
  ·
    refine ⟨18477112825248563219303753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12318075216832375479535835 18477112825248563219303753)
    ·
      refine ⟨13857834618936422414477815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18477112825248563219303753 13857834618936422414477815)
      ·
        refine ⟨20786751928404633621716723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13857834618936422414477815 20786751928404633621716723)
        ·
          refine ⟨31180127892606950432575085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20786751928404633621716723 31180127892606950432575085)
          ·
            refine ⟨11692547959727606412215657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31180127892606950432575085 11692547959727606412215657)
            ·
              refine ⟨8769410969795704809161743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11692547959727606412215657 8769410969795704809161743)
              ·
                refine ⟨13154116454693557213742615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769410969795704809161743 13154116454693557213742615)
                ·
                  refine ⟨19731174682040335820613923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13154116454693557213742615 19731174682040335820613923)
                  ·
                    refine ⟨29596762023060503730920885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19731174682040335820613923 29596762023060503730920885)
                    ·
                      refine ⟨2774696439661922224773833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29596762023060503730920885 2774696439661922224773833)
                      ·
                        rfl

theorem cell23_5403702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5403702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403702 prefixEnd_5403702 := by exact prefixLift 5403702
  have htrace : WordTrace (prefixWord ++ tailWord_5403702) baseStart_5403702 baseEnd_5403702 := by
    simpa [prefixWord, tailWord_5403702, baseEnd_5403702] using wordTrace_append hprefix tailTrace_5403702
  have hstable : (prefixWord ++ tailWord_5403702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403702).length < 2 ^ (prefixWord ++ tailWord_5403702).sum := by decide
  have hdescent : baseEnd_5403702 < baseStart_5403702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403715 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 3]
def baseStart_5403715 : Nat := 118140960795 + 5403715 * 2 ^ 59
def prefixEnd_5403715 : Nat := 4983230072969 + 3 ^ 40 * 5403715 * 2
def baseEnd_5403715 : Nat := 2774703114910430673911273

theorem tailTrace_5403715 : CollatzResearch.WordTrace tailWord_5403715 prefixEnd_5403715 2774703114910430673911273 := by
  unfold tailWord_5403715
  simp only [CollatzResearch.WordTrace]
  refine ⟨197089677618270910892796599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131393118412180607261864399 197089677618270910892796599)
  ·
    refine ⟨295634516427406366339194899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197089677618270910892796599 295634516427406366339194899)
    ·
      refine ⟨443451774641109549508792349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295634516427406366339194899 443451774641109549508792349)
      ·
        refine ⟨166294415490416081065797131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443451774641109549508792349 166294415490416081065797131)
        ·
          refine ⟨249441623235624121598695697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166294415490416081065797131 249441623235624121598695697)
          ·
            refine ⟨187081217426718091199021773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249441623235624121598695697 187081217426718091199021773)
            ·
              refine ⟨70155456535019284199633165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187081217426718091199021773 70155456535019284199633165)
              ·
                refine ⟨26308296200632231574862437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70155456535019284199633165 26308296200632231574862437)
                ·
                  refine ⟨4932805537618543420286707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26308296200632231574862437 4932805537618543420286707)
                  ·
                    refine ⟨7399208306427815130430061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4932805537618543420286707 7399208306427815130430061)
                    ·
                      refine ⟨2774703114910430673911273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7399208306427815130430061 2774703114910430673911273)
                      ·
                        rfl

theorem cell23_5403715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_5403715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403715 prefixEnd_5403715 := by exact prefixLift 5403715
  have htrace : WordTrace (prefixWord ++ tailWord_5403715) baseStart_5403715 baseEnd_5403715 := by
    simpa [prefixWord, tailWord_5403715, baseEnd_5403715] using wordTrace_append hprefix tailTrace_5403715
  have hstable : (prefixWord ++ tailWord_5403715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403715).length < 2 ^ (prefixWord ++ tailWord_5403715).sum := by decide
  have hdescent : baseEnd_5403715 < baseStart_5403715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403738 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5403738 : Nat := 118140960795 + 5403738 * 2 ^ 59
def prefixEnd_5403738 : Nat := 4983230072969 + 3 ^ 40 * 5403738 * 2
def baseEnd_5403738 : Nat := 2774714924965484083923667

theorem tailTrace_5403738 : CollatzResearch.WordTrace tailWord_5403738 prefixEnd_5403738 2774714924965484083923667 := by
  unfold tailWord_5403738
  simp only [CollatzResearch.WordTrace]
  refine ⟨49272629124296896455220967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131393677664791723880589245 49272629124296896455220967)
  ·
    refine ⟨73908943686445344682831451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49272629124296896455220967 73908943686445344682831451)
    ·
      refine ⟨110863415529668017024247177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73908943686445344682831451 110863415529668017024247177)
      ·
        refine ⟨83147561647251012768185383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110863415529668017024247177 83147561647251012768185383)
        ·
          refine ⟨124721342470876519152278075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83147561647251012768185383 124721342470876519152278075)
          ·
            refine ⟨187082013706314778728417113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124721342470876519152278075 187082013706314778728417113)
            ·
              refine ⟨140311510279736084046312835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187082013706314778728417113 140311510279736084046312835)
              ·
                refine ⟨210467265419604126069469253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140311510279736084046312835 210467265419604126069469253)
                ·
                  refine ⟨39462612266175773638025485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210467265419604126069469253 39462612266175773638025485)
                  ·
                    refine ⟨14798479599815915114259557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39462612266175773638025485 14798479599815915114259557)
                    ·
                      refine ⟨2774714924965484083923667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14798479599815915114259557 2774714924965484083923667)
                      ·
                        rfl

theorem cell23_5403738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5403738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403738 prefixEnd_5403738 := by exact prefixLift 5403738
  have htrace : WordTrace (prefixWord ++ tailWord_5403738) baseStart_5403738 baseEnd_5403738 := by
    simpa [prefixWord, tailWord_5403738, baseEnd_5403738] using wordTrace_append hprefix tailTrace_5403738
  have hstable : (prefixWord ++ tailWord_5403738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403738).length < 2 ^ (prefixWord ++ tailWord_5403738).sum := by decide
  have hdescent : baseEnd_5403738 < baseStart_5403738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403748 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_5403748 : Nat := 118140960795 + 5403748 * 2 ^ 59
def prefixEnd_5403748 : Nat := 4983230072969 + 3 ^ 40 * 5403748 * 2
def baseEnd_5403748 : Nat := 924906686590676348266207

theorem tailTrace_5403748 : CollatzResearch.WordTrace tailWord_5403748 prefixEnd_5403748 924906686590676348266207 := by
  unfold tailWord_5403748
  simp only [CollatzResearch.WordTrace]
  refine ⟨98545440613575678764373949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131393920818100905019165265 98545440613575678764373949)
  ·
    refine ⟨36954540230090879536640231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98545440613575678764373949 36954540230090879536640231)
    ·
      refine ⟨55431810345136319304960347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36954540230090879536640231 55431810345136319304960347)
      ·
        refine ⟨83147715517704478957440521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55431810345136319304960347 83147715517704478957440521)
        ·
          refine ⟨62360786638278359218080391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83147715517704478957440521 62360786638278359218080391)
          ·
            refine ⟨93541179957417538827120587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62360786638278359218080391 93541179957417538827120587)
            ·
              refine ⟨140311769936126308240680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93541179957417538827120587 140311769936126308240680881)
              ·
                refine ⟨105233827452094731180510661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140311769936126308240680881 105233827452094731180510661)
                ·
                  refine ⟨19731342647267762096345749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105233827452094731180510661 19731342647267762096345749)
                  ·
                    refine ⟨924906686590676348266207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19731342647267762096345749 924906686590676348266207)
                    ·
                      rfl

theorem cell23_5403748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_5403748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403748 prefixEnd_5403748 := by exact prefixLift 5403748
  have htrace : WordTrace (prefixWord ++ tailWord_5403748) baseStart_5403748 baseEnd_5403748 := by
    simpa [prefixWord, tailWord_5403748, baseEnd_5403748] using wordTrace_append hprefix tailTrace_5403748
  have hstable : (prefixWord ++ tailWord_5403748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403748).length < 2 ^ (prefixWord ++ tailWord_5403748).sum := by decide
  have hdescent : baseEnd_5403748 < baseStart_5403748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403759 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 1, 3, 2]
def baseStart_5403759 : Nat := 118140960795 + 5403759 * 2 ^ 59
def prefixEnd_5403759 : Nat := 4983230072969 + 3 ^ 40 * 5403759 * 2
def baseEnd_5403759 : Nat := 2774725708059228501761071

theorem tailTrace_5403759 : CollatzResearch.WordTrace tailWord_5403759 prefixEnd_5403759 2774725708059228501761071 := by
  unfold tailWord_5403759
  simp only [CollatzResearch.WordTrace]
  refine ⟨197091282430111506407398331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131394188286741004271598887 197091282430111506407398331)
  ·
    refine ⟨295636923645167259611097497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197091282430111506407398331 295636923645167259611097497)
    ·
      refine ⟨221727692733875444708323123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295636923645167259611097497 221727692733875444708323123)
      ·
        refine ⟨332591539100813167062484685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221727692733875444708323123 332591539100813167062484685)
        ·
          refine ⟨124721827162804937648431757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332591539100813167062484685 124721827162804937648431757)
          ·
            refine ⟨46770685186051851618161909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124721827162804937648431757 46770685186051851618161909)
            ·
              refine ⟨4384751736192361089202679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46770685186051851618161909 4384751736192361089202679)
              ·
                refine ⟨6577127604288541633804019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384751736192361089202679 6577127604288541633804019)
                ·
                  refine ⟨9865691406432812450706029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577127604288541633804019 9865691406432812450706029)
                  ·
                    refine ⟨3699634277412304669014761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9865691406432812450706029 3699634277412304669014761)
                    ·
                      refine ⟨2774725708059228501761071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699634277412304669014761 2774725708059228501761071)
                      ·
                        rfl

theorem cell23_5403759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 3, 2].length) (baseStart_5403759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403759 prefixEnd_5403759 := by exact prefixLift 5403759
  have htrace : WordTrace (prefixWord ++ tailWord_5403759) baseStart_5403759 baseEnd_5403759 := by
    simpa [prefixWord, tailWord_5403759, baseEnd_5403759] using wordTrace_append hprefix tailTrace_5403759
  have hstable : (prefixWord ++ tailWord_5403759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403759).length < 2 ^ (prefixWord ++ tailWord_5403759).sum := by decide
  have hdescent : baseEnd_5403759 < baseStart_5403759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403785 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_5403785 : Nat := 118140960795 + 5403785 * 2 ^ 59
def prefixEnd_5403785 : Nat := 4983230072969 + 3 ^ 40 * 5403785 * 2
def baseEnd_5403785 : Nat := 2774739058556245400035951

theorem tailTrace_5403785 : CollatzResearch.WordTrace tailWord_5403785 prefixEnd_5403785 2774739058556245400035951 := by
  unfold tailWord_5403785
  simp only [CollatzResearch.WordTrace]
  refine ⟨197092230728017312847844809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131394820485344875231896539 197092230728017312847844809)
  ·
    refine ⟨147819173046012984635883607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197092230728017312847844809 147819173046012984635883607)
    ·
      refine ⟨221728759569019476953825411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147819173046012984635883607 221728759569019476953825411)
      ·
        refine ⟨332593139353529215430738117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221728759569019476953825411 332593139353529215430738117)
        ·
          refine ⟨62361213628786727893263397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 332593139353529215430738117 62361213628786727893263397)
          ·
            refine ⟨11692727555397511479986887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62361213628786727893263397 11692727555397511479986887)
            ·
              refine ⟨17539091333096267219980331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692727555397511479986887 17539091333096267219980331)
              ·
                refine ⟨26308636999644400829970497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17539091333096267219980331 26308636999644400829970497)
                ·
                  refine ⟨19731477749733300622477873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26308636999644400829970497 19731477749733300622477873)
                  ·
                    refine ⟨14798608312299975466858405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19731477749733300622477873 14798608312299975466858405)
                    ·
                      refine ⟨2774739058556245400035951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14798608312299975466858405 2774739058556245400035951)
                      ·
                        rfl

theorem cell23_5403785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_5403785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403785 prefixEnd_5403785 := by exact prefixLift 5403785
  have htrace : WordTrace (prefixWord ++ tailWord_5403785) baseStart_5403785 baseEnd_5403785 := by
    simpa [prefixWord, tailWord_5403785, baseEnd_5403785] using wordTrace_append hprefix tailTrace_5403785
  have hstable : (prefixWord ++ tailWord_5403785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403785).length < 2 ^ (prefixWord ++ tailWord_5403785).sum := by decide
  have hdescent : baseEnd_5403785 < baseStart_5403785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403805 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_5403805 : Nat := 118140960795 + 5403805 * 2 ^ 59
def prefixEnd_5403805 : Nat := 4983230072969 + 3 ^ 40 * 5403805 * 2
def baseEnd_5403805 : Nat := 2774749328169335321785859

theorem tailTrace_5403805 : CollatzResearch.WordTrace tailWord_5403805 prefixEnd_5403805 2774749328169335321785859 := by
  unfold tailWord_5403805
  simp only [CollatzResearch.WordTrace]
  refine ⟨197092960187944856263572869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131395306791963237509048579 197092960187944856263572869)
  ·
    refine ⟨36954930035239660549419913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197092960187944856263572869 36954930035239660549419913)
    ·
      refine ⟨27716197526429745412064935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36954930035239660549419913 27716197526429745412064935)
      ·
        refine ⟨41574296289644618118097403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27716197526429745412064935 41574296289644618118097403)
        ·
          refine ⟨62361444434466927177146105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41574296289644618118097403 62361444434466927177146105)
          ·
            refine ⟨46771083325850195382859579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62361444434466927177146105 46771083325850195382859579)
            ·
              refine ⟨70156624988775293074289369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46771083325850195382859579 70156624988775293074289369)
              ·
                refine ⟨52617468741581469805717027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70156624988775293074289369 52617468741581469805717027)
                ·
                  refine ⟨78926203112372204708575541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52617468741581469805717027 78926203112372204708575541)
                  ·
                    refine ⟨7399331541784894191428957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78926203112372204708575541 7399331541784894191428957)
                    ·
                      refine ⟨2774749328169335321785859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7399331541784894191428957 2774749328169335321785859)
                      ·
                        rfl

theorem cell23_5403805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_5403805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403805 prefixEnd_5403805 := by exact prefixLift 5403805
  have htrace : WordTrace (prefixWord ++ tailWord_5403805) baseStart_5403805 baseEnd_5403805 := by
    simpa [prefixWord, tailWord_5403805, baseEnd_5403805] using wordTrace_append hprefix tailTrace_5403805
  have hstable : (prefixWord ++ tailWord_5403805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403805).length < 2 ^ (prefixWord ++ tailWord_5403805).sum := by decide
  have hdescent : baseEnd_5403805 < baseStart_5403805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403810 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_5403810 : Nat := 118140960795 + 5403810 * 2 ^ 59
def prefixEnd_5403810 : Nat := 4983230072969 + 3 ^ 40 * 5403810 * 2
def baseEnd_5403810 : Nat := 2774751895572607802223337

theorem tailTrace_5403810 : CollatzResearch.WordTrace tailWord_5403810 prefixEnd_5403810 2774751895572607802223337 := by
  unfold tailWord_5403810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49273285638231685529376221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131395428368617828078336589 49273285638231685529376221)
  ·
    refine ⟨18477482114336882073516083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49273285638231685529376221 18477482114336882073516083)
    ·
      refine ⟨27716223171505323110274125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18477482114336882073516083 27716223171505323110274125)
      ·
        refine ⟨10393583689314496166352797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27716223171505323110274125 10393583689314496166352797)
        ·
          refine ⟨3897593883492936062382299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10393583689314496166352797 3897593883492936062382299)
          ·
            refine ⟨5846390825239404093573449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897593883492936062382299 5846390825239404093573449)
            ·
              refine ⟨4384793118929553070180087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5846390825239404093573449 4384793118929553070180087)
              ·
                refine ⟨6577189678394329605270131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4384793118929553070180087 6577189678394329605270131)
                ·
                  refine ⟨9865784517591494407905197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577189678394329605270131 9865784517591494407905197)
                  ·
                    refine ⟨3699669194096810402964449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9865784517591494407905197 3699669194096810402964449)
                    ·
                      refine ⟨2774751895572607802223337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699669194096810402964449 2774751895572607802223337)
                      ·
                        rfl

theorem cell23_5403810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_5403810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403810 prefixEnd_5403810 := by exact prefixLift 5403810
  have htrace : WordTrace (prefixWord ++ tailWord_5403810) baseStart_5403810 baseEnd_5403810 := by
    simpa [prefixWord, tailWord_5403810, baseEnd_5403810] using wordTrace_append hprefix tailTrace_5403810
  have hstable : (prefixWord ++ tailWord_5403810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403810).length < 2 ^ (prefixWord ++ tailWord_5403810).sum := by decide
  have hdescent : baseEnd_5403810 < baseStart_5403810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403812 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 5]
def baseStart_5403812 : Nat := 118140960795 + 5403812 * 2 ^ 59
def prefixEnd_5403812 : Nat := 4983230072969 + 3 ^ 40 * 5403812 * 2
def baseEnd_5403812 : Nat := 308305880281546310488703

theorem tailTrace_5403812 : CollatzResearch.WordTrace tailWord_5403812 prefixEnd_5403812 308305880281546310488703 := by
  unfold tailWord_5403812
  simp only [CollatzResearch.WordTrace]
  refine ⟨98546607749459748229538845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131395476999279664306051793 98546607749459748229538845)
  ·
    refine ⟨36954977906047405586077067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98546607749459748229538845 36954977906047405586077067)
    ·
      refine ⟨55432466859071108379115601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36954977906047405586077067 55432466859071108379115601)
      ·
        refine ⟨41574350144303331284336701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55432466859071108379115601 41574350144303331284336701)
        ·
          refine ⟨15590381304113749231626263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41574350144303331284336701 15590381304113749231626263)
          ·
            refine ⟨23385571956170623847439395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590381304113749231626263 23385571956170623847439395)
            ·
              refine ⟨35078357934255935771159093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23385571956170623847439395 35078357934255935771159093)
              ·
                refine ⟨3288596056336493978546165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35078357934255935771159093 3288596056336493978546165)
                ·
                  refine ⟨308305880281546310488703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3288596056336493978546165 308305880281546310488703)
                  ·
                    rfl

theorem cell23_5403812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_5403812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403812 prefixEnd_5403812 := by exact prefixLift 5403812
  have htrace : WordTrace (prefixWord ++ tailWord_5403812) baseStart_5403812 baseEnd_5403812 := by
    simpa [prefixWord, tailWord_5403812, baseEnd_5403812] using wordTrace_append hprefix tailTrace_5403812
  have hstable : (prefixWord ++ tailWord_5403812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403812).length < 2 ^ (prefixWord ++ tailWord_5403812).sum := by decide
  have hdescent : baseEnd_5403812 < baseStart_5403812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403855 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 5, 4]
def baseStart_5403855 : Nat := 118140960795 + 5403855 * 2 ^ 59
def prefixEnd_5403855 : Nat := 4983230072969 + 3 ^ 40 * 5403855 * 2
def baseEnd_5403855 : Nat := 924925000734020042053543

theorem tailTrace_5403855 : CollatzResearch.WordTrace tailWord_5403855 prefixEnd_5403855 924925000734020042053543 := by
  unfold tailWord_5403855
  simp only [CollatzResearch.WordTrace]
  refine ⟨197094783837763714802893019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131396522558509143201928679 197094783837763714802893019)
  ·
    refine ⟨295642175756645572204339529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197094783837763714802893019 295642175756645572204339529)
    ·
      refine ⟨221731631817484179153254647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295642175756645572204339529 221731631817484179153254647)
      ·
        refine ⟨332597447726226268729881971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221731631817484179153254647 332597447726226268729881971)
        ·
          refine ⟨498896171589339403094822957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332597447726226268729881971 498896171589339403094822957)
          ·
            refine ⟨187086064346002276160558609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498896171589339403094822957 187086064346002276160558609)
            ·
              refine ⟨140314548259501707120418957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187086064346002276160558609 140314548259501707120418957)
              ·
                refine ⟨52617955597313140170157109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140314548259501707120418957 52617955597313140170157109)
                ·
                  refine ⟨4932933337248106890952229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52617955597313140170157109 4932933337248106890952229)
                  ·
                    refine ⟨924925000734020042053543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932933337248106890952229 924925000734020042053543)
                    ·
                      rfl

theorem cell23_5403855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_5403855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403855 prefixEnd_5403855 := by exact prefixLift 5403855
  have htrace : WordTrace (prefixWord ++ tailWord_5403855) baseStart_5403855 baseEnd_5403855 := by
    simpa [prefixWord, tailWord_5403855, baseEnd_5403855] using wordTrace_append hprefix tailTrace_5403855
  have hstable : (prefixWord ++ tailWord_5403855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403855).length < 2 ^ (prefixWord ++ tailWord_5403855).sum := by decide
  have hdescent : baseEnd_5403855 < baseStart_5403855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403879 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5403879 : Nat := 118140960795 + 5403879 * 2 ^ 59
def prefixEnd_5403879 : Nat := 4983230072969 + 3 ^ 40 * 5403879 * 2
def baseEnd_5403879 : Nat := 2774787325737768032260519

theorem tailTrace_5403879 : CollatzResearch.WordTrace tailWord_5403879 prefixEnd_5403879 2774787325737768032260519 := by
  unfold tailWord_5403879
  simp only [CollatzResearch.WordTrace]
  refine ⟨197095659189676766901766691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131397106126451177934511127 197095659189676766901766691)
  ·
    refine ⟨295643488784515150352650037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197095659189676766901766691 295643488784515150352650037)
    ·
      refine ⟨27716577073548295345560941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295643488784515150352650037 27716577073548295345560941)
      ·
        refine ⟨10393716402580610754585353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27716577073548295345560941 10393716402580610754585353)
        ·
          refine ⟨7795287301935458065939015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10393716402580610754585353 7795287301935458065939015)
          ·
            refine ⟨11692930952903187098908523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795287301935458065939015 11692930952903187098908523)
            ·
              refine ⟨17539396429354780648362785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692930952903187098908523 17539396429354780648362785)
              ·
                refine ⟨13154547322016085486272089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17539396429354780648362785 13154547322016085486272089)
                ·
                  refine ⟨9865910491512064114704067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13154547322016085486272089 9865910491512064114704067)
                  ·
                    refine ⟨14798865737268096172056101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9865910491512064114704067 14798865737268096172056101)
                    ·
                      refine ⟨2774787325737768032260519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14798865737268096172056101 2774787325737768032260519)
                      ·
                        rfl

theorem cell23_5403879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5403879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403879 prefixEnd_5403879 := by exact prefixLift 5403879
  have htrace : WordTrace (prefixWord ++ tailWord_5403879) baseStart_5403879 baseEnd_5403879 := by
    simpa [prefixWord, tailWord_5403879, baseEnd_5403879] using wordTrace_append hprefix tailTrace_5403879
  have hstable : (prefixWord ++ tailWord_5403879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403879).length < 2 ^ (prefixWord ++ tailWord_5403879).sum := by decide
  have hdescent : baseEnd_5403879 < baseStart_5403879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403882 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_5403882 : Nat := 118140960795 + 5403882 * 2 ^ 59
def prefixEnd_5403882 : Nat := 4983230072969 + 3 ^ 40 * 5403882 * 2
def baseEnd_5403882 : Nat := 2774788866179731520523005

theorem tailTrace_5403882 : CollatzResearch.WordTrace tailWord_5403882 prefixEnd_5403882 2774788866179731520523005 := by
  unfold tailWord_5403882
  simp only [CollatzResearch.WordTrace]
  refine ⟨49273942152166474603531475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131397179072443932276083933 49273942152166474603531475)
  ·
    refine ⟨73910913228249711905297213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49273942152166474603531475 73910913228249711905297213)
    ·
      refine ⟨27716592460593641964486455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73910913228249711905297213 27716592460593641964486455)
      ·
        refine ⟨41574888690890462946729683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27716592460593641964486455 41574888690890462946729683)
        ·
          refine ⟨62362333036335694420094525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41574888690890462946729683 62362333036335694420094525)
          ·
            refine ⟨23385874888625885407535447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62362333036335694420094525 23385874888625885407535447)
            ·
              refine ⟨35078812332938828111303171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23385874888625885407535447 35078812332938828111303171)
              ·
                refine ⟨52618218499408242166954757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35078812332938828111303171 52618218499408242166954757)
                ·
                  refine ⟨9865915968639045406304017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52618218499408242166954757 9865915968639045406304017)
                  ·
                    refine ⟨7399436976479284054728013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9865915968639045406304017 7399436976479284054728013)
                    ·
                      refine ⟨2774788866179731520523005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7399436976479284054728013 2774788866179731520523005)
                      ·
                        rfl

theorem cell23_5403882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_5403882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403882 prefixEnd_5403882 := by exact prefixLift 5403882
  have htrace : WordTrace (prefixWord ++ tailWord_5403882) baseStart_5403882 baseEnd_5403882 := by
    simpa [prefixWord, tailWord_5403882, baseEnd_5403882] using wordTrace_append hprefix tailTrace_5403882
  have hstable : (prefixWord ++ tailWord_5403882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403882).length < 2 ^ (prefixWord ++ tailWord_5403882).sum := by decide
  have hdescent : baseEnd_5403882 < baseStart_5403882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403932 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_5403932 : Nat := 118140960795 + 5403932 * 2 ^ 59
def prefixEnd_5403932 : Nat := 4983230072969 + 3 ^ 40 * 5403932 * 2
def baseEnd_5403932 : Nat := 924938180070818774965925

theorem tailTrace_5403932 : CollatzResearch.WordTrace tailWord_5403932 prefixEnd_5403932 924938180070818774965925 := by
  unfold tailWord_5403932
  simp only [CollatzResearch.WordTrace]
  refine ⟨98548796129242378476723025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131398394838989837968964033 98548796129242378476723025)
  ·
    refine ⟨73911597096931783857542269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98548796129242378476723025 73911597096931783857542269)
    ·
      refine ⟨27716848911349418946578351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73911597096931783857542269 27716848911349418946578351)
      ·
        refine ⟨41575273367024128419867527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27716848911349418946578351 41575273367024128419867527)
        ·
          refine ⟨62362910050536192629801291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41575273367024128419867527 62362910050536192629801291)
          ·
            refine ⟨93544365075804288944701937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62362910050536192629801291 93544365075804288944701937)
            ·
              refine ⟨70158273806853216708526453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93544365075804288944701937 70158273806853216708526453)
              ·
                refine ⟨6577338169392489066424355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70158273806853216708526453 6577338169392489066424355)
                ·
                  refine ⟨9866007254088733599636533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577338169392489066424355 9866007254088733599636533)
                  ·
                    refine ⟨924938180070818774965925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9866007254088733599636533 924938180070818774965925)
                    ·
                      rfl

theorem cell23_5403932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_5403932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403932 prefixEnd_5403932 := by exact prefixLift 5403932
  have htrace : WordTrace (prefixWord ++ tailWord_5403932) baseStart_5403932 baseEnd_5403932 := by
    simpa [prefixWord, tailWord_5403932, baseEnd_5403932] using wordTrace_append hprefix tailTrace_5403932
  have hstable : (prefixWord ++ tailWord_5403932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403932).length < 2 ^ (prefixWord ++ tailWord_5403932).sum := by decide
  have hdescent : baseEnd_5403932 < baseStart_5403932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403939 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 2, 3, 2]
def baseStart_5403939 : Nat := 118140960795 + 5403939 * 2 ^ 59
def prefixEnd_5403939 : Nat := 4983230072969 + 3 ^ 40 * 5403939 * 2
def baseEnd_5403939 : Nat := 2774818134577037797510243

theorem tailTrace_5403939 : CollatzResearch.WordTrace tailWord_5403939 prefixEnd_5403939 2774818134577037797510243 := by
  unfold tailWord_5403939
  simp only [CollatzResearch.WordTrace]
  refine ⟨197097847569459397148950871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131398565046306264765967247 197097847569459397148950871)
  ·
    refine ⟨295646771354189095723426307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197097847569459397148950871 295646771354189095723426307)
    ·
      refine ⟨443470157031283643585139461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295646771354189095723426307 443470157031283643585139461)
      ·
        refine ⟨83150654443365683172213649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 443470157031283643585139461 83150654443365683172213649)
        ·
          refine ⟨62362990832524262379160237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83150654443365683172213649 62362990832524262379160237)
          ·
            refine ⟨23386121562196598392185089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62362990832524262379160237 23386121562196598392185089)
            ·
              refine ⟨17539591171647448794138817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23386121562196598392185089 17539591171647448794138817)
              ·
                refine ⟨13154693378735586595604113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17539591171647448794138817 13154693378735586595604113)
                ·
                  refine ⟨9866020034051689946703085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13154693378735586595604113 9866020034051689946703085)
                  ·
                    refine ⟨3699757512769383730013657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9866020034051689946703085 3699757512769383730013657)
                    ·
                      refine ⟨2774818134577037797510243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699757512769383730013657 2774818134577037797510243)
                      ·
                        rfl

theorem cell23_5403939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_5403939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403939 prefixEnd_5403939 := by exact prefixLift 5403939
  have htrace : WordTrace (prefixWord ++ tailWord_5403939) baseStart_5403939 baseEnd_5403939 := by
    simpa [prefixWord, tailWord_5403939, baseEnd_5403939] using wordTrace_append hprefix tailTrace_5403939
  have hstable : (prefixWord ++ tailWord_5403939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403939).length < 2 ^ (prefixWord ++ tailWord_5403939).sum := by decide
  have hdescent : baseEnd_5403939 < baseStart_5403939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403949 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5403949 : Nat := 118140960795 + 5403949 * 2 ^ 59
def prefixEnd_5403949 : Nat := 4983230072969 + 3 ^ 40 * 5403949 * 2
def baseEnd_5403949 : Nat := 924941089794527586128399

theorem tailTrace_5403949 : CollatzResearch.WordTrace tailWord_5403949 prefixEnd_5403949 924941089794527586128399 := by
  unfold tailWord_5403949
  simp only [CollatzResearch.WordTrace]
  refine ⟨197098212299423168856814901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131398808199615445904543267 197098212299423168856814901)
  ·
    refine ⟨18477957403070922080326397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197098212299423168856814901 18477957403070922080326397)
    ·
      refine ⟨6929234026151595780122399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18477957403070922080326397 6929234026151595780122399)
      ·
        refine ⟨10393851039227393670183599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929234026151595780122399 10393851039227393670183599)
        ·
          refine ⟨15590776558841090505275399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393851039227393670183599 15590776558841090505275399)
          ·
            refine ⟨23386164838261635757913099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590776558841090505275399 23386164838261635757913099)
            ·
              refine ⟨35079247257392453636869649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23386164838261635757913099 35079247257392453636869649)
              ·
                refine ⟨26309435443044340227652237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35079247257392453636869649 26309435443044340227652237)
                ·
                  refine ⟨9866038291141627585369589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26309435443044340227652237 9866038291141627585369589)
                  ·
                    refine ⟨924941089794527586128399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9866038291141627585369589 924941089794527586128399)
                    ·
                      rfl

theorem cell23_5403949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5403949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403949 prefixEnd_5403949 := by exact prefixLift 5403949
  have htrace : WordTrace (prefixWord ++ tailWord_5403949) baseStart_5403949 baseEnd_5403949 := by
    simpa [prefixWord, tailWord_5403949, baseEnd_5403949] using wordTrace_append hprefix tailTrace_5403949
  have hstable : (prefixWord ++ tailWord_5403949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403949).length < 2 ^ (prefixWord ++ tailWord_5403949).sum := by decide
  have hdescent : baseEnd_5403949 < baseStart_5403949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403962 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_5403962 : Nat := 118140960795 + 5403962 * 2 ^ 59
def prefixEnd_5403962 : Nat := 4983230072969 + 3 ^ 40 * 5403962 * 2
def baseEnd_5403962 : Nat := 924943314877363735840879

theorem tailTrace_5403962 : CollatzResearch.WordTrace tailWord_5403962 prefixEnd_5403962 924943314877363735840879 := by
  unfold tailWord_5403962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49274671612094018019259535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131399124298917381384692093 49274671612094018019259535)
  ·
    refine ⟨73912007418141027028889303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49274671612094018019259535 73912007418141027028889303)
    ·
      refine ⟨110868011127211540543333955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73912007418141027028889303 110868011127211540543333955)
      ·
        refine ⟨166302016690817310815000933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110868011127211540543333955 166302016690817310815000933)
        ·
          refine ⟨31181628129528245777812675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166302016690817310815000933 31181628129528245777812675)
          ·
            refine ⟨46772442194292368666719013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31181628129528245777812675 46772442194292368666719013)
            ·
              refine ⟨8769832911429819125009815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46772442194292368666719013 8769832911429819125009815)
              ·
                refine ⟨13154749367144728687514723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8769832911429819125009815 13154749367144728687514723)
                ·
                  refine ⟨19732124050717093031272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13154749367144728687514723 19732124050717093031272085)
                  ·
                    refine ⟨924943314877363735840879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19732124050717093031272085 924943314877363735840879)
                    ·
                      rfl

theorem cell23_5403962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_5403962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403962 prefixEnd_5403962 := by exact prefixLift 5403962
  have htrace : WordTrace (prefixWord ++ tailWord_5403962) baseStart_5403962 baseEnd_5403962 := by
    simpa [prefixWord, tailWord_5403962, baseEnd_5403962] using wordTrace_append hprefix tailTrace_5403962
  have hstable : (prefixWord ++ tailWord_5403962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403962).length < 2 ^ (prefixWord ++ tailWord_5403962).sum := by decide
  have hdescent : baseEnd_5403962 < baseStart_5403962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403969 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5403969 : Nat := 118140960795 + 5403969 * 2 ^ 59
def prefixEnd_5403969 : Nat := 4983230072969 + 3 ^ 40 * 5403969 * 2
def baseEnd_5403969 : Nat := 2774833538996672680135105

theorem tailTrace_5403969 : CollatzResearch.WordTrace tailWord_5403969 prefixEnd_5403969 2774833538996672680135105 := by
  unfold tailWord_5403969
  simp only [CollatzResearch.WordTrace]
  refine ⟨197098941759350712272542961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131399294506233808181695307 197098941759350712272542961)
  ·
    refine ⟨147824206319513034204407221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197098941759350712272542961 147824206319513034204407221)
    ·
      refine ⟨13858519342454346956663177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147824206319513034204407221 13858519342454346956663177)
      ·
        refine ⟨10393889506840760217497383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13858519342454346956663177 10393889506840760217497383)
        ·
          refine ⟨15590834260261140326246075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393889506840760217497383 15590834260261140326246075)
          ·
            refine ⟨23386251390391710489369113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590834260261140326246075 23386251390391710489369113)
            ·
              refine ⟨17539688542793782867026835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23386251390391710489369113 17539688542793782867026835)
              ·
                refine ⟨26309532814190674300540253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17539688542793782867026835 26309532814190674300540253)
                ·
                  refine ⟨9866074805321502862702595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26309532814190674300540253 9866074805321502862702595)
                  ·
                    refine ⟨14799112207982254294053893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9866074805321502862702595 14799112207982254294053893)
                    ·
                      refine ⟨2774833538996672680135105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14799112207982254294053893 2774833538996672680135105)
                      ·
                        rfl

theorem cell23_5403969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5403969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403969 prefixEnd_5403969 := by exact prefixLift 5403969
  have htrace : WordTrace (prefixWord ++ tailWord_5403969) baseStart_5403969 baseEnd_5403969 := by
    simpa [prefixWord, tailWord_5403969, baseEnd_5403969] using wordTrace_append hprefix tailTrace_5403969
  have hstable : (prefixWord ++ tailWord_5403969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403969).length < 2 ^ (prefixWord ++ tailWord_5403969).sum := by decide
  have hdescent : baseEnd_5403969 < baseStart_5403969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5403982 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_5403982 : Nat := 118140960795 + 5403982 * 2 ^ 59
def prefixEnd_5403982 : Nat := 4983230072969 + 3 ^ 40 * 5403982 * 2
def baseEnd_5403982 : Nat := 2774840214245181129272545

theorem tailTrace_5403982 : CollatzResearch.WordTrace tailWord_5403982 prefixEnd_5403982 2774840214245181129272545 := by
  unfold tailWord_5403982
  simp only [CollatzResearch.WordTrace]
  refine ⟨24637426988537951936595775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131399610605535743661844133 24637426988537951936595775)
  ·
    refine ⟨36956140482806927904893663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24637426988537951936595775 36956140482806927904893663)
    ·
      refine ⟨55434210724210391857340495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36956140482806927904893663 55434210724210391857340495)
      ·
        refine ⟨83151316086315587786010743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55434210724210391857340495 83151316086315587786010743)
        ·
          refine ⟨124726974129473381679016115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83151316086315587786010743 124726974129473381679016115)
          ·
            refine ⟨187090461194210072518524173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124726974129473381679016115 187090461194210072518524173)
            ·
              refine ⟨70158922947828777194446565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187090461194210072518524173 70158922947828777194446565)
              ·
                refine ⟨13154798052717895723958731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70158922947828777194446565 13154798052717895723958731)
                ·
                  refine ⟨19732197079076843585938097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13154798052717895723958731 19732197079076843585938097)
                  ·
                    refine ⟨14799147809307632689453573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19732197079076843585938097 14799147809307632689453573)
                    ·
                      refine ⟨2774840214245181129272545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14799147809307632689453573 2774840214245181129272545)
                      ·
                        rfl

theorem cell23_5403982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_5403982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5403982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5403982 prefixEnd_5403982 := by exact prefixLift 5403982
  have htrace : WordTrace (prefixWord ++ tailWord_5403982) baseStart_5403982 baseEnd_5403982 := by
    simpa [prefixWord, tailWord_5403982, baseEnd_5403982] using wordTrace_append hprefix tailTrace_5403982
  have hstable : (prefixWord ++ tailWord_5403982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5403982).length < 2 ^ (prefixWord ++ tailWord_5403982).sum := by decide
  have hdescent : baseEnd_5403982 < baseStart_5403982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5403982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404003 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 1, 2, 2]
def baseStart_5404003 : Nat := 118140960795 + 5404003 * 2 ^ 59
def prefixEnd_5404003 : Nat := 4983230072969 + 3 ^ 40 * 5404003 * 2
def baseEnd_5404003 : Nat := 2774850997338925547109949

theorem tailTrace_5404003 : CollatzResearch.WordTrace tailWord_5404003 prefixEnd_5404003 2774850997338925547109949 := by
  unfold tailWord_5404003
  simp only [CollatzResearch.WordTrace]
  refine ⟨197100181841227536079280663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131400121227485024052853775 197100181841227536079280663)
  ·
    refine ⟨295650272761841304118920995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197100181841227536079280663 295650272761841304118920995)
    ·
      refine ⟨443475409142761956178381493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295650272761841304118920995 443475409142761956178381493)
      ·
        refine ⟨41575819607133933391723265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443475409142761956178381493 41575819607133933391723265)
        ·
          refine ⟨31181864705350450043792449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41575819607133933391723265 31181864705350450043792449)
          ·
            refine ⟨23386398529012837532844337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31181864705350450043792449 23386398529012837532844337)
            ·
              refine ⟨17539798896759628149633253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23386398529012837532844337 17539798896759628149633253)
              ·
                refine ⟨3288712293142430278056235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17539798896759628149633253 3288712293142430278056235)
                ·
                  refine ⟨4933068439713645417084353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288712293142430278056235 4933068439713645417084353)
                  ·
                    refine ⟨3699801329785234062813265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4933068439713645417084353 3699801329785234062813265)
                    ·
                      refine ⟨2774850997338925547109949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3699801329785234062813265 2774850997338925547109949)
                      ·
                        rfl

theorem cell23_5404003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_5404003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404003 prefixEnd_5404003 := by exact prefixLift 5404003
  have htrace : WordTrace (prefixWord ++ tailWord_5404003) baseStart_5404003 baseEnd_5404003 := by
    simpa [prefixWord, tailWord_5404003, baseEnd_5404003] using wordTrace_append hprefix tailTrace_5404003
  have hstable : (prefixWord ++ tailWord_5404003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404003).length < 2 ^ (prefixWord ++ tailWord_5404003).sum := by decide
  have hdescent : baseEnd_5404003 < baseStart_5404003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404146 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_5404146 : Nat := 118140960795 + 5404146 * 2 ^ 59
def prefixEnd_5404146 : Nat := 4983230072969 + 3 ^ 40 * 5404146 * 2
def baseEnd_5404146 : Nat := 924974808357506162540597

theorem tailTrace_5404146 : CollatzResearch.WordTrace tailWord_5404146 prefixEnd_5404146 924974808357506162540597 := by
  unfold tailWord_5404146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49276349369927367875434073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131403598319806314334490861 49276349369927367875434073)
  ·
    refine ⟨36957262027445525906575555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49276349369927367875434073 36957262027445525906575555)
    ·
      refine ⟨55435893041168288859863333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36957262027445525906575555 55435893041168288859863333)
      ·
        refine ⟨10394229945219054161224375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55435893041168288859863333 10394229945219054161224375)
        ·
          refine ⟨15591344917828581241836563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10394229945219054161224375 15591344917828581241836563)
          ·
            refine ⟨23387017376742871862754845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15591344917828581241836563 23387017376742871862754845)
            ·
              refine ⟨8770131516278576948533067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23387017376742871862754845 8770131516278576948533067)
              ·
                refine ⟨13155197274417865422799601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8770131516278576948533067 13155197274417865422799601)
                ·
                  refine ⟨9866397955813399067099701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13155197274417865422799601 9866397955813399067099701)
                  ·
                    refine ⟨924974808357506162540597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9866397955813399067099701 924974808357506162540597)
                    ·
                      rfl

theorem cell23_5404146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_5404146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404146 prefixEnd_5404146 := by exact prefixLift 5404146
  have htrace : WordTrace (prefixWord ++ tailWord_5404146) baseStart_5404146 baseEnd_5404146 := by
    simpa [prefixWord, tailWord_5404146, baseEnd_5404146] using wordTrace_append hprefix tailTrace_5404146
  have hstable : (prefixWord ++ tailWord_5404146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404146).length < 2 ^ (prefixWord ++ tailWord_5404146).sum := by decide
  have hdescent : baseEnd_5404146 < baseStart_5404146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404169 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_5404169 : Nat := 118140960795 + 5404169 * 2 ^ 59
def prefixEnd_5404169 : Nat := 4983230072969 + 3 ^ 40 * 5404169 * 2
def baseEnd_5404169 : Nat := 2774936235127571897634185

theorem tailTrace_5404169 : CollatzResearch.WordTrace tailWord_5404169 prefixEnd_5404169 2774936235127571897634185 := by
  unfold tailWord_5404169
  simp only [CollatzResearch.WordTrace]
  refine ⟨197106236358626146429823561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131404157572417430953215707 197106236358626146429823561)
  ·
    refine ⟨147829677268969609822367671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197106236358626146429823561 147829677268969609822367671)
    ·
      refine ⟨221744515903454414733551507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147829677268969609822367671 221744515903454414733551507)
      ·
        refine ⟨332616773855181622100327261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221744515903454414733551507 332616773855181622100327261)
        ·
          refine ⟨124731290195693108287622723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332616773855181622100327261 124731290195693108287622723)
          ·
            refine ⟨187096935293539662431434085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124731290195693108287622723 187096935293539662431434085)
            ·
              refine ⟨35080675367538686705893891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187096935293539662431434085 35080675367538686705893891)
              ·
                refine ⟨52621013051308030058840837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35080675367538686705893891 52621013051308030058840837)
                ·
                  refine ⟨9866439947120255636032657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52621013051308030058840837 9866439947120255636032657)
                  ·
                    refine ⟨7399829960340191727024493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9866439947120255636032657 7399829960340191727024493)
                    ·
                      refine ⟨2774936235127571897634185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7399829960340191727024493 2774936235127571897634185)
                      ·
                        rfl

theorem cell23_5404169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_5404169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404169 prefixEnd_5404169 := by exact prefixLift 5404169
  have htrace : WordTrace (prefixWord ++ tailWord_5404169) baseStart_5404169 baseEnd_5404169 := by
    simpa [prefixWord, tailWord_5404169, baseEnd_5404169] using wordTrace_append hprefix tailTrace_5404169
  have hstable : (prefixWord ++ tailWord_5404169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404169).length < 2 ^ (prefixWord ++ tailWord_5404169).sum := by decide
  have hdescent : baseEnd_5404169 < baseStart_5404169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404233 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 1, 1, 3]
def baseStart_5404233 : Nat := 118140960795 + 5404233 * 2 ^ 59
def prefixEnd_5404233 : Nat := 4983230072969 + 3 ^ 40 * 5404233 * 2
def baseEnd_5404233 : Nat := 2774969097889459647233891

theorem tailTrace_5404233 : CollatzResearch.WordTrace tailWord_5404233 prefixEnd_5404233 2774969097889459647233891 := by
  unfold tailWord_5404233
  simp only [CollatzResearch.WordTrace]
  refine ⟨197108570630394285360153353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131405713753596190240102235 197108570630394285360153353)
  ·
    refine ⟨147831427972795714020115015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197108570630394285360153353 147831427972795714020115015)
    ·
      refine ⟨221747141959193571030172523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147831427972795714020115015 221747141959193571030172523)
      ·
        refine ⟨332620712938790356545258785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221747141959193571030172523 332620712938790356545258785)
        ·
          refine ⟨249465534704092767408944089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332620712938790356545258785 249465534704092767408944089)
          ·
            refine ⟨187099151028069575556708067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249465534704092767408944089 187099151028069575556708067)
            ·
              refine ⟨280648726542104363335062101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187099151028069575556708067 280648726542104363335062101)
              ·
                refine ⟨3288852264165285507832759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 280648726542104363335062101 3288852264165285507832759)
                ·
                  refine ⟨4933278396247928261749139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288852264165285507832759 4933278396247928261749139)
                  ·
                    refine ⟨7399917594371892392623709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4933278396247928261749139 7399917594371892392623709)
                    ·
                      refine ⟨2774969097889459647233891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7399917594371892392623709 2774969097889459647233891)
                      ·
                        rfl

theorem cell23_5404233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 1, 3].length) (baseStart_5404233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404233 prefixEnd_5404233 := by exact prefixLift 5404233
  have htrace : WordTrace (prefixWord ++ tailWord_5404233) baseStart_5404233 baseEnd_5404233 := by
    simpa [prefixWord, tailWord_5404233, baseEnd_5404233] using wordTrace_append hprefix tailTrace_5404233
  have hstable : (prefixWord ++ tailWord_5404233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404233).length < 2 ^ (prefixWord ++ tailWord_5404233).sum := by decide
  have hdescent : baseEnd_5404233 < baseStart_5404233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404239 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_5404239 : Nat := 118140960795 + 5404239 * 2 ^ 59
def prefixEnd_5404239 : Nat := 4983230072969 + 3 ^ 40 * 5404239 * 2
def baseEnd_5404239 : Nat := 2774972178773386623758863

theorem tailTrace_5404239 : CollatzResearch.WordTrace tailWord_5404239 prefixEnd_5404239 2774972178773386623758863 := by
  unfold tailWord_5404239
  simp only [CollatzResearch.WordTrace]
  refine ⟨197108789468372548384871771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131405859645581698923247847 197108789468372548384871771)
  ·
    refine ⟨295663184202558822577307657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197108789468372548384871771 295663184202558822577307657)
    ·
      refine ⟨221747388151919116932980743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295663184202558822577307657 221747388151919116932980743)
      ·
        refine ⟨332621082227878675399471115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221747388151919116932980743 332621082227878675399471115)
        ·
          refine ⟨498931623341818013099206673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332621082227878675399471115 498931623341818013099206673)
          ·
            refine ⟨374198717506363509824405005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498931623341818013099206673 374198717506363509824405005)
            ·
              refine ⟨140324519064886316184151877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374198717506363509824405005 140324519064886316184151877)
              ·
                refine ⟨26310847324666184284528477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140324519064886316184151877 26310847324666184284528477)
                ·
                  refine ⟨9866567746749819106698179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26310847324666184284528477 9866567746749819106698179)
                  ·
                    refine ⟨14799851620124728660047269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9866567746749819106698179 14799851620124728660047269)
                    ·
                      refine ⟨2774972178773386623758863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14799851620124728660047269 2774972178773386623758863)
                      ·
                        rfl

theorem cell23_5404239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_5404239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404239 prefixEnd_5404239 := by exact prefixLift 5404239
  have htrace : WordTrace (prefixWord ++ tailWord_5404239) baseStart_5404239 baseEnd_5404239 := by
    simpa [prefixWord, tailWord_5404239, baseEnd_5404239] using wordTrace_append hprefix tailTrace_5404239
  have hstable : (prefixWord ++ tailWord_5404239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404239).length < 2 ^ (prefixWord ++ tailWord_5404239).sum := by decide
  have hdescent : baseEnd_5404239 < baseStart_5404239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404266 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_5404266 : Nat := 118140960795 + 5404266 * 2 ^ 59
def prefixEnd_5404266 : Nat := 4983230072969 + 3 ^ 40 * 5404266 * 2
def baseEnd_5404266 : Nat := 924995347583686006040413

theorem tailTrace_5404266 : CollatzResearch.WordTrace tailWord_5404266 prefixEnd_5404266 924995347583686006040413 := by
  unfold tailWord_5404266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49277443559818682999026163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131406516159516487997403101 49277443559818682999026163)
  ·
    refine ⟨73916165339728024498539245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49277443559818682999026163 73916165339728024498539245)
    ·
      refine ⟨27718562002398009186952217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73916165339728024498539245 27718562002398009186952217)
      ·
        refine ⟨20788921501798506890214163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27718562002398009186952217 20788921501798506890214163)
        ·
          refine ⟨31183382252697760335321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20788921501798506890214163 31183382252697760335321245)
          ·
            refine ⟨11693768344761660125745467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31183382252697760335321245 11693768344761660125745467)
            ·
              refine ⟨17540652517142490188618201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11693768344761660125745467 17540652517142490188618201)
              ·
                refine ⟨13155489387856867641463651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17540652517142490188618201 13155489387856867641463651)
                ·
                  refine ⟨19733234081785301462195477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13155489387856867641463651 19733234081785301462195477)
                  ·
                    refine ⟨924995347583686006040413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19733234081785301462195477 924995347583686006040413)
                    ·
                      rfl

theorem cell23_5404266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_5404266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404266 prefixEnd_5404266 := by exact prefixLift 5404266
  have htrace : WordTrace (prefixWord ++ tailWord_5404266) baseStart_5404266 baseEnd_5404266 := by
    simpa [prefixWord, tailWord_5404266, baseEnd_5404266] using wordTrace_append hprefix tailTrace_5404266
  have hstable : (prefixWord ++ tailWord_5404266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404266).length < 2 ^ (prefixWord ++ tailWord_5404266).sum := by decide
  have hdescent : baseEnd_5404266 < baseStart_5404266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404270 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_5404270 : Nat := 118140960795 + 5404270 * 2 ^ 59
def prefixEnd_5404270 : Nat := 4983230072969 + 3 ^ 40 * 5404270 * 2
def baseEnd_5404270 : Nat := 924996032224558667490407

theorem tailTrace_5404270 : CollatzResearch.WordTrace tailWord_5404270 prefixEnd_5404270 924996032224558667490407 := by
  unfold tailWord_5404270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24638740016407530084906283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131406613420840160452833509 24638740016407530084906283)
  ·
    refine ⟨36958110024611295127359425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24638740016407530084906283 36958110024611295127359425)
    ·
      refine ⟨27718582518458471345519569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36958110024611295127359425 27718582518458471345519569)
      ·
        refine ⟨20788936888843853509139677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27718582518458471345519569 20788936888843853509139677)
        ·
          refine ⟨7795851333316445065927379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20788936888843853509139677 7795851333316445065927379)
          ·
            refine ⟨11693776999974667598891069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795851333316445065927379 11693776999974667598891069)
            ·
              refine ⟨4385166374990500349584151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11693776999974667598891069 4385166374990500349584151)
              ·
                refine ⟨6577749562485750524376227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385166374990500349584151 6577749562485750524376227)
                ·
                  refine ⟨9866624343728625786564341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577749562485750524376227 9866624343728625786564341)
                  ·
                    refine ⟨924996032224558667490407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9866624343728625786564341 924996032224558667490407)
                    ·
                      rfl

theorem cell23_5404270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_5404270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404270 prefixEnd_5404270 := by exact prefixLift 5404270
  have htrace : WordTrace (prefixWord ++ tailWord_5404270) baseStart_5404270 baseEnd_5404270 := by
    simpa [prefixWord, tailWord_5404270, baseEnd_5404270] using wordTrace_append hprefix tailTrace_5404270
  have hstable : (prefixWord ++ tailWord_5404270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404270).length < 2 ^ (prefixWord ++ tailWord_5404270).sum := by decide
  have hdescent : baseEnd_5404270 < baseStart_5404270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404334 : List Nat := [4, 1, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_5404334 : Nat := 118140960795 + 5404334 * 2 ^ 59
def prefixEnd_5404334 : Nat := 4983230072969 + 3 ^ 40 * 5404334 * 2
def baseEnd_5404334 : Nat := 925006986478521250690309

theorem tailTrace_5404334 : CollatzResearch.WordTrace tailWord_5404334 prefixEnd_5404334 925006986478521250690309 := by
  unfold tailWord_5404334
  simp only [CollatzResearch.WordTrace]
  refine ⟨24639031800378547451197507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131408169602018919739720037 24639031800378547451197507)
  ·
    refine ⟨36958547700567821176796261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24639031800378547451197507 36958547700567821176796261)
    ·
      refine ⟨6929727693856466470649299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36958547700567821176796261 6929727693856466470649299)
      ·
        refine ⟨10394591540784699705973949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929727693856466470649299 10394591540784699705973949)
        ·
          refine ⟨3897971827794262389740231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10394591540784699705973949 3897971827794262389740231)
          ·
            refine ⟨5846957741691393584610347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897971827794262389740231 5846957741691393584610347)
            ·
              refine ⟨8770436612537090376915521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846957741691393584610347 8770436612537090376915521)
              ·
                refine ⟨6577827459402817782686641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8770436612537090376915521 6577827459402817782686641)
                ·
                  refine ⟨4933370594552113337014981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6577827459402817782686641 4933370594552113337014981)
                  ·
                    refine ⟨925006986478521250690309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933370594552113337014981 925006986478521250690309)
                    ·
                      rfl

theorem cell23_5404334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_5404334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404334 prefixEnd_5404334 := by exact prefixLift 5404334
  have htrace : WordTrace (prefixWord ++ tailWord_5404334) baseStart_5404334 baseEnd_5404334 := by
    simpa [prefixWord, tailWord_5404334, baseEnd_5404334] using wordTrace_append hprefix tailTrace_5404334
  have hstable : (prefixWord ++ tailWord_5404334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404334).length < 2 ^ (prefixWord ++ tailWord_5404334).sum := by decide
  have hdescent : baseEnd_5404334 < baseStart_5404334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404339 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 4, 6]
def baseStart_5404339 : Nat := 118140960795 + 5404339 * 2 ^ 59
def prefixEnd_5404339 : Nat := 4983230072969 + 3 ^ 40 * 5404339 * 2
def baseEnd_5404339 : Nat := 925007842279612077502801

theorem tailTrace_5404339 : CollatzResearch.WordTrace tailWord_5404339 prefixEnd_5404339 925007842279612077502801 := by
  unfold tailWord_5404339
  simp only [CollatzResearch.WordTrace]
  refine ⟨197112436768010265463512071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131408291178673510309008047 197112436768010265463512071)
  ·
    refine ⟨295668655152015398195268107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197112436768010265463512071 295668655152015398195268107)
    ·
      refine ⟨443502982728023097292902161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295668655152015398195268107 443502982728023097292902161)
      ·
        refine ⟨332627237046017322969676621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443502982728023097292902161 332627237046017322969676621)
        ·
          refine ⟨124735213892256496113628733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332627237046017322969676621 124735213892256496113628733)
          ·
            refine ⟨46775705209596186042610775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124735213892256496113628733 46775705209596186042610775)
            ·
              refine ⟨70163557814394279063916163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46775705209596186042610775 70163557814394279063916163)
              ·
                refine ⟨105245336721591418595874245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70163557814394279063916163 105245336721591418595874245)
                ·
                  refine ⟨19733500635298390986726421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105245336721591418595874245 19733500635298390986726421)
                  ·
                    refine ⟨925007842279612077502801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19733500635298390986726421 925007842279612077502801)
                    ·
                      rfl

theorem cell23_5404339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 6].length) (baseStart_5404339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404339 prefixEnd_5404339 := by exact prefixLift 5404339
  have htrace : WordTrace (prefixWord ++ tailWord_5404339) baseStart_5404339 baseEnd_5404339 := by
    simpa [prefixWord, tailWord_5404339, baseEnd_5404339] using wordTrace_append hprefix tailTrace_5404339
  have hstable : (prefixWord ++ tailWord_5404339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404339).length < 2 ^ (prefixWord ++ tailWord_5404339).sum := by decide
  have hdescent : baseEnd_5404339 < baseStart_5404339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404354 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5404354 : Nat := 118140960795 + 5404354 * 2 ^ 59
def prefixEnd_5404354 : Nat := 4983230072969 + 3 ^ 40 * 5404354 * 2
def baseEnd_5404354 : Nat := 2775031229048653673820835

theorem tailTrace_5404354 : CollatzResearch.WordTrace tailWord_5404354 prefixEnd_5404354 2775031229048653673820835 := by
  unfold tailWord_5404354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49278245965738980756327029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131408655908637282016872077 49278245965738980756327029)
  ·
    refine ⟨4619835559288029445905659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49278245965738980756327029 4619835559288029445905659)
    ·
      refine ⟨6929753338932044168858489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619835559288029445905659 6929753338932044168858489)
      ·
        refine ⟨5197315004199033126643867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6929753338932044168858489 5197315004199033126643867)
        ·
          refine ⟨7795972506298549689965801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197315004199033126643867 7795972506298549689965801)
          ·
            refine ⟨5846979379723912267474351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7795972506298549689965801 5846979379723912267474351)
            ·
              refine ⟨8770469069585868401211527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846979379723912267474351 8770469069585868401211527)
              ·
                refine ⟨13155703604378802601817291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8770469069585868401211527 13155703604378802601817291)
                ·
                  refine ⟨19733555406568203902725937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13155703604378802601817291 19733555406568203902725937)
                  ·
                    refine ⟨14800166554926152927044453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19733555406568203902725937 14800166554926152927044453)
                    ·
                      refine ⟨2775031229048653673820835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14800166554926152927044453 2775031229048653673820835)
                      ·
                        rfl

theorem cell23_5404354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5404354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404354 prefixEnd_5404354 := by exact prefixLift 5404354
  have htrace : WordTrace (prefixWord ++ tailWord_5404354) baseStart_5404354 baseEnd_5404354 := by
    simpa [prefixWord, tailWord_5404354, baseEnd_5404354] using wordTrace_append hprefix tailTrace_5404354
  have hstable : (prefixWord ++ tailWord_5404354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404354).length < 2 ^ (prefixWord ++ tailWord_5404354).sum := by decide
  have hdescent : baseEnd_5404354 < baseStart_5404354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404356 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_5404356 : Nat := 118140960795 + 5404356 * 2 ^ 59
def prefixEnd_5404356 : Nat := 4983230072969 + 3 ^ 40 * 5404356 * 2
def baseEnd_5404356 : Nat := 925010752003320888665275

theorem tailTrace_5404356 : CollatzResearch.WordTrace tailWord_5404356 prefixEnd_5404356 925010752003320888665275 := by
  unfold tailWord_5404356
  simp only [CollatzResearch.WordTrace]
  refine ⟨98556528404474338683440461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131408704539299118244587281 98556528404474338683440461)
  ·
    refine ⟨36958698151677877006290173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98556528404474338683440461 36958698151677877006290173)
    ·
      refine ⟨13859511806879203877358815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36958698151677877006290173 13859511806879203877358815)
      ·
        refine ⟨20789267710318805816038223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859511806879203877358815 20789267710318805816038223)
        ·
          refine ⟨31183901565478208724057335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20789267710318805816038223 31183901565478208724057335)
          ·
            refine ⟨46775852348217313086086003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31183901565478208724057335 46775852348217313086086003)
            ·
              refine ⟨70163778522325969629129005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46775852348217313086086003 70163778522325969629129005)
              ·
                refine ⟨26311416945872238610923377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70163778522325969629129005 26311416945872238610923377)
                ·
                  refine ⟨19733562709404178958192533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26311416945872238610923377 19733562709404178958192533)
                  ·
                    refine ⟨925010752003320888665275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19733562709404178958192533 925010752003320888665275)
                    ·
                      rfl

theorem cell23_5404356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_5404356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404356 prefixEnd_5404356 := by exact prefixLift 5404356
  have htrace : WordTrace (prefixWord ++ tailWord_5404356) baseStart_5404356 baseEnd_5404356 := by
    simpa [prefixWord, tailWord_5404356, baseEnd_5404356] using wordTrace_append hprefix tailTrace_5404356
  have hstable : (prefixWord ++ tailWord_5404356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404356).length < 2 ^ (prefixWord ++ tailWord_5404356).sum := by decide
  have hdescent : baseEnd_5404356 < baseStart_5404356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404366 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_5404366 : Nat := 118140960795 + 5404366 * 2 ^ 59
def prefixEnd_5404366 : Nat := 4983230072969 + 3 ^ 40 * 5404366 * 2
def baseEnd_5404366 : Nat := 2775037390816507626870779

theorem tailTrace_5404366 : CollatzResearch.WordTrace tailWord_5404366 prefixEnd_5404366 2775037390816507626870779 := by
  unfold tailWord_5404366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24639177692364056134343119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131408947692608299383163301 24639177692364056134343119)
  ·
    refine ⟨36958766538546084201514679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24639177692364056134343119 36958766538546084201514679)
    ·
      refine ⟨55438149807819126302272019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36958766538546084201514679 55438149807819126302272019)
      ·
        refine ⟨83157224711728689453408029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55438149807819126302272019 83157224711728689453408029)
        ·
          refine ⟨31183959266898258545028011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83157224711728689453408029 31183959266898258545028011)
          ·
            refine ⟨46775938900347387817542017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31183959266898258545028011 46775938900347387817542017)
            ·
              refine ⟨35081954175260540863156513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46775938900347387817542017 35081954175260540863156513)
              ·
                refine ⟨26311465631445405647367385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35081954175260540863156513 26311465631445405647367385)
                ·
                  refine ⟨19733599223584054235525539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26311465631445405647367385 19733599223584054235525539)
                  ·
                    refine ⟨29600398835376081353288309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19733599223584054235525539 29600398835376081353288309)
                    ·
                      refine ⟨2775037390816507626870779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29600398835376081353288309 2775037390816507626870779)
                      ·
                        rfl

theorem cell23_5404366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_5404366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404366 prefixEnd_5404366 := by exact prefixLift 5404366
  have htrace : WordTrace (prefixWord ++ tailWord_5404366) baseStart_5404366 baseEnd_5404366 := by
    simpa [prefixWord, tailWord_5404366, baseEnd_5404366] using wordTrace_append hprefix tailTrace_5404366
  have hstable : (prefixWord ++ tailWord_5404366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404366).length < 2 ^ (prefixWord ++ tailWord_5404366).sum := by decide
  have hdescent : baseEnd_5404366 < baseStart_5404366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404396 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_5404396 : Nat := 118140960795 + 5404396 * 2 ^ 59
def prefixEnd_5404396 : Nat := 4983230072969 + 3 ^ 40 * 5404396 * 2
def baseEnd_5404396 : Nat := 2775052795236142509495641

theorem tailTrace_5404396 : CollatzResearch.WordTrace tailWord_5404396 prefixEnd_5404396 2775052795236142509495641 := by
  unfold tailWord_5404396
  simp only [CollatzResearch.WordTrace]
  refine ⟨98557257864401882099168521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131409677152535842798891361 98557257864401882099168521)
  ·
    refine ⟨73917943398301411574376391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98557257864401882099168521 73917943398301411574376391)
    ·
      refine ⟨110876915097452117361564587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73917943398301411574376391 110876915097452117361564587)
      ·
        refine ⟨166315372646178176042346881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110876915097452117361564587 166315372646178176042346881)
        ·
          refine ⟨124736529484633632031760161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166315372646178176042346881 124736529484633632031760161)
          ·
            refine ⟨93552397113475224023820121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124736529484633632031760161 93552397113475224023820121)
            ·
              refine ⟨70164297835106418017865091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93552397113475224023820121 70164297835106418017865091)
              ·
                refine ⟨105246446752659627026797637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70164297835106418017865091 105246446752659627026797637)
                ·
                  refine ⟨19733708766123680067524557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105246446752659627026797637 19733708766123680067524557)
                  ·
                    refine ⟨7400140787296380025321709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19733708766123680067524557 7400140787296380025321709)
                    ·
                      refine ⟨2775052795236142509495641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7400140787296380025321709 2775052795236142509495641)
                      ·
                        rfl

theorem cell23_5404396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_5404396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404396 prefixEnd_5404396 := by exact prefixLift 5404396
  have htrace : WordTrace (prefixWord ++ tailWord_5404396) baseStart_5404396 baseEnd_5404396 := by
    simpa [prefixWord, tailWord_5404396, baseEnd_5404396] using wordTrace_append hprefix tailTrace_5404396
  have hstable : (prefixWord ++ tailWord_5404396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404396).length < 2 ^ (prefixWord ++ tailWord_5404396).sum := by decide
  have hdescent : baseEnd_5404396 < baseStart_5404396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404414 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_5404414 : Nat := 118140960795 + 5404414 * 2 ^ 59
def prefixEnd_5404414 : Nat := 4983230072969 + 3 ^ 40 * 5404414 * 2
def baseEnd_5404414 : Nat := 2775062037887923439070559

theorem tailTrace_5404414 : CollatzResearch.WordTrace tailWord_5404414 prefixEnd_5404414 2775062037887923439070559 := by
  unfold tailWord_5404414
  simp only [CollatzResearch.WordTrace]
  refine ⟨24639396530342319159061537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131410114828492368848328197 24639396530342319159061537)
  ·
    refine ⟨18479547397756739369296153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24639396530342319159061537 18479547397756739369296153)
    ·
      refine ⟨13859660548317554526972115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18479547397756739369296153 13859660548317554526972115)
      ·
        refine ⟨20789490822476331790458173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859660548317554526972115 20789490822476331790458173)
        ·
          refine ⟨7796059058428624421421815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20789490822476331790458173 7796059058428624421421815)
          ·
            refine ⟨11694088587642936632132723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796059058428624421421815 11694088587642936632132723)
            ·
              refine ⟨17541132881464404948199085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694088587642936632132723 17541132881464404948199085)
              ·
                refine ⟨6577924830549151855574657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17541132881464404948199085 6577924830549151855574657)
                ·
                  refine ⟨4933443622911863891680993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6577924830549151855574657 4933443622911863891680993)
                  ·
                    refine ⟨3700082717183897918760745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4933443622911863891680993 3700082717183897918760745)
                    ·
                      refine ⟨2775062037887923439070559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700082717183897918760745 2775062037887923439070559)
                      ·
                        rfl

theorem cell23_5404414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_5404414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404414 prefixEnd_5404414 := by exact prefixLift 5404414
  have htrace : WordTrace (prefixWord ++ tailWord_5404414) baseStart_5404414 baseEnd_5404414 := by
    simpa [prefixWord, tailWord_5404414, baseEnd_5404414] using wordTrace_append hprefix tailTrace_5404414
  have hstable : (prefixWord ++ tailWord_5404414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404414).length < 2 ^ (prefixWord ++ tailWord_5404414).sum := by decide
  have hdescent : baseEnd_5404414 < baseStart_5404414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404453 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_5404453 : Nat := 118140960795 + 5404453 * 2 ^ 59
def prefixEnd_5404453 : Nat := 4983230072969 + 3 ^ 40 * 5404453 * 2
def baseEnd_5404453 : Nat := 2775082063633448786482879

theorem tailTrace_5404453 : CollatzResearch.WordTrace tailWord_5404453 prefixEnd_5404453 2775082063633448786482879 := by
  unfold tailWord_5404453
  simp only [CollatzResearch.WordTrace]
  refine ⟨197116594689597262933162013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131411063126398175288774675 197116594689597262933162013)
  ·
    refine ⟨73918723008598973599935755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197116594689597262933162013 73918723008598973599935755)
    ·
      refine ⟨110878084512898460399903633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73918723008598973599935755 110878084512898460399903633)
      ·
        refine ⟨83158563384673845299927725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110878084512898460399903633 83158563384673845299927725)
        ·
          refine ⟨31184461269252691987472897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83158563384673845299927725 31184461269252691987472897)
          ·
            refine ⟨23388345951939518990604673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31184461269252691987472897 23388345951939518990604673)
            ·
              refine ⟨17541259463954639242953505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23388345951939518990604673 17541259463954639242953505)
              ·
                refine ⟨13155944597965979432215129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17541259463954639242953505 13155944597965979432215129)
                ·
                  refine ⟨9866958448474484574161347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13155944597965979432215129 9866958448474484574161347)
                  ·
                    refine ⟨14800437672711726861242021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9866958448474484574161347 14800437672711726861242021)
                    ·
                      refine ⟨2775082063633448786482879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14800437672711726861242021 2775082063633448786482879)
                      ·
                        rfl

theorem cell23_5404453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_5404453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404453 prefixEnd_5404453 := by exact prefixLift 5404453
  have htrace : WordTrace (prefixWord ++ tailWord_5404453) baseStart_5404453 baseEnd_5404453 := by
    simpa [prefixWord, tailWord_5404453, baseEnd_5404453] using wordTrace_append hprefix tailTrace_5404453
  have hstable : (prefixWord ++ tailWord_5404453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404453).length < 2 ^ (prefixWord ++ tailWord_5404453).sum := by decide
  have hdescent : baseEnd_5404453 < baseStart_5404453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404497 : List Nat := [1, 2, 2, 1, 5, 2, 2, 3, 1, 4]
def baseStart_5404497 : Nat := 118140960795 + 5404497 * 2 ^ 59
def prefixEnd_5404497 : Nat := 4983230072969 + 3 ^ 40 * 5404497 * 2
def baseEnd_5404497 : Nat := 925034885594082204777559

theorem tailTrace_5404497 : CollatzResearch.WordTrace tailWord_5404497 prefixEnd_5404497 925034885594082204777559 := by
  unfold tailWord_5404497
  simp only [CollatzResearch.WordTrace]
  refine ⟨197118199501437858447763745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131412133000958572298509163 197118199501437858447763745)
  ·
    refine ⟨147838649626078393835822809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197118199501437858447763745 147838649626078393835822809)
    ·
      refine ⟨110878987219558795376867107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147838649626078393835822809 110878987219558795376867107)
      ·
        refine ⟨166318480829338193065300661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110878987219558795376867107 166318480829338193065300661)
        ·
          refine ⟨15592357577750455599871937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166318480829338193065300661 15592357577750455599871937)
          ·
            refine ⟨11694268183312841699903953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15592357577750455599871937 11694268183312841699903953)
            ·
              refine ⟨8770701137484631274927965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694268183312841699903953 8770701137484631274927965)
              ·
                refine ⟨3289012926556736728097987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8770701137484631274927965 3289012926556736728097987)
                ·
                  refine ⟨4933519389835105092146981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289012926556736728097987 4933519389835105092146981)
                  ·
                    refine ⟨925034885594082204777559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933519389835105092146981 925034885594082204777559)
                    ·
                      rfl

theorem cell23_5404497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_5404497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404497 prefixEnd_5404497 := by exact prefixLift 5404497
  have htrace : WordTrace (prefixWord ++ tailWord_5404497) baseStart_5404497 baseEnd_5404497 := by
    simpa [prefixWord, tailWord_5404497, baseEnd_5404497] using wordTrace_append hprefix tailTrace_5404497
  have hstable : (prefixWord ++ tailWord_5404497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404497).length < 2 ^ (prefixWord ++ tailWord_5404497).sum := by decide
  have hdescent : baseEnd_5404497 < baseStart_5404497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404543 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 8, 2]
def baseStart_5404543 : Nat := 118140960795 + 5404543 * 2 ^ 59
def prefixEnd_5404543 : Nat := 4983230072969 + 3 ^ 40 * 5404543 * 2
def baseEnd_5404543 : Nat := 2775128276892353434357465

theorem tailTrace_5404543 : CollatzResearch.WordTrace tailWord_5404543 prefixEnd_5404543 2775128276892353434357465 := by
  unfold tailWord_5404543
  simp only [CollatzResearch.WordTrace]
  refine ⟨197119877259271208303938283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131413251506180805535958855 197119877259271208303938283)
  ·
    refine ⟨295679815888906812455907425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197119877259271208303938283 295679815888906812455907425)
    ·
      refine ⟨221759861916680109341930569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295679815888906812455907425 221759861916680109341930569)
      ·
        refine ⟨166319896437510082006447927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221759861916680109341930569 166319896437510082006447927)
        ·
          refine ⟨249479844656265123009671891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166319896437510082006447927 249479844656265123009671891)
          ·
            refine ⟨374219766984397684514507837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249479844656265123009671891 374219766984397684514507837)
            ·
              refine ⟨140332412619149131692940439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374219766984397684514507837 140332412619149131692940439)
              ·
                refine ⟨210498618928723697539410659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140332412619149131692940439 210498618928723697539410659)
                ·
                  refine ⟨315747928393085546309115989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210498618928723697539410659 315747928393085546309115989)
                  ·
                    refine ⟨3700171035856471245809953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 315747928393085546309115989 3700171035856471245809953)
                    ·
                      refine ⟨2775128276892353434357465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700171035856471245809953 2775128276892353434357465)
                      ·
                        rfl

theorem cell23_5404543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_5404543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404543 prefixEnd_5404543 := by exact prefixLift 5404543
  have htrace : WordTrace (prefixWord ++ tailWord_5404543) baseStart_5404543 baseEnd_5404543 := by
    simpa [prefixWord, tailWord_5404543, baseEnd_5404543] using wordTrace_append hprefix tailTrace_5404543
  have hstable : (prefixWord ++ tailWord_5404543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404543).length < 2 ^ (prefixWord ++ tailWord_5404543).sum := by decide
  have hdescent : baseEnd_5404543 < baseStart_5404543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404553 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_5404553 : Nat := 118140960795 + 5404553 * 2 ^ 59
def prefixEnd_5404553 : Nat := 4983230072969 + 3 ^ 40 * 5404553 * 2
def baseEnd_5404553 : Nat := 925044470566299465077473

theorem tailTrace_5404553 : CollatzResearch.WordTrace tailWord_5404553 prefixEnd_5404553 925044470566299465077473 := by
  unfold tailWord_5404553
  simp only [CollatzResearch.WordTrace]
  refine ⟨197120241989234980011802313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131413494659489986674534875 197120241989234980011802313)
  ·
    refine ⟨147840181491926235008851735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197120241989234980011802313 147840181491926235008851735)
    ·
      refine ⟨221760272237889352513277603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147840181491926235008851735 221760272237889352513277603)
      ·
        refine ⟨332640408356834028769916405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221760272237889352513277603 332640408356834028769916405)
        ·
          refine ⟨31185038283453190197179663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 332640408356834028769916405 31185038283453190197179663)
          ·
            refine ⟨46777557425179785295769495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31185038283453190197179663 46777557425179785295769495)
            ·
              refine ⟨70166336137769677943654243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46777557425179785295769495 70166336137769677943654243)
              ·
                refine ⟨105249504206654516915481365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70166336137769677943654243 105249504206654516915481365)
                ·
                  refine ⟨4933570509686930480413189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105249504206654516915481365 4933570509686930480413189)
                  ·
                    refine ⟨925044470566299465077473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933570509686930480413189 925044470566299465077473)
                    ·
                      rfl

theorem cell23_5404553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_5404553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404553 prefixEnd_5404553 := by exact prefixLift 5404553
  have htrace : WordTrace (prefixWord ++ tailWord_5404553) baseStart_5404553 baseEnd_5404553 := by
    simpa [prefixWord, tailWord_5404553, baseEnd_5404553] using wordTrace_append hprefix tailTrace_5404553
  have hstable : (prefixWord ++ tailWord_5404553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404553).length < 2 ^ (prefixWord ++ tailWord_5404553).sum := by decide
  have hdescent : baseEnd_5404553 < baseStart_5404553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404560 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2]
def baseStart_5404560 : Nat := 118140960795 + 5404560 * 2 ^ 59
def prefixEnd_5404560 : Nat := 4983230072969 + 3 ^ 40 * 5404560 * 2
def baseEnd_5404560 : Nat := 2775137006063479867844887

theorem tailTrace_5404560 : CollatzResearch.WordTrace tailWord_5404560 prefixEnd_5404560 2775137006063479867844887 := by
  unfold tailWord_5404560
  simp only [CollatzResearch.WordTrace]
  refine ⟨98560248650104810103653567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131413664866806413471538089 98560248650104810103653567)
  ·
    refine ⟨147840372975157215155480351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98560248650104810103653567 147840372975157215155480351)
    ·
      refine ⟨221760559462735822733220527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147840372975157215155480351 221760559462735822733220527)
      ·
        refine ⟨332640839194103734099830791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221760559462735822733220527 332640839194103734099830791)
        ·
          refine ⟨498961258791155601149746187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332640839194103734099830791 498961258791155601149746187)
          ·
            refine ⟨748441888186733401724619281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498961258791155601149746187 748441888186733401724619281)
            ·
              refine ⟨561331416140050051293464461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748441888186733401724619281 561331416140050051293464461)
              ·
                refine ⟨210499281052518769235049173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561331416140050051293464461 210499281052518769235049173)
                ·
                  refine ⟨4933576899668408653946465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 210499281052518769235049173 4933576899668408653946465)
                  ·
                    refine ⟨3700182674751306490459849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4933576899668408653946465 3700182674751306490459849)
                    ·
                      refine ⟨2775137006063479867844887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700182674751306490459849 2775137006063479867844887)
                      ·
                        rfl

theorem cell23_5404560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 2, 2].length) (baseStart_5404560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404560 prefixEnd_5404560 := by exact prefixLift 5404560
  have htrace : WordTrace (prefixWord ++ tailWord_5404560) baseStart_5404560 baseEnd_5404560 := by
    simpa [prefixWord, tailWord_5404560, baseEnd_5404560] using wordTrace_append hprefix tailTrace_5404560
  have hstable : (prefixWord ++ tailWord_5404560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404560).length < 2 ^ (prefixWord ++ tailWord_5404560).sum := by decide
  have hdescent : baseEnd_5404560 < baseStart_5404560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404570 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_5404570 : Nat := 118140960795 + 5404570 * 2 ^ 59
def prefixEnd_5404570 : Nat := 4983230072969 + 3 ^ 40 * 5404570 * 2
def baseEnd_5404570 : Nat := 925047380290008276239947

theorem tailTrace_5404570 : CollatzResearch.WordTrace tailWord_5404570 prefixEnd_5404570 925047380290008276239947 := by
  unfold tailWord_5404570
  simp only [CollatzResearch.WordTrace]
  refine ⟨49280215507543347978792791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131413908020115594610114109 49280215507543347978792791)
  ·
    refine ⟨73920323261315021968189187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49280215507543347978792791 73920323261315021968189187)
    ·
      refine ⟨110880484891972532952283781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73920323261315021968189187 110880484891972532952283781)
      ·
        refine ⟨20790090917244849928553209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110880484891972532952283781 20790090917244849928553209)
        ·
          refine ⟨15592568187933637446414907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20790090917244849928553209 15592568187933637446414907)
          ·
            refine ⟨23388852281900456169622361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15592568187933637446414907 23388852281900456169622361)
            ·
              refine ⟨17541639211425342127216771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23388852281900456169622361 17541639211425342127216771)
              ·
                refine ⟨26312458817138013190825157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17541639211425342127216771 26312458817138013190825157)
                ·
                  refine ⟨4933586028213377473279717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26312458817138013190825157 4933586028213377473279717)
                  ·
                    refine ⟨925047380290008276239947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933586028213377473279717 925047380290008276239947)
                    ·
                      rfl

theorem cell23_5404570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_5404570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404570 prefixEnd_5404570 := by exact prefixLift 5404570
  have htrace : WordTrace (prefixWord ++ tailWord_5404570) baseStart_5404570 baseEnd_5404570 := by
    simpa [prefixWord, tailWord_5404570, baseEnd_5404570] using wordTrace_append hprefix tailTrace_5404570
  have hstable : (prefixWord ++ tailWord_5404570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404570).length < 2 ^ (prefixWord ++ tailWord_5404570).sum := by decide
  have hdescent : baseEnd_5404570 < baseStart_5404570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404573 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5404573 : Nat := 118140960795 + 5404573 * 2 ^ 59
def prefixEnd_5404573 : Nat := 4983230072969 + 3 ^ 40 * 5404573 * 2
def baseEnd_5404573 : Nat := 2775143681311988316982327

theorem tailTrace_5404573 : CollatzResearch.WordTrace tailWord_5404573 prefixEnd_5404573 2775143681311988316982327 := by
  unfold tailWord_5404573
  simp only [CollatzResearch.WordTrace]
  refine ⟨197120971449162523427530373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131413980966108348951686915 197120971449162523427530373)
  ·
    refine ⟨36960182146717973142661945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197120971449162523427530373 36960182146717973142661945)
    ·
      refine ⟨27720136610038479856996459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36960182146717973142661945 27720136610038479856996459)
      ·
        refine ⟨41580204915057719785494689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27720136610038479856996459 41580204915057719785494689)
        ·
          refine ⟨31185153686293289839121017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41580204915057719785494689 31185153686293289839121017)
          ·
            refine ⟨23388865264719967379340763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31185153686293289839121017 23388865264719967379340763)
            ·
              refine ⟨35083297897079951069011145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23388865264719967379340763 35083297897079951069011145)
              ·
                refine ⟨26312473422809963301758359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35083297897079951069011145 26312473422809963301758359)
                ·
                  refine ⟨39468710134214944952637539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26312473422809963301758359 39468710134214944952637539)
                  ·
                    refine ⟨59203065201322417428956309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39468710134214944952637539 59203065201322417428956309)
                    ·
                      refine ⟨2775143681311988316982327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59203065201322417428956309 2775143681311988316982327)
                      ·
                        rfl

theorem cell23_5404573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5404573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404573 prefixEnd_5404573 := by exact prefixLift 5404573
  have htrace : WordTrace (prefixWord ++ tailWord_5404573) baseStart_5404573 baseEnd_5404573 := by
    simpa [prefixWord, tailWord_5404573, baseEnd_5404573] using wordTrace_append hprefix tailTrace_5404573
  have hstable : (prefixWord ++ tailWord_5404573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404573).length < 2 ^ (prefixWord ++ tailWord_5404573).sum := by decide
  have hdescent : baseEnd_5404573 < baseStart_5404573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404583 : List Nat := [1, 1, 6, 1, 2, 1, 1, 10]
def baseStart_5404583 : Nat := 118140960795 + 5404583 * 2 ^ 59
def prefixEnd_5404583 : Nat := 4983230072969 + 3 ^ 40 * 5404583 * 2
def baseEnd_5404583 : Nat := 102783289485871602883603

theorem tailTrace_5404583 : CollatzResearch.WordTrace tailWord_5404583 prefixEnd_5404583 102783289485871602883603 := by
  unfold tailWord_5404583
  simp only [CollatzResearch.WordTrace]
  refine ⟨197121336179126295135394403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131414224119417530090262935 197121336179126295135394403)
  ·
    refine ⟨295682004268689442703091605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197121336179126295135394403 295682004268689442703091605)
    ·
      refine ⟨13860093950094817626707419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 295682004268689442703091605 13860093950094817626707419)
      ·
        refine ⟨20790140925142226440061129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860093950094817626707419 20790140925142226440061129)
        ·
          refine ⟨15592605693856669830045847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20790140925142226440061129 15592605693856669830045847)
          ·
            refine ⟨23388908540785004745068771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15592605693856669830045847 23388908540785004745068771)
            ·
              refine ⟨35083362811177507117603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23388908540785004745068771 35083362811177507117603157)
              ·
                refine ⟨102783289485871602883603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35083362811177507117603157 102783289485871602883603)
                ·
                  rfl

theorem cell23_5404583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 10].length) (baseStart_5404583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404583 prefixEnd_5404583 := by exact prefixLift 5404583
  have htrace : WordTrace (prefixWord ++ tailWord_5404583) baseStart_5404583 baseEnd_5404583 := by
    simpa [prefixWord, tailWord_5404583, baseEnd_5404583] using wordTrace_append hprefix tailTrace_5404583
  have hstable : (prefixWord ++ tailWord_5404583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404583).length < 2 ^ (prefixWord ++ tailWord_5404583).sum := by decide
  have hdescent : baseEnd_5404583 < baseStart_5404583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404597 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_5404597 : Nat := 118140960795 + 5404597 * 2 ^ 59
def prefixEnd_5404597 : Nat := 4983230072969 + 3 ^ 40 * 5404597 * 2
def baseEnd_5404597 : Nat := 2775156004847696223082217

theorem tailTrace_5404597 : CollatzResearch.WordTrace tailWord_5404597 prefixEnd_5404597 2775156004847696223082217 := by
  unfold tailWord_5404597
  simp only [CollatzResearch.WordTrace]
  refine ⟨197121846801075575526404045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131414564534050383684269363 197121846801075575526404045)
  ·
    refine ⟨73920692550403340822401517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197121846801075575526404045 73920692550403340822401517)
    ·
      refine ⟨27720259706401252808400569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73920692550403340822401517 27720259706401252808400569)
      ·
        refine ⟨20790194779800939606300427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27720259706401252808400569 20790194779800939606300427)
        ·
          refine ⟨31185292169701409409450641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20790194779800939606300427 31185292169701409409450641)
          ·
            refine ⟨23388969127276057057087981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31185292169701409409450641 23388969127276057057087981)
            ·
              refine ⟨8770863422728521396407993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23388969127276057057087981 8770863422728521396407993)
              ·
                refine ⟨6578147567046391047305995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8770863422728521396407993 6578147567046391047305995)
                ·
                  refine ⟨9867221350569586570958993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6578147567046391047305995 9867221350569586570958993)
                  ·
                    refine ⟨7400416012927189928219245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9867221350569586570958993 7400416012927189928219245)
                    ·
                      refine ⟨2775156004847696223082217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7400416012927189928219245 2775156004847696223082217)
                      ·
                        rfl

theorem cell23_5404597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_5404597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404597 prefixEnd_5404597 := by exact prefixLift 5404597
  have htrace : WordTrace (prefixWord ++ tailWord_5404597) baseStart_5404597 baseEnd_5404597 := by
    simpa [prefixWord, tailWord_5404597, baseEnd_5404597] using wordTrace_append hprefix tailTrace_5404597
  have hstable : (prefixWord ++ tailWord_5404597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404597).length < 2 ^ (prefixWord ++ tailWord_5404597).sum := by decide
  have hdescent : baseEnd_5404597 < baseStart_5404597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404643 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 8]
def baseStart_5404643 : Nat := 118140960795 + 5404643 * 2 ^ 59
def prefixEnd_5404643 : Nat := 4983230072969 + 3 ^ 40 * 5404643 * 2
def baseEnd_5404643 : Nat := 925059874985934347702335

theorem tailTrace_5404643 : CollatzResearch.WordTrace tailWord_5404643 prefixEnd_5404643 925059874985934347702335 := by
  unfold tailWord_5404643
  simp only [CollatzResearch.WordTrace]
  refine ⟨197123524558908925382578583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131415683039272616921719055 197123524558908925382578583)
  ·
    refine ⟨295685286838363388073867875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197123524558908925382578583 295685286838363388073867875)
    ·
      refine ⟨443527930257545082110801813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295685286838363388073867875 443527930257545082110801813)
      ·
        refine ⟨20790371730822425723943835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 443527930257545082110801813 20790371730822425723943835)
        ·
          refine ⟨31185557596233638585915753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20790371730822425723943835 31185557596233638585915753)
          ·
            refine ⟨23389168197175228939436815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31185557596233638585915753 23389168197175228939436815)
            ·
              refine ⟨35083752295762843409155223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23389168197175228939436815 35083752295762843409155223)
              ·
                refine ⟨52625628443644265113732835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35083752295762843409155223 52625628443644265113732835)
                ·
                  refine ⟨78938442665466397670599253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52625628443644265113732835 78938442665466397670599253)
                  ·
                    refine ⟨925059874985934347702335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78938442665466397670599253 925059874985934347702335)
                    ·
                      rfl

theorem cell23_5404643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_5404643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404643 prefixEnd_5404643 := by exact prefixLift 5404643
  have htrace : WordTrace (prefixWord ++ tailWord_5404643) baseStart_5404643 baseEnd_5404643 := by
    simpa [prefixWord, tailWord_5404643, baseEnd_5404643] using wordTrace_append hprefix tailTrace_5404643
  have hstable : (prefixWord ++ tailWord_5404643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404643).length < 2 ^ (prefixWord ++ tailWord_5404643).sum := by decide
  have hdescent : baseEnd_5404643 < baseStart_5404643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404673 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 9]
def baseStart_5404673 : Nat := 118140960795 + 5404673 * 2 ^ 59
def prefixEnd_5404673 : Nat := 4983230072969 + 3 ^ 40 * 5404673 * 2
def baseEnd_5404673 : Nat := 308355003264159769525763

theorem tailTrace_5404673 : CollatzResearch.WordTrace tailWord_5404673 prefixEnd_5404673 308355003264159769525763 := by
  unfold tailWord_5404673
  simp only [CollatzResearch.WordTrace]
  refine ⟨197124618748800240506170673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131416412499200160337447115 197124618748800240506170673)
  ·
    refine ⟨147843464061600180379628005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197124618748800240506170673 147843464061600180379628005)
    ·
      refine ⟨27720649511550033821180251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147843464061600180379628005 27720649511550033821180251)
      ·
        refine ⟨41580974267325050731770377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27720649511550033821180251 41580974267325050731770377)
        ·
          refine ⟨31185730700493788048827783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41580974267325050731770377 31185730700493788048827783)
          ·
            refine ⟨46778596050740682073241675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31185730700493788048827783 46778596050740682073241675)
            ·
              refine ⟨70167894076111023109862513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46778596050740682073241675 70167894076111023109862513)
              ·
                refine ⟨52625920557083267332396885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70167894076111023109862513 52625920557083267332396885)
                ·
                  refine ⟨308355003264159769525763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52625920557083267332396885 308355003264159769525763)
                  ·
                    rfl

theorem cell23_5404673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_5404673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404673 prefixEnd_5404673 := by exact prefixLift 5404673
  have htrace : WordTrace (prefixWord ++ tailWord_5404673) baseStart_5404673 baseEnd_5404673 := by
    simpa [prefixWord, tailWord_5404673, baseEnd_5404673] using wordTrace_append hprefix tailTrace_5404673
  have hstable : (prefixWord ++ tailWord_5404673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404673).length < 2 ^ (prefixWord ++ tailWord_5404673).sum := by decide
  have hdescent : baseEnd_5404673 < baseStart_5404673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404703 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 3, 7]
def baseStart_5404703 : Nat := 118140960795 + 5404703 * 2 ^ 59
def prefixEnd_5404703 : Nat := 4983230072969 + 3 ^ 40 * 5404703 * 2
def baseEnd_5404703 : Nat := 925070144599024269452243

theorem tailTrace_5404703 : CollatzResearch.WordTrace tailWord_5404703 prefixEnd_5404703 925070144599024269452243 := by
  unfold tailWord_5404703
  simp only [CollatzResearch.WordTrace]
  refine ⟨197125712938691555629762763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131417141959127703753175175 197125712938691555629762763)
  ·
    refine ⟨295688569408037333444644145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197125712938691555629762763 295688569408037333444644145)
    ·
      refine ⟨221766427056028000083483109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295688569408037333444644145 221766427056028000083483109)
      ·
        refine ⟨41581205073005250015653083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221766427056028000083483109 41581205073005250015653083)
        ·
          refine ⟨62371807609507875023479625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41581205073005250015653083 62371807609507875023479625)
          ·
            refine ⟨46778855707130906267609719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62371807609507875023479625 46778855707130906267609719)
            ·
              refine ⟨70168283560696359401414579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46778855707130906267609719 70168283560696359401414579)
              ·
                refine ⟨105252425341044539102121869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70168283560696359401414579 105252425341044539102121869)
                ·
                  refine ⟨39469659502891702163295701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105252425341044539102121869 39469659502891702163295701)
                  ·
                    refine ⟨925070144599024269452243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39469659502891702163295701 925070144599024269452243)
                    ·
                      rfl

theorem cell23_5404703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_5404703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404703 prefixEnd_5404703 := by exact prefixLift 5404703
  have htrace : WordTrace (prefixWord ++ tailWord_5404703) baseStart_5404703 baseEnd_5404703 := by
    simpa [prefixWord, tailWord_5404703, baseEnd_5404703] using wordTrace_append hprefix tailTrace_5404703
  have hstable : (prefixWord ++ tailWord_5404703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404703).length < 2 ^ (prefixWord ++ tailWord_5404703).sum := by decide
  have hdescent : baseEnd_5404703 < baseStart_5404703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404737 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5404737 : Nat := 118140960795 + 5404737 * 2 ^ 59
def prefixEnd_5404737 : Nat := 4983230072969 + 3 ^ 40 * 5404737 * 2
def baseEnd_5404737 : Nat := 925075964046441891777191

theorem tailTrace_5404737 : CollatzResearch.WordTrace tailWord_5404737 prefixEnd_5404737 925075964046441891777191 := by
  unfold tailWord_5404737
  simp only [CollatzResearch.WordTrace]
  refine ⟨197126953020568379436500465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131417968680378919624333643 197126953020568379436500465)
  ·
    refine ⟨147845214765426284577375349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197126953020568379436500465 147845214765426284577375349)
    ·
      refine ⟨13860488884258714179128939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147845214765426284577375349 13860488884258714179128939)
      ·
        refine ⟨20790733326388071268693409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860488884258714179128939 20790733326388071268693409)
        ·
          refine ⟨15593049994791053451520057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20790733326388071268693409 15593049994791053451520057)
          ·
            refine ⟨11694787496093290088640043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15593049994791053451520057 11694787496093290088640043)
            ·
              refine ⟨17542181244139935132960065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694787496093290088640043 17542181244139935132960065)
              ·
                refine ⟨13156635933104951349720049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17542181244139935132960065 13156635933104951349720049)
                ·
                  refine ⟨9867476949828713512290037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13156635933104951349720049 9867476949828713512290037)
                  ·
                    refine ⟨925075964046441891777191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9867476949828713512290037 925075964046441891777191)
                    ·
                      rfl

theorem cell23_5404737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5404737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404737 prefixEnd_5404737 := by exact prefixLift 5404737
  have htrace : WordTrace (prefixWord ++ tailWord_5404737) baseStart_5404737 baseEnd_5404737 := by
    simpa [prefixWord, tailWord_5404737, baseEnd_5404737] using wordTrace_append hprefix tailTrace_5404737
  have hstable : (prefixWord ++ tailWord_5404737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404737).length < 2 ^ (prefixWord ++ tailWord_5404737).sum := by decide
  have hdescent : baseEnd_5404737 < baseStart_5404737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404777 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_5404777 : Nat := 118140960795 + 5404777 * 2 ^ 59
def prefixEnd_5404777 : Nat := 4983230072969 + 3 ^ 40 * 5404777 * 2
def baseEnd_5404777 : Nat := 2775248431365505518831389

theorem tailTrace_5404777 : CollatzResearch.WordTrace tailWord_5404777 prefixEnd_5404777 2775248431365505518831389 := by
  unfold tailWord_5404777
  simp only [CollatzResearch.WordTrace]
  refine ⟨197128411940423466267956585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131418941293615644178637723 197128411940423466267956585)
  ·
    refine ⟨147846308955317599700967439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197128411940423466267956585 147846308955317599700967439)
    ·
      refine ⟨221769463432976399551451159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147846308955317599700967439 221769463432976399551451159)
      ·
        refine ⟨332654195149464599327176739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221769463432976399551451159 332654195149464599327176739)
        ·
          refine ⟨498981292724196898990765109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332654195149464599327176739 498981292724196898990765109)
          ·
            refine ⟨46779496192893459280384229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 498981292724196898990765109 46779496192893459280384229)
            ·
              refine ⟨8771155536167523615072043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46779496192893459280384229 8771155536167523615072043)
              ·
                refine ⟨13156733304251285422608065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771155536167523615072043 13156733304251285422608065)
                ·
                  refine ⟨9867549978188464066956049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13156733304251285422608065 9867549978188464066956049)
                  ·
                    refine ⟨7400662483641348050217037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9867549978188464066956049 7400662483641348050217037)
                    ·
                      refine ⟨2775248431365505518831389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7400662483641348050217037 2775248431365505518831389)
                      ·
                        rfl

theorem cell23_5404777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_5404777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404777 prefixEnd_5404777 := by exact prefixLift 5404777
  have htrace : WordTrace (prefixWord ++ tailWord_5404777) baseStart_5404777 baseEnd_5404777 := by
    simpa [prefixWord, tailWord_5404777, baseEnd_5404777] using wordTrace_append hprefix tailTrace_5404777
  have hstable : (prefixWord ++ tailWord_5404777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404777).length < 2 ^ (prefixWord ++ tailWord_5404777).sum := by decide
  have hdescent : baseEnd_5404777 < baseStart_5404777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404797 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 6]
def baseStart_5404797 : Nat := 118140960795 + 5404797 * 2 ^ 59
def prefixEnd_5404797 : Nat := 4983230072969 + 3 ^ 40 * 5404797 * 2
def baseEnd_5404797 : Nat := 308362077886510604509033

theorem tailTrace_5404797 : CollatzResearch.WordTrace tailWord_5404797 prefixEnd_5404797 308362077886510604509033 := by
  unfold tailWord_5404797
  simp only [CollatzResearch.WordTrace]
  refine ⟨197129141400351009683684645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131419427600234006455789763 197129141400351009683684645)
  ·
    refine ⟨36961714012565814315690871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197129141400351009683684645 36961714012565814315690871)
    ·
      refine ⟨55442571018848721473536307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36961714012565814315690871 55442571018848721473536307)
      ·
        refine ⟨83163856528273082210304461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55442571018848721473536307 83163856528273082210304461)
        ·
          refine ⟨31186446198102405828864173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83163856528273082210304461 31186446198102405828864173)
          ·
            refine ⟨11694917324288402185824065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31186446198102405828864173 11694917324288402185824065)
            ·
              refine ⟨8771187993216301639368049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694917324288402185824065 8771187993216301639368049)
              ·
                refine ⟨6578390994912226229526037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8771187993216301639368049 6578390994912226229526037)
                ·
                  refine ⟨308362077886510604509033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6578390994912226229526037 308362077886510604509033)
                  ·
                    rfl

theorem cell23_5404797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_5404797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404797 prefixEnd_5404797 := by exact prefixLift 5404797
  have htrace : WordTrace (prefixWord ++ tailWord_5404797) baseStart_5404797 baseEnd_5404797 := by
    simpa [prefixWord, tailWord_5404797, baseEnd_5404797] using wordTrace_append hprefix tailTrace_5404797
  have hstable : (prefixWord ++ tailWord_5404797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404797).length < 2 ^ (prefixWord ++ tailWord_5404797).sum := by decide
  have hdescent : baseEnd_5404797 < baseStart_5404797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404801 : List Nat := [1, 2, 4, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5404801 : Nat := 118140960795 + 5404801 * 2 ^ 59
def prefixEnd_5404801 : Nat := 4983230072969 + 3 ^ 40 * 5404801 * 2
def baseEnd_5404801 : Nat := 925086918300404474977093

theorem tailTrace_5404801 : CollatzResearch.WordTrace tailWord_5404801 prefixEnd_5404801 925086918300404474977093 := by
  unfold tailWord_5404801
  simp only [CollatzResearch.WordTrace]
  refine ⟨197129287292336518366830257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131419524861557678911220171 197129287292336518366830257)
  ·
    refine ⟨147846965469252388775122693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197129287292336518366830257 147846965469252388775122693)
    ·
      refine ⟨27721306025484822895335505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147846965469252388775122693 27721306025484822895335505)
      ·
        refine ⟨20790979519113617171501629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27721306025484822895335505 20790979519113617171501629)
        ·
          refine ⟨7796617319667606439313111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20790979519113617171501629 7796617319667606439313111)
          ·
            refine ⟨11694925979501409658969667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796617319667606439313111 11694925979501409658969667)
            ·
              refine ⟨17542388969252114488454501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694925979501409658969667 17542388969252114488454501)
              ·
                refine ⟨3289197931734771466585219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17542388969252114488454501 3289197931734771466585219)
                ·
                  refine ⟨4933796897602157199877829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289197931734771466585219 4933796897602157199877829)
                  ·
                    refine ⟨925086918300404474977093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933796897602157199877829 925086918300404474977093)
                    ·
                      rfl

theorem cell23_5404801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5404801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404801 prefixEnd_5404801 := by exact prefixLift 5404801
  have htrace : WordTrace (prefixWord ++ tailWord_5404801) baseStart_5404801 baseEnd_5404801 := by
    simpa [prefixWord, tailWord_5404801, baseEnd_5404801] using wordTrace_append hprefix tailTrace_5404801
  have hstable : (prefixWord ++ tailWord_5404801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404801).length < 2 ^ (prefixWord ++ tailWord_5404801).sum := by decide
  have hdescent : baseEnd_5404801 < baseStart_5404801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404822 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5404822 : Nat := 118140960795 + 5404822 * 2 ^ 59
def prefixEnd_5404822 : Nat := 4983230072969 + 3 ^ 40 * 5404822 * 2
def baseEnd_5404822 : Nat := 925090512664985947589561

theorem tailTrace_5404822 : CollatzResearch.WordTrace tailWord_5404822 prefixEnd_5404822 925090512664985947589561 := by
  unfold tailWord_5404822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320628326578777434584045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131420035483506959302229813 12320628326578777434584045)
  ·
    refine ⟨4620235622467041537969017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12320628326578777434584045 4620235622467041537969017)
    ·
      refine ⟨3465176716850281153476763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4620235622467041537969017 3465176716850281153476763)
      ·
        refine ⟨5197765075275421730215145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465176716850281153476763 5197765075275421730215145)
        ·
          refine ⟨3898323806456566297661359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197765075275421730215145 3898323806456566297661359)
          ·
            refine ⟨5847485709684849446492039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898323806456566297661359 5847485709684849446492039)
            ·
              refine ⟨8771228564527274169738059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847485709684849446492039 8771228564527274169738059)
              ·
                refine ⟨13156842846790911254607089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771228564527274169738059 13156842846790911254607089)
                ·
                  refine ⟨9867632135093183440955317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13156842846790911254607089 9867632135093183440955317)
                  ·
                    refine ⟨925090512664985947589561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9867632135093183440955317 925090512664985947589561)
                    ·
                      rfl

theorem cell23_5404822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5404822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404822 prefixEnd_5404822 := by exact prefixLift 5404822
  have htrace : WordTrace (prefixWord ++ tailWord_5404822) baseStart_5404822 baseEnd_5404822 := by
    simpa [prefixWord, tailWord_5404822, baseEnd_5404822] using wordTrace_append hprefix tailTrace_5404822
  have hstable : (prefixWord ++ tailWord_5404822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404822).length < 2 ^ (prefixWord ++ tailWord_5404822).sum := by decide
  have hdescent : baseEnd_5404822 < baseStart_5404822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404857 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_5404857 : Nat := 118140960795 + 5404857 * 2 ^ 59
def prefixEnd_5404857 : Nat := 4983230072969 + 3 ^ 40 * 5404857 * 2
def baseEnd_5404857 : Nat := 925096503272621735277007

theorem tailTrace_5404857 : CollatzResearch.WordTrace tailWord_5404857 prefixEnd_5404857 925096503272621735277007 := by
  unfold tailWord_5404857
  simp only [CollatzResearch.WordTrace]
  refine ⟨197131329780133639930868825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131420886520089093287245883 197131329780133639930868825)
  ·
    refine ⟨147848497335100229948151619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197131329780133639930868825 147848497335100229948151619)
    ·
      refine ⟨221772746002650344922227429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147848497335100229948151619 221772746002650344922227429)
      ·
        refine ⟨41582389875496939672917643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221772746002650344922227429 41582389875496939672917643)
        ·
          refine ⟨62373584813245409509376465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41582389875496939672917643 62373584813245409509376465)
          ·
            refine ⟨46780188609934057132032349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62373584813245409509376465 46780188609934057132032349)
            ·
              refine ⟨17542570728725271424512131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46780188609934057132032349 17542570728725271424512131)
              ·
                refine ⟨26313856093087907136768197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17542570728725271424512131 26313856093087907136768197)
                ·
                  refine ⟨4933848017453982588144037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26313856093087907136768197 4933848017453982588144037)
                  ·
                    refine ⟨925096503272621735277007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933848017453982588144037 925096503272621735277007)
                    ·
                      rfl

theorem cell23_5404857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_5404857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404857 prefixEnd_5404857 := by exact prefixLift 5404857
  have htrace : WordTrace (prefixWord ++ tailWord_5404857) baseStart_5404857 baseEnd_5404857 := by
    simpa [prefixWord, tailWord_5404857, baseEnd_5404857] using wordTrace_append hprefix tailTrace_5404857
  have hstable : (prefixWord ++ tailWord_5404857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404857).length < 2 ^ (prefixWord ++ tailWord_5404857).sum := by decide
  have hdescent : baseEnd_5404857 < baseStart_5404857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404892 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5404892 : Nat := 118140960795 + 5404892 * 2 ^ 59
def prefixEnd_5404892 : Nat := 4983230072969 + 3 ^ 40 * 5404892 * 2
def baseEnd_5404892 : Nat := 2775307481640772568893361

theorem tailTrace_5404892 : CollatzResearch.WordTrace tailWord_5404892 prefixEnd_5404892 2775307481640772568893361 := by
  unfold tailWord_5404892
  simp only [CollatzResearch.WordTrace]
  refine ⟨98566303167503420454196465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131421737556671227272261953 98566303167503420454196465)
  ·
    refine ⟨73924727375627565340647349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98566303167503420454196465 73924727375627565340647349)
    ·
      refine ⟨6930443191465084250685689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73924727375627565340647349 6930443191465084250685689)
      ·
        refine ⟨5197832393598813188014267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930443191465084250685689 5197832393598813188014267)
        ·
          refine ⟨7796748590398219782021401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197832393598813188014267 7796748590398219782021401)
          ·
            refine ⟨5847561442798664836516051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7796748590398219782021401 5847561442798664836516051)
            ·
              refine ⟨8771342164197997254774077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847561442798664836516051 8771342164197997254774077)
              ·
                refine ⟨3289253311574248970540279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8771342164197997254774077 3289253311574248970540279)
                ·
                  refine ⟨4933879967361373455810419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289253311574248970540279 4933879967361373455810419)
                  ·
                    refine ⟨7400819951042060183715629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4933879967361373455810419 7400819951042060183715629)
                    ·
                      refine ⟨2775307481640772568893361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7400819951042060183715629 2775307481640772568893361)
                      ·
                        rfl

theorem cell23_5404892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5404892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404892 prefixEnd_5404892 := by exact prefixLift 5404892
  have htrace : WordTrace (prefixWord ++ tailWord_5404892) baseStart_5404892 baseEnd_5404892 := by
    simpa [prefixWord, tailWord_5404892, baseEnd_5404892] using wordTrace_append hprefix tailTrace_5404892
  have hstable : (prefixWord ++ tailWord_5404892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404892).length < 2 ^ (prefixWord ++ tailWord_5404892).sum := by decide
  have hdescent : baseEnd_5404892 < baseStart_5404892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404897 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_5404897 : Nat := 118140960795 + 5404897 * 2 ^ 59
def prefixEnd_5404897 : Nat := 4983230072969 + 3 ^ 40 * 5404897 * 2
def baseEnd_5404897 : Nat := 2775310049044045049330837

theorem tailTrace_5404897 : CollatzResearch.WordTrace tailWord_5404897 prefixEnd_5404897 2775310049044045049330837 := by
  unfold tailWord_5404897
  simp only [CollatzResearch.WordTrace]
  refine ⟨197132788699988726762324945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131421859133325817841549963 197132788699988726762324945)
  ·
    refine ⟨147849591524991545071743709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197132788699988726762324945 147849591524991545071743709)
    ·
      refine ⟨55443596821871829401903891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147849591524991545071743709 55443596821871829401903891)
      ·
        refine ⟨83165395232807744102855837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55443596821871829401903891 83165395232807744102855837)
        ·
          refine ⟨31187023212302904038570939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83165395232807744102855837 31187023212302904038570939)
          ·
            refine ⟨46780534818454356057856409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31187023212302904038570939 46780534818454356057856409)
            ·
              refine ⟨35085401113840767043392307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46780534818454356057856409 35085401113840767043392307)
              ·
                refine ⟨52628101670761150565088461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35085401113840767043392307 52628101670761150565088461)
                ·
                  refine ⟨19735538126535431461908173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52628101670761150565088461 19735538126535431461908173)
                  ·
                    refine ⟨7400826797450786798215565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19735538126535431461908173 7400826797450786798215565)
                    ·
                      refine ⟨2775310049044045049330837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7400826797450786798215565 2775310049044045049330837)
                      ·
                        rfl

theorem cell23_5404897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_5404897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404897 prefixEnd_5404897 := by exact prefixLift 5404897
  have htrace : WordTrace (prefixWord ++ tailWord_5404897) baseStart_5404897 baseEnd_5404897 := by
    simpa [prefixWord, tailWord_5404897, baseEnd_5404897] using wordTrace_append hprefix tailTrace_5404897
  have hstable : (prefixWord ++ tailWord_5404897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404897).length < 2 ^ (prefixWord ++ tailWord_5404897).sum := by decide
  have hdescent : baseEnd_5404897 < baseStart_5404897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404900 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_5404900 : Nat := 118140960795 + 5404900 * 2 ^ 59
def prefixEnd_5404900 : Nat := 4983230072969 + 3 ^ 40 * 5404900 * 2
def baseEnd_5404900 : Nat := 925103863162002845864441

theorem tailTrace_5404900 : CollatzResearch.WordTrace tailWord_5404900 prefixEnd_5404900 925103863162002845864441 := by
  unfold tailWord_5404900
  simp only [CollatzResearch.WordTrace]
  refine ⟨98566449059488929137342077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131421932079318572183122769 98566449059488929137342077)
  ·
    refine ⟨36962418397308348426503279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98566449059488929137342077 36962418397308348426503279)
    ·
      refine ⟨55443627595962522639754919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36962418397308348426503279 55443627595962522639754919)
      ·
        refine ⟨83165441393943783959632379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55443627595962522639754919 83165441393943783959632379)
        ·
          refine ⟨124748162090915675939448569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83165441393943783959632379 124748162090915675939448569)
          ·
            refine ⟨93561121568186756954586427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124748162090915675939448569 93561121568186756954586427)
            ·
              refine ⟨140341682352280135431879641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93561121568186756954586427 140341682352280135431879641)
              ·
                refine ⟨105256261764210101573909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140341682352280135431879641 105256261764210101573909731)
                ·
                  refine ⟨157884392646315152360864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105256261764210101573909731 157884392646315152360864597)
                  ·
                    refine ⟨925103863162002845864441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157884392646315152360864597 925103863162002845864441)
                    ·
                      rfl

theorem cell23_5404900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_5404900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404900 prefixEnd_5404900 := by exact prefixLift 5404900
  have htrace : WordTrace (prefixWord ++ tailWord_5404900) baseStart_5404900 baseEnd_5404900 := by
    simpa [prefixWord, tailWord_5404900, baseEnd_5404900] using wordTrace_append hprefix tailTrace_5404900
  have hstable : (prefixWord ++ tailWord_5404900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404900).length < 2 ^ (prefixWord ++ tailWord_5404900).sum := by decide
  have hdescent : baseEnd_5404900 < baseStart_5404900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5404935 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5404935 : Nat := 118140960795 + 5404935 * 2 ^ 59
def prefixEnd_5404935 : Nat := 4983230072969 + 3 ^ 40 * 5404935 * 2
def baseEnd_5404935 : Nat := 2775329561308915900655663

theorem tailTrace_5404935 : CollatzResearch.WordTrace tailWord_5404935 prefixEnd_5404935 2775329561308915900655663 := by
  unfold tailWord_5404935
  simp only [CollatzResearch.WordTrace]
  refine ⟨197134174673851059252208259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131422783115900706168138839 197134174673851059252208259)
  ·
    refine ⟨295701262010776588878312389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197134174673851059252208259 295701262010776588878312389)
    ·
      refine ⟨55443986627020610414683573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295701262010776588878312389 55443986627020610414683573)
      ·
        refine ⟨5197873746283182226376585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55443986627020610414683573 5197873746283182226376585)
        ·
          refine ⟨3898405309712386669782439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197873746283182226376585 3898405309712386669782439)
          ·
            refine ⟨5847607964568580004673659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898405309712386669782439 5847607964568580004673659)
            ·
              refine ⟨8771411946852870007010489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847607964568580004673659 8771411946852870007010489)
              ·
                refine ⟨6578558960139652505257867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8771411946852870007010489 6578558960139652505257867)
                ·
                  refine ⟨9867838440209478757886801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6578558960139652505257867 9867838440209478757886801)
                  ·
                    refine ⟨7400878830157109068415101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9867838440209478757886801 7400878830157109068415101)
                    ·
                      refine ⟨2775329561308915900655663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7400878830157109068415101 2775329561308915900655663)
                      ·
                        rfl

theorem cell23_5404935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5404935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5404935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5404935 prefixEnd_5404935 := by exact prefixLift 5404935
  have htrace : WordTrace (prefixWord ++ tailWord_5404935) baseStart_5404935 baseEnd_5404935 := by
    simpa [prefixWord, tailWord_5404935, baseEnd_5404935] using wordTrace_append hprefix tailTrace_5404935
  have hstable : (prefixWord ++ tailWord_5404935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5404935).length < 2 ^ (prefixWord ++ tailWord_5404935).sum := by decide
  have hdescent : baseEnd_5404935 < baseStart_5404935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5404935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405007 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 2, 5]
def baseStart_5405007 : Nat := 118140960795 + 5405007 * 2 ^ 59
def prefixEnd_5405007 : Nat := 4983230072969 + 3 ^ 40 * 5405007 * 2
def baseEnd_5405007 : Nat := 925122177305346539651777

theorem tailTrace_5405007 : CollatzResearch.WordTrace tailWord_5405007 prefixEnd_5405007 925122177305346539651777 := by
  unfold tailWord_5405007
  simp only [CollatzResearch.WordTrace]
  refine ⟨197136800729590215548829275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131424533819726810365886183 197136800729590215548829275)
  ·
    refine ⟨295705201094385323323243913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197136800729590215548829275 295705201094385323323243913)
    ·
      refine ⟨221778900820788992492432935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295705201094385323323243913 221778900820788992492432935)
      ·
        refine ⟨332668351231183488738649403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221778900820788992492432935 332668351231183488738649403)
        ·
          refine ⟨499002526846775233107974105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332668351231183488738649403 499002526846775233107974105)
          ·
            refine ⟨374251895135081424830980579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499002526846775233107974105 374251895135081424830980579)
            ·
              refine ⟨561377842702622137246470869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374251895135081424830980579 561377842702622137246470869)
              ·
                refine ⟨13157293188342706341714161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 561377842702622137246470869 13157293188342706341714161)
                ·
                  refine ⟨9867969891257029756285621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13157293188342706341714161 9867969891257029756285621)
                  ·
                    refine ⟨925122177305346539651777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9867969891257029756285621 925122177305346539651777)
                    ·
                      rfl

theorem cell23_5405007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_5405007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405007 prefixEnd_5405007 := by exact prefixLift 5405007
  have htrace : WordTrace (prefixWord ++ tailWord_5405007) baseStart_5405007 baseEnd_5405007 := by
    simpa [prefixWord, tailWord_5405007, baseEnd_5405007] using wordTrace_append hprefix tailTrace_5405007
  have hstable : (prefixWord ++ tailWord_5405007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405007).length < 2 ^ (prefixWord ++ tailWord_5405007).sum := by decide
  have hdescent : baseEnd_5405007 < baseStart_5405007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405064 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_5405064 : Nat := 118140960795 + 5405064 * 2 ^ 59
def prefixEnd_5405064 : Nat := 4983230072969 + 3 ^ 40 * 5405064 * 2
def baseEnd_5405064 : Nat := 2775395800313345895942569

theorem tailTrace_5405064 : CollatzResearch.WordTrace tailWord_5405064 prefixEnd_5405064 2775395800313345895942569 := by
  unfold tailWord_5405064
  simp only [CollatzResearch.WordTrace]
  refine ⟨98569439845191857141827123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131425919793589142855769497 98569439845191857141827123)
  ·
    refine ⟨147854159767787785712740685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98569439845191857141827123 147854159767787785712740685)
    ·
      refine ⟨55445309912920419642277757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147854159767787785712740685 55445309912920419642277757)
      ·
        refine ⟨20791991217345157365854159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55445309912920419642277757 20791991217345157365854159)
        ·
          refine ⟨31187986826017736048781239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20791991217345157365854159 31187986826017736048781239)
          ·
            refine ⟨46781980239026604073171859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31187986826017736048781239 46781980239026604073171859)
            ·
              refine ⟨70172970358539906109757789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46781980239026604073171859 70172970358539906109757789)
              ·
                refine ⟨26314863884452464791159171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70172970358539906109757789 26314863884452464791159171)
                ·
                  refine ⟨39472295826678697186738757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26314863884452464791159171 39472295826678697186738757)
                  ·
                    refine ⟨7401055467502255722513517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39472295826678697186738757 7401055467502255722513517)
                    ·
                      refine ⟨2775395800313345895942569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401055467502255722513517 2775395800313345895942569)
                      ·
                        rfl

theorem cell23_5405064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_5405064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405064 prefixEnd_5405064 := by exact prefixLift 5405064
  have htrace : WordTrace (prefixWord ++ tailWord_5405064) baseStart_5405064 baseEnd_5405064 := by
    simpa [prefixWord, tailWord_5405064, baseEnd_5405064] using wordTrace_append hprefix tailTrace_5405064
  have hstable : (prefixWord ++ tailWord_5405064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405064).length < 2 ^ (prefixWord ++ tailWord_5405064).sum := by decide
  have hdescent : baseEnd_5405064 < baseStart_5405064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405067 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 8]
def baseStart_5405067 : Nat := 118140960795 + 5405067 * 2 ^ 59
def prefixEnd_5405067 : Nat := 4983230072969 + 3 ^ 40 * 5405067 * 2
def baseEnd_5405067 : Nat := 308377482306145487133895

theorem tailTrace_5405067 : CollatzResearch.WordTrace tailWord_5405067 prefixEnd_5405067 308377482306145487133895 := by
  unfold tailWord_5405067
  simp only [CollatzResearch.WordTrace]
  refine ⟨197138989109372845796013455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131425992739581897197342303 197138989109372845796013455)
  ·
    refine ⟨295708483664059268694020183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197138989109372845796013455 295708483664059268694020183)
    ·
      refine ⟨443562725496088903041030275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295708483664059268694020183 443562725496088903041030275)
      ·
        refine ⟨665344088244133354561545413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443562725496088903041030275 665344088244133354561545413)
        ·
          refine ⟨124752016545775003980289765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 665344088244133354561545413 124752016545775003980289765)
          ·
            refine ⟨23391003102332813246304331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124752016545775003980289765 23391003102332813246304331)
            ·
              refine ⟨35086504653499219869456497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23391003102332813246304331 35086504653499219869456497)
              ·
                refine ⟨26314878490124414902092373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35086504653499219869456497 26314878490124414902092373)
                ·
                  refine ⟨308377482306145487133895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26314878490124414902092373 308377482306145487133895)
                  ·
                    rfl

theorem cell23_5405067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 8].length) (baseStart_5405067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405067 prefixEnd_5405067 := by exact prefixLift 5405067
  have htrace : WordTrace (prefixWord ++ tailWord_5405067) baseStart_5405067 baseEnd_5405067 := by
    simpa [prefixWord, tailWord_5405067, baseEnd_5405067] using wordTrace_append hprefix tailTrace_5405067
  have hstable : (prefixWord ++ tailWord_5405067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405067).length < 2 ^ (prefixWord ++ tailWord_5405067).sum := by decide
  have hdescent : baseEnd_5405067 < baseStart_5405067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405168 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2]
def baseStart_5405168 : Nat := 118140960795 + 5405168 * 2 ^ 59
def prefixEnd_5405168 : Nat := 4983230072969 + 3 ^ 40 * 5405168 * 2
def baseEnd_5405168 : Nat := 2775449202301413489042091

theorem tailTrace_5405168 : CollatzResearch.WordTrace tailWord_5405168 prefixEnd_5405168 2775449202301413489042091 := by
  unfold tailWord_5405168
  simp only [CollatzResearch.WordTrace]
  refine ⟨98571336441003470022720079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131428448588004626696960105 98571336441003470022720079)
  ·
    refine ⟨147857004661505205034080119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98571336441003470022720079 147857004661505205034080119)
    ·
      refine ⟨221785506992257807551120179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147857004661505205034080119 221785506992257807551120179)
      ·
        refine ⟨332678260488386711326680269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221785506992257807551120179 332678260488386711326680269)
        ·
          refine ⟨124754347683145016747505101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332678260488386711326680269 124754347683145016747505101)
          ·
            refine ⟨46782880381179381280314413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124754347683145016747505101 46782880381179381280314413)
            ·
              refine ⟨17543580142942267980117905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46782880381179381280314413 17543580142942267980117905)
              ·
                refine ⟨13157685107206700985088429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17543580142942267980117905 13157685107206700985088429)
                ·
                  refine ⟨4934131915202512869408161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13157685107206700985088429 4934131915202512869408161)
                  ·
                    refine ⟨3700598936401884652056121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934131915202512869408161 3700598936401884652056121)
                    ·
                      refine ⟨2775449202301413489042091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700598936401884652056121 2775449202301413489042091)
                      ·
                        rfl

theorem cell23_5405168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 2, 2].length) (baseStart_5405168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405168 prefixEnd_5405168 := by exact prefixLift 5405168
  have htrace : WordTrace (prefixWord ++ tailWord_5405168) baseStart_5405168 baseEnd_5405168 := by
    simpa [prefixWord, tailWord_5405168, baseEnd_5405168] using wordTrace_append hprefix tailTrace_5405168
  have hstable : (prefixWord ++ tailWord_5405168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405168).length < 2 ^ (prefixWord ++ tailWord_5405168).sum := by decide
  have hdescent : baseEnd_5405168 < baseStart_5405168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405171 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 3]
def baseStart_5405171 : Nat := 118140960795 + 5405171 * 2 ^ 59
def prefixEnd_5405171 : Nat := 4983230072969 + 3 ^ 40 * 5405171 * 2
def baseEnd_5405171 : Nat := 2775450742743376977304577

theorem tailTrace_5405171 : CollatzResearch.WordTrace tailWord_5405171 prefixEnd_5405171 2775450742743376977304577 := by
  unfold tailWord_5405171
  simp only [CollatzResearch.WordTrace]
  refine ⟨197142782300996071557799367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131428521533997381038532911 197142782300996071557799367)
  ·
    refine ⟨295714173451494107336699051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197142782300996071557799367 295714173451494107336699051)
    ·
      refine ⟨443571260177241161005048577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295714173451494107336699051 443571260177241161005048577)
      ·
        refine ⟨332678445132930870753786433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443571260177241161005048577 332678445132930870753786433)
        ·
          refine ⟨249508833849698153065339825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332678445132930870753786433 249508833849698153065339825)
          ·
            refine ⟨187131625387273614799004869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249508833849698153065339825 187131625387273614799004869)
            ·
              refine ⟨35087179760113802774813413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187131625387273614799004869 35087179760113802774813413)
              ·
                refine ⟨6578846205021338020277515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35087179760113802774813413 6578846205021338020277515)
                ·
                  refine ⟨9868269307532007030416273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6578846205021338020277515 9868269307532007030416273)
                  ·
                    refine ⟨7401201980649005272812205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9868269307532007030416273 7401201980649005272812205)
                    ·
                      refine ⟨2775450742743376977304577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401201980649005272812205 2775450742743376977304577)
                      ·
                        rfl

theorem cell23_5405171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_5405171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405171 prefixEnd_5405171 := by exact prefixLift 5405171
  have htrace : WordTrace (prefixWord ++ tailWord_5405171) baseStart_5405171 baseEnd_5405171 := by
    simpa [prefixWord, tailWord_5405171, baseEnd_5405171] using wordTrace_append hprefix tailTrace_5405171
  have hstable : (prefixWord ++ tailWord_5405171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405171).length < 2 ^ (prefixWord ++ tailWord_5405171).sum := by decide
  have hdescent : baseEnd_5405171 < baseStart_5405171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405185 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_5405185 : Nat := 118140960795 + 5405185 * 2 ^ 59
def prefixEnd_5405185 : Nat := 4983230072969 + 3 ^ 40 * 5405185 * 2
def baseEnd_5405185 : Nat := 2775457931472539922529513

theorem tailTrace_5405185 : CollatzResearch.WordTrace tailWord_5405185 prefixEnd_5405185 2775457931472539922529513 := by
  unfold tailWord_5405185
  simp only [CollatzResearch.WordTrace]
  refine ⟨197143292922945351948809009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131428861948630234632539339 197143292922945351948809009)
  ·
    refine ⟨147857469692209013961606757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197143292922945351948809009 147857469692209013961606757)
    ·
      refine ⟨27723275567289190117801267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147857469692209013961606757 27723275567289190117801267)
      ·
        refine ⟨41584913350933785176701901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27723275567289190117801267 41584913350933785176701901)
        ·
          refine ⟨15594342506600169441263213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41584913350933785176701901 15594342506600169441263213)
          ·
            refine ⟨5847878439975063540473705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15594342506600169441263213 5847878439975063540473705)
            ·
              refine ⟨4385908829981297655355279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5847878439975063540473705 4385908829981297655355279)
              ·
                refine ⟨6578863244971946483032919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385908829981297655355279 6578863244971946483032919)
                ·
                  refine ⟨9868294867457919724549379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6578863244971946483032919 9868294867457919724549379)
                  ·
                    refine ⟨14802442301186879586824069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9868294867457919724549379 14802442301186879586824069)
                    ·
                      refine ⟨2775457931472539922529513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14802442301186879586824069 2775457931472539922529513)
                      ·
                        rfl

theorem cell23_5405185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_5405185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405185 prefixEnd_5405185 := by exact prefixLift 5405185
  have htrace : WordTrace (prefixWord ++ tailWord_5405185) baseStart_5405185 baseEnd_5405185 := by
    simpa [prefixWord, tailWord_5405185, baseEnd_5405185] using wordTrace_append hprefix tailTrace_5405185
  have hstable : (prefixWord ++ tailWord_5405185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405185).length < 2 ^ (prefixWord ++ tailWord_5405185).sum := by decide
  have hdescent : baseEnd_5405185 < baseStart_5405185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405234 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_5405234 : Nat := 118140960795 + 5405234 * 2 ^ 59
def prefixEnd_5405234 : Nat := 4983230072969 + 3 ^ 40 * 5405234 * 2
def baseEnd_5405234 : Nat := 925161030674870076938929

theorem tailTrace_5405234 : CollatzResearch.WordTrace tailWord_5405234 prefixEnd_5405234 925161030674870076938929 := by
  unfold tailWord_5405234
  simp only [CollatzResearch.WordTrace]
  refine ⟨49286270024941958329335689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131430053399845222211561837 49286270024941958329335689)
  ·
    refine ⟨36964702518706468747001767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49286270024941958329335689 36964702518706468747001767)
    ·
      refine ⟨55447053778059703120502651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36964702518706468747001767 55447053778059703120502651)
      ·
        refine ⟨83170580667089554680753977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55447053778059703120502651 83170580667089554680753977)
        ·
          refine ⟨62377935500317166010565483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83170580667089554680753977 62377935500317166010565483)
          ·
            refine ⟨93566903250475749015848225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62377935500317166010565483 93566903250475749015848225)
            ·
              refine ⟨70175177437856811761886169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93566903250475749015848225 70175177437856811761886169)
              ·
                refine ⟨52631383078392608821414627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70175177437856811761886169 52631383078392608821414627)
                ·
                  refine ⟨78947074617588913232121941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52631383078392608821414627 78947074617588913232121941)
                  ·
                    refine ⟨925161030674870076938929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78947074617588913232121941 925161030674870076938929)
                    ·
                      rfl

theorem cell23_5405234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_5405234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405234 prefixEnd_5405234 := by exact prefixLift 5405234
  have htrace : WordTrace (prefixWord ++ tailWord_5405234) baseStart_5405234 baseEnd_5405234 := by
    simpa [prefixWord, tailWord_5405234, baseEnd_5405234] using wordTrace_append hprefix tailTrace_5405234
  have hstable : (prefixWord ++ tailWord_5405234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405234).length < 2 ^ (prefixWord ++ tailWord_5405234).sum := by decide
  have hdescent : baseEnd_5405234 < baseStart_5405234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405245 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5405245 : Nat := 118140960795 + 5405245 * 2 ^ 59
def prefixEnd_5405245 : Nat := 4983230072969 + 3 ^ 40 * 5405245 * 2
def baseEnd_5405245 : Nat := 2775488740311809687779237

theorem tailTrace_5405245 : CollatzResearch.WordTrace tailWord_5405245 prefixEnd_5405245 2775488740311809687779237 := by
  unfold tailWord_5405245
  simp only [CollatzResearch.WordTrace]
  refine ⟨197145481302727982195993189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131430320868485321463995459 197145481302727982195993189)
  ·
    refine ⟨36964777744261496661748723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197145481302727982195993189 36964777744261496661748723)
    ·
      refine ⟨55447166616392244992623085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36964777744261496661748723 55447166616392244992623085)
      ·
        refine ⟨20792687481147091872233657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55447166616392244992623085 20792687481147091872233657)
        ·
          refine ⟨15594515610860318904175243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20792687481147091872233657 15594515610860318904175243)
          ·
            refine ⟨23391773416290478356262865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15594515610860318904175243 23391773416290478356262865)
            ·
              refine ⟨17543830062217858767197149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23391773416290478356262865 17543830062217858767197149)
              ·
                refine ⟨6578936273331697037698931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17543830062217858767197149 6578936273331697037698931)
                ·
                  refine ⟨9868404409997545556548397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6578936273331697037698931 9868404409997545556548397)
                  ·
                    refine ⟨3700651653749079583705649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9868404409997545556548397 3700651653749079583705649)
                    ·
                      refine ⟨2775488740311809687779237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700651653749079583705649 2775488740311809687779237)
                      ·
                        rfl

theorem cell23_5405245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5405245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405245 prefixEnd_5405245 := by exact prefixLift 5405245
  have htrace : WordTrace (prefixWord ++ tailWord_5405245) baseStart_5405245 baseEnd_5405245 := by
    simpa [prefixWord, tailWord_5405245, baseEnd_5405245] using wordTrace_append hprefix tailTrace_5405245
  have hstable : (prefixWord ++ tailWord_5405245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405245).length < 2 ^ (prefixWord ++ tailWord_5405245).sum := by decide
  have hdescent : baseEnd_5405245 < baseStart_5405245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405264 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 7]
def baseStart_5405264 : Nat := 118140960795 + 5405264 * 2 ^ 59
def prefixEnd_5405264 : Nat := 4983230072969 + 3 ^ 40 * 5405264 * 2
def baseEnd_5405264 : Nat := 308388721827138345937961

theorem tailTrace_5405264 : CollatzResearch.WordTrace tailWord_5405264 prefixEnd_5405264 308388721827138345937961 := by
  unfold tailWord_5405264
  simp only [CollatzResearch.WordTrace]
  refine ⟨98573087144829574220467423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131430782859772765627289897 98573087144829574220467423)
  ·
    refine ⟨147859630717244361330701135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98573087144829574220467423 147859630717244361330701135)
    ·
      refine ⟨221789446075866541996051703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147859630717244361330701135 221789446075866541996051703)
      ·
        refine ⟨332684169113799812994077555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221789446075866541996051703 332684169113799812994077555)
        ·
          refine ⟨499026253670699719491116333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332684169113799812994077555 499026253670699719491116333)
          ·
            refine ⟨187134845126512394809168625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499026253670699719491116333 187134845126512394809168625)
            ·
              refine ⟨140351133844884296106876469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187134845126512394809168625 140351133844884296106876469)
              ·
                refine ⟨13157918797957902760019669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140351133844884296106876469 13157918797957902760019669)
                ·
                  refine ⟨308388721827138345937961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13157918797957902760019669 308388721827138345937961)
                  ·
                    rfl

theorem cell23_5405264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_5405264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405264 prefixEnd_5405264 := by exact prefixLift 5405264
  have htrace : WordTrace (prefixWord ++ tailWord_5405264) baseStart_5405264 baseEnd_5405264 := by
    simpa [prefixWord, tailWord_5405264, baseEnd_5405264] using wordTrace_append hprefix tailTrace_5405264
  have hstable : (prefixWord ++ tailWord_5405264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405264).length < 2 ^ (prefixWord ++ tailWord_5405264).sum := by decide
  have hdescent : baseEnd_5405264 < baseStart_5405264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405304 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_5405304 : Nat := 118140960795 + 5405304 * 2 ^ 59
def prefixEnd_5405304 : Nat := 4983230072969 + 3 ^ 40 * 5405304 * 2
def baseEnd_5405304 : Nat := 2775519035670424956941465

theorem tailTrace_5405304 : CollatzResearch.WordTrace tailWord_5405304 prefixEnd_5405304 2775519035670424956941465 := by
  unfold tailWord_5405304
  simp only [CollatzResearch.WordTrace]
  refine ⟨98573816604757117636195483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131431755473009490181593977 98573816604757117636195483)
  ·
    refine ⟨147860724907135676454293225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98573816604757117636195483 147860724907135676454293225)
    ·
      refine ⟨110895543680351757340719919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147860724907135676454293225 110895543680351757340719919)
      ·
        refine ⟨166343315520527636011079879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110895543680351757340719919 166343315520527636011079879)
        ·
          refine ⟨249514973280791454016619819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166343315520527636011079879 249514973280791454016619819)
          ·
            refine ⟨374272459921187181024929729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249514973280791454016619819 374272459921187181024929729)
            ·
              refine ⟨280704344940890385768697297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374272459921187181024929729 280704344940890385768697297)
              ·
                refine ⟨210528258705667789326522973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280704344940890385768697297 210528258705667789326522973)
                ·
                  refine ⟨78948097014625420997446115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210528258705667789326522973 78948097014625420997446115)
                  ·
                    refine ⟨118422145521938131496169173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78948097014625420997446115 118422145521938131496169173)
                    ·
                      refine ⟨2775519035670424956941465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118422145521938131496169173 2775519035670424956941465)
                      ·
                        rfl

theorem cell23_5405304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_5405304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405304 prefixEnd_5405304 := by exact prefixLift 5405304
  have htrace : WordTrace (prefixWord ++ tailWord_5405304) baseStart_5405304 baseEnd_5405304 := by
    simpa [prefixWord, tailWord_5405304, baseEnd_5405304] using wordTrace_append hprefix tailTrace_5405304
  have hstable : (prefixWord ++ tailWord_5405304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405304).length < 2 ^ (prefixWord ++ tailWord_5405304).sum := by decide
  have hdescent : baseEnd_5405304 < baseStart_5405304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405345 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_5405345 : Nat := 118140960795 + 5405345 * 2 ^ 59
def prefixEnd_5405345 : Nat := 4983230072969 + 3 ^ 40 * 5405345 * 2
def baseEnd_5405345 : Nat := 925180029459086432176259

theorem tailTrace_5405345 : CollatzResearch.WordTrace tailWord_5405345 prefixEnd_5405345 925180029459086432176259 := by
  unfold tailWord_5405345
  simp only [CollatzResearch.WordTrace]
  refine ⟨197149128602365699274633489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131432752401577132849755659 197149128602365699274633489)
  ·
    refine ⟨147861846451774274455975117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197149128602365699274633489 147861846451774274455975117)
    ·
      refine ⟨55448192419415352920990669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147861846451774274455975117 55448192419415352920990669)
      ·
        refine ⟨20793072157280757345371501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55448192419415352920990669 20793072157280757345371501)
        ·
          refine ⟨7797402058980284004514313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20793072157280757345371501 7797402058980284004514313)
          ·
            refine ⟨5848051544235213003385735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7797402058980284004514313 5848051544235213003385735)
            ·
              refine ⟨8772077316352819505078603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848051544235213003385735 8772077316352819505078603)
              ·
                refine ⟨13158115974529229257617905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772077316352819505078603 13158115974529229257617905)
                ·
                  refine ⟨9868586980896921943213429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13158115974529229257617905 9868586980896921943213429)
                  ·
                    refine ⟨925180029459086432176259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9868586980896921943213429 925180029459086432176259)
                    ·
                      rfl

theorem cell23_5405345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_5405345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405345 prefixEnd_5405345 := by exact prefixLift 5405345
  have htrace : WordTrace (prefixWord ++ tailWord_5405345) baseStart_5405345 baseEnd_5405345 := by
    simpa [prefixWord, tailWord_5405345, baseEnd_5405345] using wordTrace_append hprefix tailTrace_5405345
  have hstable : (prefixWord ++ tailWord_5405345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405345).length < 2 ^ (prefixWord ++ tailWord_5405345).sum := by decide
  have hdescent : baseEnd_5405345 < baseStart_5405345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405348 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_5405348 : Nat := 118140960795 + 5405348 * 2 ^ 59
def prefixEnd_5405348 : Nat := 4983230072969 + 3 ^ 40 * 5405348 * 2
def baseEnd_5405348 : Nat := 2775541628819222784791263

theorem tailTrace_5405348 : CollatzResearch.WordTrace tailWord_5405348 prefixEnd_5405348 2775541628819222784791263 := by
  unfold tailWord_5405348
  simp only [CollatzResearch.WordTrace]
  refine ⟨98574619010677415393496349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131432825347569887191328465 98574619010677415393496349)
  ·
    refine ⟨36965482129004030772561131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98574619010677415393496349 36965482129004030772561131)
    ·
      refine ⟨55448223193506046158841697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36965482129004030772561131 55448223193506046158841697)
      ·
        refine ⟨41586167395129534619131273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55448223193506046158841697 41586167395129534619131273)
        ·
          refine ⟨31189625546347150964348455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41586167395129534619131273 31189625546347150964348455)
          ·
            refine ⟨46784438319520726446522683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31189625546347150964348455 46784438319520726446522683)
            ·
              refine ⟨70176657479281089669784025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46784438319520726446522683 70176657479281089669784025)
              ·
                refine ⟨52632493109460817252338019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70176657479281089669784025 52632493109460817252338019)
                ·
                  refine ⟨78948739664191225878507029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52632493109460817252338019 78948739664191225878507029)
                  ·
                    refine ⟨3700722171758963713055017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78948739664191225878507029 3700722171758963713055017)
                    ·
                      refine ⟨2775541628819222784791263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700722171758963713055017 2775541628819222784791263)
                      ·
                        rfl

theorem cell23_5405348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_5405348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405348 prefixEnd_5405348 := by exact prefixLift 5405348
  have htrace : WordTrace (prefixWord ++ tailWord_5405348) baseStart_5405348 baseEnd_5405348 := by
    simpa [prefixWord, tailWord_5405348, baseEnd_5405348] using wordTrace_append hprefix tailTrace_5405348
  have hstable : (prefixWord ++ tailWord_5405348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405348).length < 2 ^ (prefixWord ++ tailWord_5405348).sum := by decide
  have hdescent : baseEnd_5405348 < baseStart_5405348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405365 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5405365 : Nat := 118140960795 + 5405365 * 2 ^ 59
def prefixEnd_5405365 : Nat := 4983230072969 + 3 ^ 40 * 5405365 * 2
def baseEnd_5405365 : Nat := 2775550357990349218278685

theorem tailTrace_5405365 : CollatzResearch.WordTrace tailWord_5405365 prefixEnd_5405365 2775550357990349218278685 := by
  unfold tailWord_5405365
  simp only [CollatzResearch.WordTrace]
  refine ⟨197149858062293242690361549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131433238708195495126907699 197149858062293242690361549)
  ·
    refine ⟨73931196773359966008885581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197149858062293242690361549 73931196773359966008885581)
    ·
      refine ⟨27724198790009987253332093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73931196773359966008885581 27724198790009987253332093)
      ·
        refine ⟨10396574546253745219999535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27724198790009987253332093 10396574546253745219999535)
        ·
          refine ⟨15594861819380617829999303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10396574546253745219999535 15594861819380617829999303)
          ·
            refine ⟨23392292729070926744998955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15594861819380617829999303 23392292729070926744998955)
            ·
              refine ⟨35088439093606390117498433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23392292729070926744998955 35088439093606390117498433)
              ·
                refine ⟨26316329320204792588123825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35088439093606390117498433 26316329320204792588123825)
                ·
                  refine ⟨19737246990153594441092869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26316329320204792588123825 19737246990153594441092869)
                  ·
                    refine ⟨3700733810653798957704913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19737246990153594441092869 3700733810653798957704913)
                    ·
                      refine ⟨2775550357990349218278685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700733810653798957704913 2775550357990349218278685)
                      ·
                        rfl

theorem cell23_5405365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5405365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405365 prefixEnd_5405365 := by exact prefixLift 5405365
  have htrace : WordTrace (prefixWord ++ tailWord_5405365) baseStart_5405365 baseEnd_5405365 := by
    simpa [prefixWord, tailWord_5405365, baseEnd_5405365] using wordTrace_append hprefix tailTrace_5405365
  have hstable : (prefixWord ++ tailWord_5405365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405365).length < 2 ^ (prefixWord ++ tailWord_5405365).sum := by decide
  have hdescent : baseEnd_5405365 < baseStart_5405365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405375 : List Nat := [1, 1, 2, 2, 2, 4, 2, 4, 1, 4]
def baseStart_5405375 : Nat := 118140960795 + 5405375 * 2 ^ 59
def prefixEnd_5405375 : Nat := 4983230072969 + 3 ^ 40 * 5405375 * 2
def baseEnd_5405375 : Nat := 925185164265631393051213

theorem tailTrace_5405375 : CollatzResearch.WordTrace tailWord_5405375 prefixEnd_5405375 925185164265631393051213 := by
  unfold tailWord_5405375
  simp only [CollatzResearch.WordTrace]
  refine ⟨197150222792257014398225579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131433481861504676265483719 197150222792257014398225579)
  ·
    refine ⟨295725334188385521597338369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197150222792257014398225579 295725334188385521597338369)
    ·
      refine ⟨221794000641289141198003777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295725334188385521597338369 221794000641289141198003777)
      ·
        refine ⟨166345500480966855898502833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221794000641289141198003777 166345500480966855898502833)
        ·
          refine ⟨124759125360725141923877125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166345500480966855898502833 124759125360725141923877125)
          ·
            refine ⟨23392336005135964110726961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124759125360725141923877125 23392336005135964110726961)
            ·
              refine ⟨17544252003851973083045221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23392336005135964110726961 17544252003851973083045221)
              ·
                refine ⟨3289547250722244953070979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17544252003851973083045221 3289547250722244953070979)
                ·
                  refine ⟨4934320876083367429606469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289547250722244953070979 4934320876083367429606469)
                  ·
                    refine ⟨925185164265631393051213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4934320876083367429606469 925185164265631393051213)
                    ·
                      rfl

theorem cell23_5405375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4, 1, 4].length) (baseStart_5405375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405375 prefixEnd_5405375 := by exact prefixLift 5405375
  have htrace : WordTrace (prefixWord ++ tailWord_5405375) baseStart_5405375 baseEnd_5405375 := by
    simpa [prefixWord, tailWord_5405375, baseEnd_5405375] using wordTrace_append hprefix tailTrace_5405375
  have hstable : (prefixWord ++ tailWord_5405375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405375).length < 2 ^ (prefixWord ++ tailWord_5405375).sum := by decide
  have hdescent : baseEnd_5405375 < baseStart_5405375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405381 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_5405381 : Nat := 118140960795 + 5405381 * 2 ^ 59
def prefixEnd_5405381 : Nat := 4983230072969 + 3 ^ 40 * 5405381 * 2
def baseEnd_5405381 : Nat := 2775558573680821155678611

theorem tailTrace_5405381 : CollatzResearch.WordTrace tailWord_5405381 prefixEnd_5405381 2775558573680821155678611 := by
  unfold tailWord_5405381
  simp only [CollatzResearch.WordTrace]
  refine ⟨197150441630235277422943997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131433627753490184948629331 197150441630235277422943997)
  ·
    refine ⟨73931415611338229033603999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197150441630235277422943997 73931415611338229033603999)
    ·
      refine ⟨110897123417007343550405999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73931415611338229033603999 110897123417007343550405999)
      ·
        refine ⟨166345685125511015325608999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110897123417007343550405999 166345685125511015325608999)
        ·
          refine ⟨249518527688266522988413499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166345685125511015325608999 249518527688266522988413499)
          ·
            refine ⟨374277791532399784482620249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249518527688266522988413499 374277791532399784482620249)
            ·
              refine ⟨280708343649299838361965187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374277791532399784482620249 280708343649299838361965187)
              ·
                refine ⟨421062515473949757542947781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280708343649299838361965187 421062515473949757542947781)
                ·
                  refine ⟨78949221651365579539302709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421062515473949757542947781 78949221651365579539302709)
                  ·
                    refine ⟨7401489529815523081809629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78949221651365579539302709 7401489529815523081809629)
                    ·
                      refine ⟨2775558573680821155678611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401489529815523081809629 2775558573680821155678611)
                      ·
                        rfl

theorem cell23_5405381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_5405381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405381 prefixEnd_5405381 := by exact prefixLift 5405381
  have htrace : WordTrace (prefixWord ++ tailWord_5405381) baseStart_5405381 baseEnd_5405381 := by
    simpa [prefixWord, tailWord_5405381, baseEnd_5405381] using wordTrace_append hprefix tailTrace_5405381
  have hstable : (prefixWord ++ tailWord_5405381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405381).length < 2 ^ (prefixWord ++ tailWord_5405381).sum := by decide
  have hdescent : baseEnd_5405381 < baseStart_5405381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405425 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_5405425 : Nat := 118140960795 + 5405425 * 2 ^ 59
def prefixEnd_5405425 : Nat := 4983230072969 + 3 ^ 40 * 5405425 * 2
def baseEnd_5405425 : Nat := 2775581166829618983528409

theorem tailTrace_5405425 : CollatzResearch.WordTrace tailWord_5405425 prefixEnd_5405425 2775581166829618983528409 := by
  unfold tailWord_5405425
  simp only [CollatzResearch.WordTrace]
  refine ⟨197152046442075872937545729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131434697628050581958363819 197152046442075872937545729)
  ·
    refine ⟨147864034831556904703159297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197152046442075872937545729 147864034831556904703159297)
    ·
      refine ⟨110898026123667678527369473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147864034831556904703159297 110898026123667678527369473)
      ·
        refine ⟨83173519592750758895527105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110898026123667678527369473 83173519592750758895527105)
        ·
          refine ⟨62380139694563069171645329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83173519592750758895527105 62380139694563069171645329)
          ·
            refine ⟨46785104770922301878733997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62380139694563069171645329 46785104770922301878733997)
            ·
              refine ⟨17544414289095863204525249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46785104770922301878733997 17544414289095863204525249)
              ·
                refine ⟨13158310716821897403393937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17544414289095863204525249 13158310716821897403393937)
                ·
                  refine ⟨9868733037616423052545453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13158310716821897403393937 9868733037616423052545453)
                  ·
                    refine ⟨3700774889106158644704545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9868733037616423052545453 3700774889106158644704545)
                    ·
                      refine ⟨2775581166829618983528409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700774889106158644704545 2775581166829618983528409)
                      ·
                        rfl

theorem cell23_5405425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_5405425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405425 prefixEnd_5405425 := by exact prefixLift 5405425
  have htrace : WordTrace (prefixWord ++ tailWord_5405425) baseStart_5405425 baseEnd_5405425 := by
    simpa [prefixWord, tailWord_5405425, baseEnd_5405425] using wordTrace_append hprefix tailTrace_5405425
  have hstable : (prefixWord ++ tailWord_5405425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405425).length < 2 ^ (prefixWord ++ tailWord_5405425).sum := by decide
  have hdescent : baseEnd_5405425 < baseStart_5405425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405455 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 5, 2, 2]
def baseStart_5405455 : Nat := 118140960795 + 5405455 * 2 ^ 59
def prefixEnd_5405455 : Nat := 4983230072969 + 3 ^ 40 * 5405455 * 2
def baseEnd_5405455 : Nat := 2775596571249253866153271

theorem tailTrace_5405455 : CollatzResearch.WordTrace tailWord_5405455 prefixEnd_5405455 2775596571249253866153271 := by
  unfold tailWord_5405455
  simp only [CollatzResearch.WordTrace]
  refine ⟨197153140631967188061137819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131435427087978125374091879 197153140631967188061137819)
  ·
    refine ⟨295729710947950782091706729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197153140631967188061137819 295729710947950782091706729)
    ·
      refine ⟨221797283210963086568780047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295729710947950782091706729 221797283210963086568780047)
      ·
        refine ⟨332695924816444629853170071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221797283210963086568780047 332695924816444629853170071)
        ·
          refine ⟨499043887224666944779755107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332695924816444629853170071 499043887224666944779755107)
          ·
            refine ⟨748565830837000417169632661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499043887224666944779755107 748565830837000417169632661)
            ·
              refine ⟨35089023320484394554826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 748565830837000417169632661 35089023320484394554826531)
              ·
                refine ⟨52633534980726591832239797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35089023320484394554826531 52633534980726591832239797)
                ·
                  refine ⟨4934393904443117984272481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52633534980726591832239797 4934393904443117984272481)
                  ·
                    refine ⟨3700795428332338488204361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934393904443117984272481 3700795428332338488204361)
                    ·
                      refine ⟨2775596571249253866153271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700795428332338488204361 2775596571249253866153271)
                      ·
                        rfl

theorem cell23_5405455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 2, 2].length) (baseStart_5405455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405455 prefixEnd_5405455 := by exact prefixLift 5405455
  have htrace : WordTrace (prefixWord ++ tailWord_5405455) baseStart_5405455 baseEnd_5405455 := by
    simpa [prefixWord, tailWord_5405455, baseEnd_5405455] using wordTrace_append hprefix tailTrace_5405455
  have hstable : (prefixWord ++ tailWord_5405455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405455).length < 2 ^ (prefixWord ++ tailWord_5405455).sum := by decide
  have hdescent : baseEnd_5405455 < baseStart_5405455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405461 : List Nat := [1, 3, 2, 1, 2, 2, 1, 11]
def baseStart_5405461 : Nat := 118140960795 + 5405461 * 2 ^ 59
def prefixEnd_5405461 : Nat := 4983230072969 + 3 ^ 40 * 5405461 * 2
def baseEnd_5405461 : Nat := 102799987116043734914009

theorem tailTrace_5405461 : CollatzResearch.WordTrace tailWord_5405461 prefixEnd_5405461 102799987116043734914009 := by
  unfold tailWord_5405461
  simp only [CollatzResearch.WordTrace]
  refine ⟨197153359469945451085856237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131435572979963634057237491 197153359469945451085856237)
  ·
    refine ⟨73932509801229544157196089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197153359469945451085856237 73932509801229544157196089)
    ·
      refine ⟨55449382350922158117897067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73932509801229544157196089 55449382350922158117897067)
      ·
        refine ⟨83174073526383237176845601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55449382350922158117897067 83174073526383237176845601)
        ·
          refine ⟨62380555144787427882634201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83174073526383237176845601 62380555144787427882634201)
          ·
            refine ⟨46785416358590570911975651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62380555144787427882634201 46785416358590570911975651)
            ·
              refine ⟨70178124537885856367963477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46785416358590570911975651 70178124537885856367963477)
              ·
                refine ⟨102799987116043734914009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 70178124537885856367963477 102799987116043734914009)
                ·
                  rfl

theorem cell23_5405461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 11].length) (baseStart_5405461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405461 prefixEnd_5405461 := by exact prefixLift 5405461
  have htrace : WordTrace (prefixWord ++ tailWord_5405461) baseStart_5405461 baseEnd_5405461 := by
    simpa [prefixWord, tailWord_5405461, baseEnd_5405461] using wordTrace_append hprefix tailTrace_5405461
  have hstable : (prefixWord ++ tailWord_5405461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405461).length < 2 ^ (prefixWord ++ tailWord_5405461).sum := by decide
  have hdescent : baseEnd_5405461 < baseStart_5405461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405468 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5405468 : Nat := 118140960795 + 5405468 * 2 ^ 59
def prefixEnd_5405468 : Nat := 4983230072969 + 3 ^ 40 * 5405468 * 2
def baseEnd_5405468 : Nat := 2775603246497762315290711

theorem tailTrace_5405468 : CollatzResearch.WordTrace tailWord_5405468 prefixEnd_5405468 2775603246497762315290711 := by
  unfold tailWord_5405468
  simp only [CollatzResearch.WordTrace]
  refine ⟨98576807390460045640680529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131435743187280060854240705 98576807390460045640680529)
  ·
    refine ⟨73932605542845034230510397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98576807390460045640680529 73932605542845034230510397)
    ·
      refine ⟨27724727078566887836441399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73932605542845034230510397 27724727078566887836441399)
      ·
        refine ⟨41587090617850331754662099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27724727078566887836441399 41587090617850331754662099)
        ·
          refine ⟨62380635926775497631993149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41587090617850331754662099 62380635926775497631993149)
          ·
            refine ⟨23392738472540811611997431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62380635926775497631993149 23392738472540811611997431)
            ·
              refine ⟨35089107708811217417996147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23392738472540811611997431 35089107708811217417996147)
              ·
                refine ⟨52633661563216826126994221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35089107708811217417996147 52633661563216826126994221)
                ·
                  refine ⟨19737623086206309797622833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52633661563216826126994221 19737623086206309797622833)
                  ·
                    refine ⟨14803217314654732348217125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19737623086206309797622833 14803217314654732348217125)
                    ·
                      refine ⟨2775603246497762315290711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14803217314654732348217125 2775603246497762315290711)
                      ·
                        rfl

theorem cell23_5405468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5405468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405468 prefixEnd_5405468 := by exact prefixLift 5405468
  have htrace : WordTrace (prefixWord ++ tailWord_5405468) baseStart_5405468 baseEnd_5405468 := by
    simpa [prefixWord, tailWord_5405468, baseEnd_5405468] using wordTrace_append hprefix tailTrace_5405468
  have hstable : (prefixWord ++ tailWord_5405468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405468).length < 2 ^ (prefixWord ++ tailWord_5405468).sum := by decide
  have hdescent : baseEnd_5405468 < baseStart_5405468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405469 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_5405469 : Nat := 118140960795 + 5405469 * 2 ^ 59
def prefixEnd_5405469 : Nat := 4983230072969 + 3 ^ 40 * 5405469 * 2
def baseEnd_5405469 : Nat := 925201253326138937126069

theorem tailTrace_5405469 : CollatzResearch.WordTrace tailWord_5405469 prefixEnd_5405469 925201253326138937126069 := by
  unfold tailWord_5405469
  simp only [CollatzResearch.WordTrace]
  refine ⟨197153651253916468452147461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131435767502610978968098307 197153651253916468452147461)
  ·
    refine ⟨36966309610109337834777649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197153651253916468452147461 36966309610109337834777649)
    ·
      refine ⟨27724732207582003376083237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36966309610109337834777649 27724732207582003376083237)
      ·
        refine ⟨5198387288921625633015607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27724732207582003376083237 5198387288921625633015607)
        ·
          refine ⟨7797580933382438449523411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198387288921625633015607 7797580933382438449523411)
          ·
            refine ⟨11696371400073657674285117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797580933382438449523411 11696371400073657674285117)
            ·
              refine ⟨4386139275027621627856919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11696371400073657674285117 4386139275027621627856919)
              ·
                refine ⟨6579208912541432441785379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386139275027621627856919 6579208912541432441785379)
                ·
                  refine ⟨9868813368812148662678069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579208912541432441785379 9868813368812148662678069)
                  ·
                    refine ⟨925201253326138937126069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9868813368812148662678069 925201253326138937126069)
                    ·
                      rfl

theorem cell23_5405469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_5405469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405469 prefixEnd_5405469 := by exact prefixLift 5405469
  have htrace : WordTrace (prefixWord ++ tailWord_5405469) baseStart_5405469 baseEnd_5405469 := by
    simpa [prefixWord, tailWord_5405469, baseEnd_5405469] using wordTrace_append hprefix tailTrace_5405469
  have hstable : (prefixWord ++ tailWord_5405469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405469).length < 2 ^ (prefixWord ++ tailWord_5405469).sum := by decide
  have hdescent : baseEnd_5405469 < baseStart_5405469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405472 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5405472 : Nat := 118140960795 + 5405472 * 2 ^ 59
def prefixEnd_5405472 : Nat := 4983230072969 + 3 ^ 40 * 5405472 * 2
def baseEnd_5405472 : Nat := 2775605300420380299640693

theorem tailTrace_5405472 : CollatzResearch.WordTrace tailWord_5405472 prefixEnd_5405472 2775605300420380299640693 := by
  unfold tailWord_5405472
  simp only [CollatzResearch.WordTrace]
  refine ⟨98576880336452799982253335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131435840448603733309671113 98576880336452799982253335)
  ·
    refine ⟨147865320504679199973380003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98576880336452799982253335 147865320504679199973380003)
    ·
      refine ⟨221797980757018799960070005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147865320504679199973380003 221797980757018799960070005)
      ·
        refine ⟨20793560695970512496256563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221797980757018799960070005 20793560695970512496256563)
        ·
          refine ⟨31190341043955768744384845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20793560695970512496256563 31190341043955768744384845)
          ·
            refine ⟨11696377891483413279144317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31190341043955768744384845 11696377891483413279144317)
            ·
              refine ⟨4386141709306279979679119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11696377891483413279144317 4386141709306279979679119)
              ·
                refine ⟨6579212563959419969518679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386141709306279979679119 6579212563959419969518679)
                ·
                  refine ⟨9868818845939129954278019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579212563959419969518679 9868818845939129954278019)
                  ·
                    refine ⟨14803228268908694931417029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9868818845939129954278019 14803228268908694931417029)
                    ·
                      refine ⟨2775605300420380299640693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14803228268908694931417029 2775605300420380299640693)
                      ·
                        rfl

theorem cell23_5405472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5405472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405472 prefixEnd_5405472 := by exact prefixLift 5405472
  have htrace : WordTrace (prefixWord ++ tailWord_5405472) baseStart_5405472 baseEnd_5405472 := by
    simpa [prefixWord, tailWord_5405472, baseEnd_5405472] using wordTrace_append hprefix tailTrace_5405472
  have hstable : (prefixWord ++ tailWord_5405472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405472).length < 2 ^ (prefixWord ++ tailWord_5405472).sum := by decide
  have hdescent : baseEnd_5405472 < baseStart_5405472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405489 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 1, 2, 2]
def baseStart_5405489 : Nat := 118140960795 + 5405489 * 2 ^ 59
def prefixEnd_5405489 : Nat := 4983230072969 + 3 ^ 40 * 5405489 * 2
def baseEnd_5405489 : Nat := 2775614029591506733128115

theorem tailTrace_5405489 : CollatzResearch.WordTrace tailWord_5405489 prefixEnd_5405489 2775614029591506733128115 := by
  unfold tailWord_5405489
  simp only [CollatzResearch.WordTrace]
  refine ⟨197154380713844011867875521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131436253809229341245250347 197154380713844011867875521)
  ·
    refine ⟨147865785535383008900906641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197154380713844011867875521 147865785535383008900906641)
    ·
      refine ⟨110899339151537256675679981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147865785535383008900906641 110899339151537256675679981)
      ·
        refine ⟨41587252181826471253379993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110899339151537256675679981 41587252181826471253379993)
        ·
          refine ⟨31190439136369853440034995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41587252181826471253379993 31190439136369853440034995)
          ·
            refine ⟨46785658704554780160052493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31190439136369853440034995 46785658704554780160052493)
            ·
              refine ⟨17544622014208042560019685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46785658704554780160052493 17544622014208042560019685)
              ·
                refine ⟨3289616627664007980003691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17544622014208042560019685 3289616627664007980003691)
                ·
                  refine ⟨4934424941496011970005537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289616627664007980003691 4934424941496011970005537)
                  ·
                    refine ⟨3700818706122008977504153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934424941496011970005537 3700818706122008977504153)
                    ·
                      refine ⟨2775614029591506733128115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700818706122008977504153 2775614029591506733128115)
                      ·
                        rfl

theorem cell23_5405489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_5405489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405489 prefixEnd_5405489 := by exact prefixLift 5405489
  have htrace : WordTrace (prefixWord ++ tailWord_5405489) baseStart_5405489 baseEnd_5405489 := by
    simpa [prefixWord, tailWord_5405489, baseEnd_5405489] using wordTrace_append hprefix tailTrace_5405489
  have hstable : (prefixWord ++ tailWord_5405489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405489).length < 2 ^ (prefixWord ++ tailWord_5405489).sum := by decide
  have hdescent : baseEnd_5405489 < baseStart_5405489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405502 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_5405502 : Nat := 118140960795 + 5405502 * 2 ^ 59
def prefixEnd_5405502 : Nat := 4983230072969 + 3 ^ 40 * 5405502 * 2
def baseEnd_5405502 : Nat := 2775620704840015182265555

theorem tailTrace_5405502 : CollatzResearch.WordTrace tailWord_5405502 prefixEnd_5405502 2775620704840015182265555 := by
  unfold tailWord_5405502
  simp only [CollatzResearch.WordTrace]
  refine ⟨24644356857849614386012345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131436569908531276725399173 24644356857849614386012345)
  ·
    refine ⟨18483267643387210789509259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24644356857849614386012345 18483267643387210789509259)
    ·
      refine ⟨27724901465080816184263889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18483267643387210789509259 27724901465080816184263889)
      ·
        refine ⟨20793676098810612138197917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27724901465080816184263889 20793676098810612138197917)
        ·
          refine ⟨7797628537053979551824219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20793676098810612138197917 7797628537053979551824219)
          ·
            refine ⟨11696442805580969327736329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797628537053979551824219 11696442805580969327736329)
            ·
              refine ⟨8772332104185726995802247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11696442805580969327736329 8772332104185726995802247)
              ·
                refine ⟨13158498156278590493703371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772332104185726995802247 13158498156278590493703371)
                ·
                  refine ⟨19737747234417885740555057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13158498156278590493703371 19737747234417885740555057)
                  ·
                    refine ⟨14803310425813414305416293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19737747234417885740555057 14803310425813414305416293)
                    ·
                      refine ⟨2775620704840015182265555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14803310425813414305416293 2775620704840015182265555)
                      ·
                        rfl

theorem cell23_5405502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_5405502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405502 prefixEnd_5405502 := by exact prefixLift 5405502
  have htrace : WordTrace (prefixWord ++ tailWord_5405502) baseStart_5405502 baseEnd_5405502 := by
    simpa [prefixWord, tailWord_5405502, baseEnd_5405502] using wordTrace_append hprefix tailTrace_5405502
  have hstable : (prefixWord ++ tailWord_5405502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405502).length < 2 ^ (prefixWord ++ tailWord_5405502).sum := by decide
  have hdescent : baseEnd_5405502 < baseStart_5405502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405531 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_5405531 : Nat := 118140960795 + 5405531 * 2 ^ 59
def prefixEnd_5405531 : Nat := 4983230072969 + 3 ^ 40 * 5405531 * 2
def baseEnd_5405531 : Nat := 2775635595778995568802921

theorem tailTrace_5405531 : CollatzResearch.WordTrace tailWord_5405531 prefixEnd_5405531 2775635595778995568802921 := by
  unfold tailWord_5405531
  simp only [CollatzResearch.WordTrace]
  refine ⟨197155912579691853040904447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131437275053127902027269631 197155912579691853040904447)
  ·
    refine ⟨295733868869537779561356671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197155912579691853040904447 295733868869537779561356671)
    ·
      refine ⟨443600803304306669342035007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295733868869537779561356671 443600803304306669342035007)
      ·
        refine ⟨665401204956460004013052511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443600803304306669342035007 665401204956460004013052511)
        ·
          refine ⟨998101807434690006019578767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665401204956460004013052511 998101807434690006019578767)
          ·
            refine ⟨1497152711152035009029368151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998101807434690006019578767 1497152711152035009029368151)
            ·
              refine ⟨2245729066728052513544052227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497152711152035009029368151 2245729066728052513544052227)
              ·
                refine ⟨3368593600092078770316078341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245729066728052513544052227 3368593600092078770316078341)
                ·
                  refine ⟨631611300017264769434264689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3368593600092078770316078341 631611300017264769434264689)
                  ·
                    refine ⟨473708475012948577075698517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 631611300017264769434264689 473708475012948577075698517)
                    ·
                      refine ⟨2775635595778995568802921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 473708475012948577075698517 2775635595778995568802921)
                      ·
                        rfl

theorem cell23_5405531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_5405531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405531 prefixEnd_5405531 := by exact prefixLift 5405531
  have htrace : WordTrace (prefixWord ++ tailWord_5405531) baseStart_5405531 baseEnd_5405531 := by
    simpa [prefixWord, tailWord_5405531, baseEnd_5405531] using wordTrace_append hprefix tailTrace_5405531
  have hstable : (prefixWord ++ tailWord_5405531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405531).length < 2 ^ (prefixWord ++ tailWord_5405531).sum := by decide
  have hdescent : baseEnd_5405531 < baseStart_5405531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405539 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 3]
def baseStart_5405539 : Nat := 118140960795 + 5405539 * 2 ^ 59
def prefixEnd_5405539 : Nat := 4983230072969 + 3 ^ 40 * 5405539 * 2
def baseEnd_5405539 : Nat := 2775639703624231537502885

theorem tailTrace_5405539 : CollatzResearch.WordTrace tailWord_5405539 prefixEnd_5405539 2775639703624231537502885 := by
  unfold tailWord_5405539
  simp only [CollatzResearch.WordTrace]
  refine ⟨197156204363662870407195671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131437469575775246938130447 197156204363662870407195671)
  ·
    refine ⟨295734306545494305610793507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197156204363662870407195671 295734306545494305610793507)
    ·
      refine ⟨443601459818241458416190261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295734306545494305610793507 443601459818241458416190261)
      ·
        refine ⟨41587636857960136726517837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 443601459818241458416190261 41587636857960136726517837)
        ·
          refine ⟨15595363821735051272444189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41587636857960136726517837 15595363821735051272444189)
          ·
            refine ⟨5848261433150644227166571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15595363821735051272444189 5848261433150644227166571)
            ·
              refine ⟨8772392149725966340749857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848261433150644227166571 8772392149725966340749857)
              ·
                refine ⟨6579294112294474755562393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8772392149725966340749857 6579294112294474755562393)
                ·
                  refine ⟨4934470584220856066671795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6579294112294474755562393 4934470584220856066671795)
                  ·
                    refine ⟨7401705876331284100007693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4934470584220856066671795 7401705876331284100007693)
                    ·
                      refine ⟨2775639703624231537502885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401705876331284100007693 2775639703624231537502885)
                      ·
                        rfl

theorem cell23_5405539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_5405539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405539 prefixEnd_5405539 := by exact prefixLift 5405539
  have htrace : WordTrace (prefixWord ++ tailWord_5405539) baseStart_5405539 baseEnd_5405539 := by
    simpa [prefixWord, tailWord_5405539, baseEnd_5405539] using wordTrace_append hprefix tailTrace_5405539
  have hstable : (prefixWord ++ tailWord_5405539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405539).length < 2 ^ (prefixWord ++ tailWord_5405539).sum := by decide
  have hdescent : baseEnd_5405539 < baseStart_5405539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405602 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_5405602 : Nat := 118140960795 + 5405602 * 2 ^ 59
def prefixEnd_5405602 : Nat := 4983230072969 + 3 ^ 40 * 5405602 * 2
def baseEnd_5405602 : Nat := 308408005878384976779455

theorem tailTrace_5405602 : CollatzResearch.WordTrace tailWord_5405602 prefixEnd_5405602 308408005878384976779455 := by
  unfold tailWord_5405602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49289625540608658041684765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131439001441623088111159373 49289625540608658041684765)
  ·
    refine ⟨18483609577728246765631787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49289625540608658041684765 18483609577728246765631787)
    ·
      refine ⟨27725414366592370148447681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18483609577728246765631787 27725414366592370148447681)
      ·
        refine ⟨20794060774944277611335761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27725414366592370148447681 20794060774944277611335761)
        ·
          refine ⟨15595545581208208208501821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20794060774944277611335761 15595545581208208208501821)
          ·
            refine ⟨5848329592953078078188183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15595545581208208208501821 5848329592953078078188183)
            ·
              refine ⟨8772494389429617117282275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848329592953078078188183 8772494389429617117282275)
              ·
                refine ⟨13158741584144425675923413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772494389429617117282275 13158741584144425675923413)
                ·
                  refine ⟨308408005878384976779455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13158741584144425675923413 308408005878384976779455)
                  ·
                    rfl

theorem cell23_5405602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_5405602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405602 prefixEnd_5405602 := by exact prefixLift 5405602
  have htrace : WordTrace (prefixWord ++ tailWord_5405602) baseStart_5405602 baseEnd_5405602 := by
    simpa [prefixWord, tailWord_5405602, baseEnd_5405602] using wordTrace_append hprefix tailTrace_5405602
  have hstable : (prefixWord ++ tailWord_5405602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405602).length < 2 ^ (prefixWord ++ tailWord_5405602).sum := by decide
  have hdescent : baseEnd_5405602 < baseStart_5405602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405613 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5405613 : Nat := 118140960795 + 5405613 * 2 ^ 59
def prefixEnd_5405613 : Nat := 4983230072969 + 3 ^ 40 * 5405613 * 2
def baseEnd_5405613 : Nat := 2775677701192664247977545

theorem tailTrace_5405613 : CollatzResearch.WordTrace tailWord_5405613 prefixEnd_5405613 2775677701192664247977545 := by
  unfold tailWord_5405613
  simp only [CollatzResearch.WordTrace]
  refine ⟨197158903365394781045389493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131439268910263187363592995 197158903365394781045389493)
  ·
    refine ⟨18483647190505760723005265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197158903365394781045389493 18483647190505760723005265)
    ·
      refine ⟨13862735392879320542253949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18483647190505760723005265 13862735392879320542253949)
      ·
        refine ⟨5198525772329745203345231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13862735392879320542253949 5198525772329745203345231)
        ·
          refine ⟨7797788658494617805017847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198525772329745203345231 7797788658494617805017847)
          ·
            refine ⟨11696682987741926707526771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797788658494617805017847 11696682987741926707526771)
            ·
              refine ⟨17545024481612890061290157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11696682987741926707526771 17545024481612890061290157)
              ·
                refine ⟨6579384180604833772983809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17545024481612890061290157 6579384180604833772983809)
                ·
                  refine ⟨4934538135453625329737857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6579384180604833772983809 4934538135453625329737857)
                  ·
                    refine ⟨3700903601590218997303393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934538135453625329737857 3700903601590218997303393)
                    ·
                      refine ⟨2775677701192664247977545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700903601590218997303393 2775677701192664247977545)
                      ·
                        rfl

theorem cell23_5405613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5405613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405613 prefixEnd_5405613 := by exact prefixLift 5405613
  have htrace : WordTrace (prefixWord ++ tailWord_5405613) baseStart_5405613 baseEnd_5405613 := by
    simpa [prefixWord, tailWord_5405613, baseEnd_5405613] using wordTrace_append hprefix tailTrace_5405613
  have hstable : (prefixWord ++ tailWord_5405613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405613).length < 2 ^ (prefixWord ++ tailWord_5405613).sum := by decide
  have hdescent : baseEnd_5405613 < baseStart_5405613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405635 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 6, 2]
def baseStart_5405635 : Nat := 118140960795 + 5405635 * 2 ^ 59
def prefixEnd_5405635 : Nat := 4983230072969 + 3 ^ 40 * 5405635 * 2
def baseEnd_5405635 : Nat := 2775688997767063161902443

theorem tailTrace_5405635 : CollatzResearch.WordTrace tailWord_5405635 prefixEnd_5405635 2775688997767063161902443 := by
  unfold tailWord_5405635
  simp only [CollatzResearch.WordTrace]
  refine ⟨197159705771315078802690359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131439803847543385868460239 197159705771315078802690359)
  ·
    refine ⟨295739558656972618204035539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197159705771315078802690359 295739558656972618204035539)
    ·
      refine ⟨443609337985458927306053309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295739558656972618204035539 443609337985458927306053309)
      ·
        refine ⟨166353501744547097739769991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443609337985458927306053309 166353501744547097739769991)
        ·
          refine ⟨249530252616820646609654987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166353501744547097739769991 249530252616820646609654987)
          ·
            refine ⟨374295378925230969914482481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249530252616820646609654987 374295378925230969914482481)
            ·
              refine ⟨280721534193923227435861861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374295378925230969914482481 280721534193923227435861861)
              ·
                refine ⟨52635287661360605144224099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280721534193923227435861861 52635287661360605144224099)
                ·
                  refine ⟨78952931492040907716336149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52635287661360605144224099 78952931492040907716336149)
                  ·
                    refine ⟨3700918663689417549203257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78952931492040907716336149 3700918663689417549203257)
                    ·
                      refine ⟨2775688997767063161902443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3700918663689417549203257 2775688997767063161902443)
                      ·
                        rfl

theorem cell23_5405635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_5405635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405635 prefixEnd_5405635 := by exact prefixLift 5405635
  have htrace : WordTrace (prefixWord ++ tailWord_5405635) baseStart_5405635 baseEnd_5405635 := by
    simpa [prefixWord, tailWord_5405635, baseEnd_5405635] using wordTrace_append hprefix tailTrace_5405635
  have hstable : (prefixWord ++ tailWord_5405635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405635).length < 2 ^ (prefixWord ++ tailWord_5405635).sum := by decide
  have hdescent : baseEnd_5405635 < baseStart_5405635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405648 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6]
def baseStart_5405648 : Nat := 118140960795 + 5405648 * 2 ^ 59
def prefixEnd_5405648 : Nat := 4983230072969 + 3 ^ 40 * 5405648 * 2
def baseEnd_5405648 : Nat := 2775695673015571611039883

theorem tailTrace_5405648 : CollatzResearch.WordTrace tailWord_5405648 prefixEnd_5405648 2775695673015571611039883 := by
  unfold tailWord_5405648
  simp only [CollatzResearch.WordTrace]
  refine ⟨98580089960133991011456799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131440119946845321348609065 98580089960133991011456799)
  ·
    refine ⟨147870134940200986517185199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98580089960133991011456799 147870134940200986517185199)
    ·
      refine ⟨221805202410301479775777799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147870134940200986517185199 221805202410301479775777799)
      ·
        refine ⟨332707803615452219663666699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221805202410301479775777799 332707803615452219663666699)
        ·
          refine ⟨499061705423178329495500049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332707803615452219663666699 499061705423178329495500049)
          ·
            refine ⟨374296279067383747121625037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499061705423178329495500049 374296279067383747121625037)
            ·
              refine ⟨140361104650268905170609389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374296279067383747121625037 140361104650268905170609389)
              ·
                refine ⟨52635414243850839438978521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140361104650268905170609389 52635414243850839438978521)
                ·
                  refine ⟨39476560682888129579233891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52635414243850839438978521 39476560682888129579233891)
                  ·
                    refine ⟨59214841024332194368850837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39476560682888129579233891 59214841024332194368850837)
                    ·
                      refine ⟨2775695673015571611039883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59214841024332194368850837 2775695673015571611039883)
                      ·
                        rfl

theorem cell23_5405648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_5405648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405648 prefixEnd_5405648 := by exact prefixLift 5405648
  have htrace : WordTrace (prefixWord ++ tailWord_5405648) baseStart_5405648 baseEnd_5405648 := by
    simpa [prefixWord, tailWord_5405648, baseEnd_5405648] using wordTrace_append hprefix tailTrace_5405648
  have hstable : (prefixWord ++ tailWord_5405648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405648).length < 2 ^ (prefixWord ++ tailWord_5405648).sum := by decide
  have hdescent : baseEnd_5405648 < baseStart_5405648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405652 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5405652 : Nat := 118140960795 + 5405652 * 2 ^ 59
def prefixEnd_5405652 : Nat := 4983230072969 + 3 ^ 40 * 5405652 * 2
def baseEnd_5405652 : Nat := 2775697726938189595389865

theorem tailTrace_5405652 : CollatzResearch.WordTrace tailWord_5405652 prefixEnd_5405652 2775697726938189595389865 := by
  unfold tailWord_5405652
  simp only [CollatzResearch.WordTrace]
  refine ⟨98580162906126745353029605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131440217208168993804039473 98580162906126745353029605)
  ·
    refine ⟨18483780544898764753693051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98580162906126745353029605 18483780544898764753693051)
    ·
      refine ⟨27725670817348147130539577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18483780544898764753693051 27725670817348147130539577)
      ·
        refine ⟨20794253113011110347904683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27725670817348147130539577 20794253113011110347904683)
        ·
          refine ⟨31191379669516665521857025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20794253113011110347904683 31191379669516665521857025)
          ·
            refine ⟨23393534752137499141392769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31191379669516665521857025 23393534752137499141392769)
            ·
              refine ⟨17545151064103124356044577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23393534752137499141392769 17545151064103124356044577)
              ·
                refine ⟨13158863298077343267033433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17545151064103124356044577 13158863298077343267033433)
                ·
                  refine ⟨9869147473558007450275075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13158863298077343267033433 9869147473558007450275075)
                  ·
                    refine ⟨14803721210337011175412613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9869147473558007450275075 14803721210337011175412613)
                    ·
                      refine ⟨2775697726938189595389865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14803721210337011175412613 2775697726938189595389865)
                      ·
                        rfl

theorem cell23_5405652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5405652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405652 prefixEnd_5405652 := by exact prefixLift 5405652
  have htrace : WordTrace (prefixWord ++ tailWord_5405652) baseStart_5405652 baseEnd_5405652 := by
    simpa [prefixWord, tailWord_5405652, baseEnd_5405652] using wordTrace_append hprefix tailTrace_5405652
  have hstable : (prefixWord ++ tailWord_5405652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405652).length < 2 ^ (prefixWord ++ tailWord_5405652).sum := by decide
  have hdescent : baseEnd_5405652 < baseStart_5405652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405655 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_5405655 : Nat := 118140960795 + 5405655 * 2 ^ 59
def prefixEnd_5405655 : Nat := 4983230072969 + 3 ^ 40 * 5405655 * 2
def baseEnd_5405655 : Nat := 2775699267380153083652351

theorem tailTrace_5405655 : CollatzResearch.WordTrace tailWord_5405655 prefixEnd_5405655 2775699267380153083652351 := by
  unfold tailWord_5405655
  simp only [CollatzResearch.WordTrace]
  refine ⟨197160435231242622218418419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131440290154161748145612279 197160435231242622218418419)
  ·
    refine ⟨295740652846863933327627629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197160435231242622218418419 295740652846863933327627629)
    ·
      refine ⟨110902744817573974997860361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295740652846863933327627629 110902744817573974997860361)
      ·
        refine ⟨83177058613180481248395271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110902744817573974997860361 83177058613180481248395271)
        ·
          refine ⟨124765587919770721872592907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83177058613180481248395271 124765587919770721872592907)
          ·
            refine ⟨187148381879656082808889361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124765587919770721872592907 187148381879656082808889361)
            ·
              refine ⟨140361286409742062106667021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187148381879656082808889361 140361286409742062106667021)
              ·
                refine ⟨52635482403653273290000133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140361286409742062106667021 52635482403653273290000133)
                ·
                  refine ⟨9869152950684988741875025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52635482403653273290000133 9869152950684988741875025)
                  ·
                    refine ⟨7401864713013741556406269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9869152950684988741875025 7401864713013741556406269)
                    ·
                      refine ⟨2775699267380153083652351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401864713013741556406269 2775699267380153083652351)
                      ·
                        rfl

theorem cell23_5405655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_5405655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405655 prefixEnd_5405655 := by exact prefixLift 5405655
  have htrace : WordTrace (prefixWord ++ tailWord_5405655) baseStart_5405655 baseEnd_5405655 := by
    simpa [prefixWord, tailWord_5405655, baseEnd_5405655] using wordTrace_append hprefix tailTrace_5405655
  have hstable : (prefixWord ++ tailWord_5405655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405655).length < 2 ^ (prefixWord ++ tailWord_5405655).sum := by decide
  have hdescent : baseEnd_5405655 < baseStart_5405655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405719 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5405719 : Nat := 118140960795 + 5405719 * 2 ^ 59
def prefixEnd_5405719 : Nat := 4983230072969 + 3 ^ 40 * 5405719 * 2
def baseEnd_5405719 : Nat := 2775732130142040833252057

theorem tailTrace_5405719 : CollatzResearch.WordTrace tailWord_5405719 prefixEnd_5405719 2775732130142040833252057 := by
  unfold tailWord_5405719
  simp only [CollatzResearch.WordTrace]
  refine ⟨197162769503010761148748211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131441846335340507432498807 197162769503010761148748211)
  ·
    refine ⟨295744154254516141723122317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197162769503010761148748211 295744154254516141723122317)
    ·
      refine ⟨110904057845443553146170869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295744154254516141723122317 110904057845443553146170869)
      ·
        refine ⟨10397255423010333107453519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110904057845443553146170869 10397255423010333107453519)
        ·
          refine ⟨15595883134515499661180279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10397255423010333107453519 15595883134515499661180279)
          ·
            refine ⟨23393824701773249491770419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15595883134515499661180279 23393824701773249491770419)
            ·
              refine ⟨35090737052659874237655629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23393824701773249491770419 35090737052659874237655629)
              ·
                refine ⟨13159026394747452839120861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35090737052659874237655629 13159026394747452839120861)
                ·
                  refine ⟨4934634898030294814670323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13159026394747452839120861 4934634898030294814670323)
                  ·
                    refine ⟨7401952347045442222005485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4934634898030294814670323 7401952347045442222005485)
                    ·
                      refine ⟨2775732130142040833252057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401952347045442222005485 2775732130142040833252057)
                      ·
                        rfl

theorem cell23_5405719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5405719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405719 prefixEnd_5405719 := by exact prefixLift 5405719
  have htrace : WordTrace (prefixWord ++ tailWord_5405719) baseStart_5405719 baseEnd_5405719 := by
    simpa [prefixWord, tailWord_5405719, baseEnd_5405719] using wordTrace_append hprefix tailTrace_5405719
  have hstable : (prefixWord ++ tailWord_5405719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405719).length < 2 ^ (prefixWord ++ tailWord_5405719).sum := by decide
  have hdescent : baseEnd_5405719 < baseStart_5405719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405745 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_5405745 : Nat := 118140960795 + 5405745 * 2 ^ 59
def prefixEnd_5405745 : Nat := 4983230072969 + 3 ^ 40 * 5405745 * 2
def baseEnd_5405745 : Nat := 2775745480639057731526937

theorem tailTrace_5405745 : CollatzResearch.WordTrace tailWord_5405745 prefixEnd_5405745 2775745480639057731526937 := by
  unfold tailWord_5405745
  simp only [CollatzResearch.WordTrace]
  refine ⟨197163717800916567589194689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131442478533944378392796459 197163717800916567589194689)
  ·
    refine ⟨147872788350687425691896017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197163717800916567589194689 147872788350687425691896017)
    ·
      refine ⟨110904591263015569268922013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147872788350687425691896017 110904591263015569268922013)
      ·
        refine ⟨41589221723630838475845755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110904591263015569268922013 41589221723630838475845755)
        ·
          refine ⟨62383832585446257713768633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41589221723630838475845755 62383832585446257713768633)
          ·
            refine ⟨46787874439084693285326475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62383832585446257713768633 46787874439084693285326475)
            ·
              refine ⟨70181811658627039927989713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46787874439084693285326475 70181811658627039927989713)
              ·
                refine ⟨52636358743970279945992285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70181811658627039927989713 52636358743970279945992285)
                ·
                  refine ⟨19738634528988854979747107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52636358743970279945992285 19738634528988854979747107)
                  ·
                    refine ⟨29607951793483282469620661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19738634528988854979747107 29607951793483282469620661)
                    ·
                      refine ⟨2775745480639057731526937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29607951793483282469620661 2775745480639057731526937)
                      ·
                        rfl

theorem cell23_5405745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_5405745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405745 prefixEnd_5405745 := by exact prefixLift 5405745
  have htrace : WordTrace (prefixWord ++ tailWord_5405745) baseStart_5405745 baseEnd_5405745 := by
    simpa [prefixWord, tailWord_5405745, baseEnd_5405745] using wordTrace_append hprefix tailTrace_5405745
  have hstable : (prefixWord ++ tailWord_5405745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405745).length < 2 ^ (prefixWord ++ tailWord_5405745).sum := by decide
  have hdescent : baseEnd_5405745 < baseStart_5405745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405752 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_5405752 : Nat := 118140960795 + 5405752 * 2 ^ 59
def prefixEnd_5405752 : Nat := 4983230072969 + 3 ^ 40 * 5405752 * 2
def baseEnd_5405752 : Nat := 925249691667879734713135

theorem tailTrace_5405752 : CollatzResearch.WordTrace tailWord_5405752 prefixEnd_5405752 925249691667879734713135 := by
  unfold tailWord_5405752
  simp only [CollatzResearch.WordTrace]
  refine ⟨98581986555945603892349755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131442648741260805189799673 98581986555945603892349755)
  ·
    refine ⟨147872979833918405838524633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98581986555945603892349755 147872979833918405838524633)
    ·
      refine ⟨110904734875438804378893475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147872979833918405838524633 110904734875438804378893475)
      ·
        refine ⟨166357102313158206568340213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110904734875438804378893475 166357102313158206568340213)
        ·
          refine ⟨15595978341858581865781895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166357102313158206568340213 15595978341858581865781895)
          ·
            refine ⟨23393967512787872798672843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15595978341858581865781895 23393967512787872798672843)
            ·
              refine ⟨35090951269181809198009265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23393967512787872798672843 35090951269181809198009265)
              ·
                refine ⟨26318213451886356898506949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35090951269181809198009265 26318213451886356898506949)
                ·
                  refine ⟨4934665022228691918470053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26318213451886356898506949 4934665022228691918470053)
                  ·
                    refine ⟨925249691667879734713135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4934665022228691918470053 925249691667879734713135)
                    ·
                      rfl

theorem cell23_5405752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_5405752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405752 prefixEnd_5405752 := by exact prefixLift 5405752
  have htrace : WordTrace (prefixWord ++ tailWord_5405752) baseStart_5405752 baseEnd_5405752 := by
    simpa [prefixWord, tailWord_5405752, baseEnd_5405752] using wordTrace_append hprefix tailTrace_5405752
  have hstable : (prefixWord ++ tailWord_5405752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405752).length < 2 ^ (prefixWord ++ tailWord_5405752).sum := by decide
  have hdescent : baseEnd_5405752 < baseStart_5405752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405753 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5405753 : Nat := 118140960795 + 5405753 * 2 ^ 59
def prefixEnd_5405753 : Nat := 4983230072969 + 3 ^ 40 * 5405753 * 2
def baseEnd_5405753 : Nat := 2775749588484293700226901

theorem tailTrace_5405753 : CollatzResearch.WordTrace tailWord_5405753 prefixEnd_5405753 2775749588484293700226901 := by
  unfold tailWord_5405753
  simp only [CollatzResearch.WordTrace]
  refine ⟨197164009584887584955485913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131442673056591723303657275 197164009584887584955485913)
  ·
    refine ⟨147873007188665688716614435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197164009584887584955485913 147873007188665688716614435)
    ·
      refine ⟨221809510782998533074921653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147873007188665688716614435 221809510782998533074921653)
      ·
        refine ⟨20794641635906112475773905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221809510782998533074921653 20794641635906112475773905)
        ·
          refine ⟨15595981226929584356830429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20794641635906112475773905 15595981226929584356830429)
          ·
            refine ⟨5848492960098594133811411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15595981226929584356830429 5848492960098594133811411)
            ·
              refine ⟨8772739440147891200717117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848492960098594133811411 8772739440147891200717117)
              ·
                refine ⟨3289777290055459200268919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8772739440147891200717117 3289777290055459200268919)
                ·
                  refine ⟨4934665935083188800403379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289777290055459200268919 4934665935083188800403379)
                  ·
                    refine ⟨7401998902624783200605069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4934665935083188800403379 7401998902624783200605069)
                    ·
                      refine ⟨2775749588484293700226901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7401998902624783200605069 2775749588484293700226901)
                      ·
                        rfl

theorem cell23_5405753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5405753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405753 prefixEnd_5405753 := by exact prefixLift 5405753
  have htrace : WordTrace (prefixWord ++ tailWord_5405753) baseStart_5405753 baseEnd_5405753 := by
    simpa [prefixWord, tailWord_5405753, baseEnd_5405753] using wordTrace_append hprefix tailTrace_5405753
  have hstable : (prefixWord ++ tailWord_5405753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405753).length < 2 ^ (prefixWord ++ tailWord_5405753).sum := by decide
  have hdescent : baseEnd_5405753 < baseStart_5405753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405775 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3]
def baseStart_5405775 : Nat := 118140960795 + 5405775 * 2 ^ 59
def prefixEnd_5405775 : Nat := 4983230072969 + 3 ^ 40 * 5405775 * 2
def baseEnd_5405775 : Nat := 2775760885058692614151799

theorem tailTrace_5405775 : CollatzResearch.WordTrace tailWord_5405775 prefixEnd_5405775 2775760885058692614151799 := by
  unfold tailWord_5405775
  simp only [CollatzResearch.WordTrace]
  refine ⟨197164811990807882712786779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131443207993871921808524519 197164811990807882712786779)
  ·
    refine ⟨295747217986211824069180169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197164811990807882712786779 295747217986211824069180169)
    ·
      refine ⟨221810413489658868051885127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295747217986211824069180169 221810413489658868051885127)
      ·
        refine ⟨332715620234488302077827691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221810413489658868051885127 332715620234488302077827691)
        ·
          refine ⟨499073430351732453116741537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332715620234488302077827691 499073430351732453116741537)
          ·
            refine ⟨374305072763799339837556153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499073430351732453116741537 374305072763799339837556153)
            ·
              refine ⟨280728804572849504878167115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374305072763799339837556153 280728804572849504878167115)
              ·
                refine ⟨421093206859274257317250673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280728804572849504878167115 421093206859274257317250673)
                ·
                  refine ⟨315819905144455692987938005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421093206859274257317250673 315819905144455692987938005)
                  ·
                    refine ⟨7402029026823180304404797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 315819905144455692987938005 7402029026823180304404797)
                    ·
                      refine ⟨2775760885058692614151799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402029026823180304404797 2775760885058692614151799)
                      ·
                        rfl

theorem cell23_5405775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_5405775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405775 prefixEnd_5405775 := by exact prefixLift 5405775
  have htrace : WordTrace (prefixWord ++ tailWord_5405775) baseStart_5405775 baseEnd_5405775 := by
    simpa [prefixWord, tailWord_5405775, baseEnd_5405775] using wordTrace_append hprefix tailTrace_5405775
  have hstable : (prefixWord ++ tailWord_5405775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405775).length < 2 ^ (prefixWord ++ tailWord_5405775).sum := by decide
  have hdescent : baseEnd_5405775 < baseStart_5405775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405776 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 1, 2, 2]
def baseStart_5405776 : Nat := 118140960795 + 5405776 * 2 ^ 59
def prefixEnd_5405776 : Nat := 4983230072969 + 3 ^ 40 * 5405776 * 2
def baseEnd_5405776 : Nat := 2775761398539347110239295

theorem tailTrace_5405776 : CollatzResearch.WordTrace tailWord_5405776 prefixEnd_5405776 2775761398539347110239295 := by
  unfold tailWord_5405776
  simp only [CollatzResearch.WordTrace]
  refine ⟨98582424231902129941786591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131443232309202839922382121 98582424231902129941786591)
  ·
    refine ⟨147873636347853194912679887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98582424231902129941786591 147873636347853194912679887)
    ·
      refine ⟨221810454521779792369019831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147873636347853194912679887 221810454521779792369019831)
      ·
        refine ⟨332715681782669688553529747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221810454521779792369019831 332715681782669688553529747)
        ·
          refine ⟨499073522674004532830294621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332715681782669688553529747 499073522674004532830294621)
          ·
            refine ⟨187152571002751699811360483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499073522674004532830294621 187152571002751699811360483)
            ·
              refine ⟨280728856504127549717040725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187152571002751699811360483 280728856504127549717040725)
              ·
                refine ⟨3289791287157744723246571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 280728856504127549717040725 3289791287157744723246571)
                ·
                  refine ⟨4934686930736617084869857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289791287157744723246571 4934686930736617084869857)
                  ·
                    refine ⟨3701015198052462813652393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934686930736617084869857 3701015198052462813652393)
                    ·
                      refine ⟨2775761398539347110239295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701015198052462813652393 2775761398539347110239295)
                      ·
                        rfl

theorem cell23_5405776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 2, 2].length) (baseStart_5405776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405776 prefixEnd_5405776 := by exact prefixLift 5405776
  have htrace : WordTrace (prefixWord ++ tailWord_5405776) baseStart_5405776 baseEnd_5405776 := by
    simpa [prefixWord, tailWord_5405776, baseEnd_5405776] using wordTrace_append hprefix tailTrace_5405776
  have hstable : (prefixWord ++ tailWord_5405776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405776).length < 2 ^ (prefixWord ++ tailWord_5405776).sum := by decide
  have hdescent : baseEnd_5405776 < baseStart_5405776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405792 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3]
def baseStart_5405792 : Nat := 118140960795 + 5405792 * 2 ^ 59
def prefixEnd_5405792 : Nat := 4983230072969 + 3 ^ 40 * 5405792 * 2
def baseEnd_5405792 : Nat := 2775769614229819047639221

theorem tailTrace_5405792 : CollatzResearch.WordTrace tailWord_5405792 prefixEnd_5405792 2775769614229819047639221 := by
  unfold tailWord_5405792
  simp only [CollatzResearch.WordTrace]
  refine ⟨98582716015873147308077815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131443621354497529744103753 98582716015873147308077815)
  ·
    refine ⟨147874074023809720962116723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98582716015873147308077815 147874074023809720962116723)
    ·
      refine ⟨221811111035714581443175085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147874074023809720962116723 221811111035714581443175085)
      ·
        refine ⟨83179166638392968041190657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221811111035714581443175085 83179166638392968041190657)
        ·
          refine ⟨62384374978794726030892993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83179166638392968041190657 62384374978794726030892993)
          ·
            refine ⟨46788281234096044523169745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62384374978794726030892993 46788281234096044523169745)
            ·
              refine ⟨35091210925572033392377309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46788281234096044523169745 35091210925572033392377309)
              ·
                refine ⟨13159204097089512522141491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35091210925572033392377309 13159204097089512522141491)
                ·
                  refine ⟨19738806145634268783212237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13159204097089512522141491 19738806145634268783212237)
                  ·
                    refine ⟨7402052304612850793704589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19738806145634268783212237 7402052304612850793704589)
                    ·
                      refine ⟨2775769614229819047639221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402052304612850793704589 2775769614229819047639221)
                      ·
                        rfl

theorem cell23_5405792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_5405792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405792 prefixEnd_5405792 := by exact prefixLift 5405792
  have htrace : WordTrace (prefixWord ++ tailWord_5405792) baseStart_5405792 baseEnd_5405792 := by
    simpa [prefixWord, tailWord_5405792, baseEnd_5405792] using wordTrace_append hprefix tailTrace_5405792
  have hstable : (prefixWord ++ tailWord_5405792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405792).length < 2 ^ (prefixWord ++ tailWord_5405792).sum := by decide
  have hdescent : baseEnd_5405792 < baseStart_5405792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405813 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5405813 : Nat := 118140960795 + 5405813 * 2 ^ 59
def prefixEnd_5405813 : Nat := 4983230072969 + 3 ^ 40 * 5405813 * 2
def baseEnd_5405813 : Nat := 2775780397323563465476625

theorem tailTrace_5405813 : CollatzResearch.WordTrace tailWord_5405813 prefixEnd_5405813 2775780397323563465476625 := by
  unfold tailWord_5405813
  simp only [CollatzResearch.WordTrace]
  refine ⟨197166197964670215202670093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131444131976446810135113395 197166197964670215202670093)
  ·
    refine ⟨73937324236751330701001285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197166197964670215202670093 73937324236751330701001285)
    ·
      refine ⟨13863248294390874506437741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73937324236751330701001285 13863248294390874506437741)
      ·
        refine ⟨5198718110396577939914153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13863248294390874506437741 5198718110396577939914153)
        ·
          refine ⟨3899038582797433454935615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198718110396577939914153 3899038582797433454935615)
          ·
            refine ⟨5848557874196150182403423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899038582797433454935615 5848557874196150182403423)
            ·
              refine ⟨8772836811294225273605135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848557874196150182403423 8772836811294225273605135)
              ·
                refine ⟨13159255216941337910407703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772836811294225273605135 13159255216941337910407703)
                ·
                  refine ⟨19738882825412006865611555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13159255216941337910407703 19738882825412006865611555)
                  ·
                    refine ⟨29608324238118010298417333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19738882825412006865611555 29608324238118010298417333)
                    ·
                      refine ⟨2775780397323563465476625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29608324238118010298417333 2775780397323563465476625)
                      ·
                        rfl

theorem cell23_5405813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5405813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405813 prefixEnd_5405813 := by exact prefixLift 5405813
  have htrace : WordTrace (prefixWord ++ tailWord_5405813) baseStart_5405813 baseEnd_5405813 := by
    simpa [prefixWord, tailWord_5405813, baseEnd_5405813] using wordTrace_append hprefix tailTrace_5405813
  have hstable : (prefixWord ++ tailWord_5405813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405813).length < 2 ^ (prefixWord ++ tailWord_5405813).sum := by decide
  have hdescent : baseEnd_5405813 < baseStart_5405813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405819 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 1, 3, 2]
def baseStart_5405819 : Nat := 118140960795 + 5405819 * 2 ^ 59
def prefixEnd_5405819 : Nat := 4983230072969 + 3 ^ 40 * 5405819 * 2
def baseEnd_5405819 : Nat := 2775783478207490442001597

theorem tailTrace_5405819 : CollatzResearch.WordTrace tailWord_5405819 prefixEnd_5405819 2775783478207490442001597 := by
  unfold tailWord_5405819
  simp only [CollatzResearch.WordTrace]
  refine ⟨197166416802648478227388511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131444277868432318818259007 197166416802648478227388511)
  ·
    refine ⟨295749625203972717341082767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197166416802648478227388511 295749625203972717341082767)
    ·
      refine ⟨443624437805959076011624151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295749625203972717341082767 443624437805959076011624151)
      ·
        refine ⟨665436656708938614017436227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443624437805959076011624151 665436656708938614017436227)
        ·
          refine ⟨998154985063407921026154341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665436656708938614017436227 998154985063407921026154341)
          ·
            refine ⟨187154059699388985192403939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 998154985063407921026154341 187154059699388985192403939)
            ·
              refine ⟨280731089549083477788605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187154059699388985192403939 280731089549083477788605909)
              ·
                refine ⟨6579634911306644010670451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280731089549083477788605909 6579634911306644010670451)
                ·
                  refine ⟨9869452366959966016005677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579634911306644010670451 9869452366959966016005677)
                  ·
                    refine ⟨3701044637609987256002129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9869452366959966016005677 3701044637609987256002129)
                    ·
                      refine ⟨2775783478207490442001597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701044637609987256002129 2775783478207490442001597)
                      ·
                        rfl

theorem cell23_5405819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 3, 2].length) (baseStart_5405819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405819 prefixEnd_5405819 := by exact prefixLift 5405819
  have htrace : WordTrace (prefixWord ++ tailWord_5405819) baseStart_5405819 baseEnd_5405819 := by
    simpa [prefixWord, tailWord_5405819, baseEnd_5405819] using wordTrace_append hprefix tailTrace_5405819
  have hstable : (prefixWord ++ tailWord_5405819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405819).length < 2 ^ (prefixWord ++ tailWord_5405819).sum := by decide
  have hdescent : baseEnd_5405819 < baseStart_5405819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405835 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_5405835 : Nat := 118140960795 + 5405835 * 2 ^ 59
def prefixEnd_5405835 : Nat := 4983230072969 + 3 ^ 40 * 5405835 * 2
def baseEnd_5405835 : Nat := 2775791693897962379401523

theorem tailTrace_5405835 : CollatzResearch.WordTrace tailWord_5405835 prefixEnd_5405835 2775791693897962379401523 := by
  unfold tailWord_5405835
  simp only [CollatzResearch.WordTrace]
  refine ⟨197167000370590512959970959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131444666913727008639980639 197167000370590512959970959)
  ·
    refine ⟨295750500555885769439956439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197167000370590512959970959 295750500555885769439956439)
    ·
      refine ⟨443625750833828654159934659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295750500555885769439956439 443625750833828654159934659)
      ·
        refine ⟨665438626250742981239901989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443625750833828654159934659 665438626250742981239901989)
        ·
          refine ⟨124769742422014308982481623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 665438626250742981239901989 124769742422014308982481623)
          ·
            refine ⟨187154613633021463473722435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124769742422014308982481623 187154613633021463473722435)
            ·
              refine ⟨280731920449532195210583653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187154613633021463473722435 280731920449532195210583653)
              ·
                refine ⟨52637235084287286601984435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280731920449532195210583653 52637235084287286601984435)
                ·
                  refine ⟨78955852626430929902976653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52637235084287286601984435 78955852626430929902976653)
                  ·
                    refine ⟨29608444734911598713616245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78955852626430929902976653 29608444734911598713616245)
                    ·
                      refine ⟨2775791693897962379401523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29608444734911598713616245 2775791693897962379401523)
                      ·
                        rfl

theorem cell23_5405835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_5405835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405835 prefixEnd_5405835 := by exact prefixLift 5405835
  have htrace : WordTrace (prefixWord ++ tailWord_5405835) baseStart_5405835 baseEnd_5405835 := by
    simpa [prefixWord, tailWord_5405835, baseEnd_5405835] using wordTrace_append hprefix tailTrace_5405835
  have hstable : (prefixWord ++ tailWord_5405835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405835).length < 2 ^ (prefixWord ++ tailWord_5405835).sum := by decide
  have hdescent : baseEnd_5405835 < baseStart_5405835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405842 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5405842 : Nat := 118140960795 + 5405842 * 2 ^ 59
def prefixEnd_5405842 : Nat := 4983230072969 + 3 ^ 40 * 5405842 * 2
def baseEnd_5405842 : Nat := 925265096087514617337997

theorem tailTrace_5405842 : CollatzResearch.WordTrace tailWord_5405842 prefixEnd_5405842 925265096087514617337997 := by
  unfold tailWord_5405842
  simp only [CollatzResearch.WordTrace]
  refine ⟨49291813920391288288868945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131444837121043435436983853 49291813920391288288868945)
  ·
    refine ⟨36968860440293466216651709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49291813920391288288868945 36968860440293466216651709)
    ·
      refine ⟨13863322665110049831244391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36968860440293466216651709 13863322665110049831244391)
      ·
        refine ⟨20794983997665074746866587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13863322665110049831244391 20794983997665074746866587)
        ·
          refine ⟨31192475996497612120299881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20794983997665074746866587 31192475996497612120299881)
          ·
            refine ⟨23394356997373209090224911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31192475996497612120299881 23394356997373209090224911)
            ·
              refine ⟨35091535496059813635337367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23394356997373209090224911 35091535496059813635337367)
              ·
                refine ⟨52637303244089720453006051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35091535496059813635337367 52637303244089720453006051)
                ·
                  refine ⟨78955954866134580679509077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52637303244089720453006051 78955954866134580679509077)
                  ·
                    refine ⟨925265096087514617337997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78955954866134580679509077 925265096087514617337997)
                    ·
                      rfl

theorem cell23_5405842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5405842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405842 prefixEnd_5405842 := by exact prefixLift 5405842
  have htrace : WordTrace (prefixWord ++ tailWord_5405842) baseStart_5405842 baseEnd_5405842 := by
    simpa [prefixWord, tailWord_5405842, baseEnd_5405842] using wordTrace_append hprefix tailTrace_5405842
  have hstable : (prefixWord ++ tailWord_5405842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405842).length < 2 ^ (prefixWord ++ tailWord_5405842).sum := by decide
  have hdescent : baseEnd_5405842 < baseStart_5405842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405849 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 8, 2, 2]
def baseStart_5405849 : Nat := 118140960795 + 5405849 * 2 ^ 59
def prefixEnd_5405849 : Nat := 4983230072969 + 3 ^ 40 * 5405849 * 2
def baseEnd_5405849 : Nat := 2775798882627125324626459

theorem tailTrace_5405849 : CollatzResearch.WordTrace tailWord_5405849 prefixEnd_5405849 2775798882627125324626459 := by
  unfold tailWord_5405849
  simp only [CollatzResearch.WordTrace]
  refine ⟨197167510992539793350980601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131445007328359862233987067 197167510992539793350980601)
  ·
    refine ⟨147875633244404845013235451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197167510992539793350980601 147875633244404845013235451)
    ·
      refine ⟨221813449866607267519853177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147875633244404845013235451 221813449866607267519853177)
      ·
        refine ⟨166360087399955450639889883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221813449866607267519853177 166360087399955450639889883)
        ·
          refine ⟨249540131099933175959834825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166360087399955450639889883 249540131099933175959834825)
          ·
            refine ⟨187155098324949881969876119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249540131099933175959834825 187155098324949881969876119)
            ·
              refine ⟨280732647487424822954814179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187155098324949881969876119 280732647487424822954814179)
              ·
                refine ⟨421098971231137234432221269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280732647487424822954814179 421098971231137234432221269)
                ·
                  refine ⟨4934753569114889466002593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 421098971231137234432221269 4934753569114889466002593)
                  ·
                    refine ⟨3701065176836167099501945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934753569114889466002593 3701065176836167099501945)
                    ·
                      refine ⟨2775798882627125324626459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701065176836167099501945 2775798882627125324626459)
                      ·
                        rfl

theorem cell23_5405849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_5405849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405849 prefixEnd_5405849 := by exact prefixLift 5405849
  have htrace : WordTrace (prefixWord ++ tailWord_5405849) baseStart_5405849 baseEnd_5405849 := by
    simpa [prefixWord, tailWord_5405849, baseEnd_5405849] using wordTrace_append hprefix tailTrace_5405849
  have hstable : (prefixWord ++ tailWord_5405849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405849).length < 2 ^ (prefixWord ++ tailWord_5405849).sum := by decide
  have hdescent : baseEnd_5405849 < baseStart_5405849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405889 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 7]
def baseStart_5405889 : Nat := 118140960795 + 5405889 * 2 ^ 59
def prefixEnd_5405889 : Nat := 4983230072969 + 3 ^ 40 * 5405889 * 2
def baseEnd_5405889 : Nat := 308424380205922796458475

theorem tailTrace_5405889 : CollatzResearch.WordTrace tailWord_5405889 prefixEnd_5405889 308424380205922796458475 := by
  unfold tailWord_5405889
  simp only [CollatzResearch.WordTrace]
  refine ⟨197168969912394880182436721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131445979941596586788291147 197168969912394880182436721)
  ·
    refine ⟨147876727434296160136827541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197168969912394880182436721 147876727434296160136827541)
    ·
      refine ⟨6931721598482632506413791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147876727434296160136827541 6931721598482632506413791)
      ·
        refine ⟨10397582397723948759620687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6931721598482632506413791 10397582397723948759620687)
        ·
          refine ⟨15596373596585923139431031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10397582397723948759620687 15596373596585923139431031)
          ·
            refine ⟨23394560394878884709146547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15596373596585923139431031 23394560394878884709146547)
            ·
              refine ⟨35091840592318327063719821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23394560394878884709146547 35091840592318327063719821)
              ·
                refine ⟨13159440222119372648894933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35091840592318327063719821 13159440222119372648894933)
                ·
                  refine ⟨308424380205922796458475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13159440222119372648894933 308424380205922796458475)
                  ·
                    rfl

theorem cell23_5405889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_5405889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405889 prefixEnd_5405889 := by exact prefixLift 5405889
  have htrace : WordTrace (prefixWord ++ tailWord_5405889) baseStart_5405889 baseEnd_5405889 := by
    simpa [prefixWord, tailWord_5405889, baseEnd_5405889] using wordTrace_append hprefix tailTrace_5405889
  have hstable : (prefixWord ++ tailWord_5405889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405889).length < 2 ^ (prefixWord ++ tailWord_5405889).sum := by decide
  have hdescent : baseEnd_5405889 < baseStart_5405889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405894 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5405894 : Nat := 118140960795 + 5405894 * 2 ^ 59
def prefixEnd_5405894 : Nat := 4983230072969 + 3 ^ 40 * 5405894 * 2
def baseEnd_5405894 : Nat := 2775821989256577648563753

theorem tailTrace_5405894 : CollatzResearch.WordTrace tailWord_5405894 prefixEnd_5405894 2775821989256577648563753 := by
  unfold tailWord_5405894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161536008668023938636523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131446101518251177357579157 6161536008668023938636523)
  ·
    refine ⟨9242304013002035907954785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6161536008668023938636523 9242304013002035907954785)
    ·
      refine ⟨6931728009751526930966089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9242304013002035907954785 6931728009751526930966089)
      ·
        refine ⟨5198796007313645198224567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6931728009751526930966089 5198796007313645198224567)
        ·
          refine ⟨7798194010970467797336851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198796007313645198224567 7798194010970467797336851)
          ·
            refine ⟨11697291016455701696005277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7798194010970467797336851 11697291016455701696005277)
            ·
              refine ⟨4386484131170888136001979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11697291016455701696005277 4386484131170888136001979)
              ·
                refine ⟨6579726196756332204002969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386484131170888136001979 6579726196756332204002969)
                ·
                  refine ⟨4934794647567249153002227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6579726196756332204002969 4934794647567249153002227)
                  ·
                    refine ⟨7402191971350873729503341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4934794647567249153002227 7402191971350873729503341)
                    ·
                      refine ⟨2775821989256577648563753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402191971350873729503341 2775821989256577648563753)
                      ·
                        rfl

theorem cell23_5405894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5405894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405894 prefixEnd_5405894 := by exact prefixLift 5405894
  have htrace : WordTrace (prefixWord ++ tailWord_5405894) baseStart_5405894 baseEnd_5405894 := by
    simpa [prefixWord, tailWord_5405894, baseEnd_5405894] using wordTrace_append hprefix tailTrace_5405894
  have hstable : (prefixWord ++ tailWord_5405894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405894).length < 2 ^ (prefixWord ++ tailWord_5405894).sum := by decide
  have hdescent : baseEnd_5405894 < baseStart_5405894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405939 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4]
def baseStart_5405939 : Nat := 118140960795 + 5405939 * 2 ^ 59
def prefixEnd_5405939 : Nat := 4983230072969 + 3 ^ 40 * 5405939 * 2
def baseEnd_5405939 : Nat := 2775845095886029972501045

theorem tailTrace_5405939 : CollatzResearch.WordTrace tailWord_5405939 prefixEnd_5405939 2775845095886029972501045 := by
  unfold tailWord_5405939
  simp only [CollatzResearch.WordTrace]
  refine ⟨197170793562213738721756871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131447195708142492481171247 197170793562213738721756871)
  ·
    refine ⟨295756190343320608082635307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197170793562213738721756871 295756190343320608082635307)
    ·
      refine ⟨443634285514980912123952961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295756190343320608082635307 443634285514980912123952961)
      ·
        refine ⟨332725714136235684092964721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443634285514980912123952961 332725714136235684092964721)
        ·
          refine ⟨249544285602176763069723541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332725714136235684092964721 249544285602176763069723541)
          ·
            refine ⟨11697388387602035768893291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249544285602176763069723541 11697388387602035768893291)
            ·
              refine ⟨17546082581403053653339937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11697388387602035768893291 17546082581403053653339937)
              ·
                refine ⟨13159561936052290240004953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17546082581403053653339937 13159561936052290240004953)
                ·
                  refine ⟨9869671452039217680003715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13159561936052290240004953 9869671452039217680003715)
                  ·
                    refine ⟨14804507178058826520005573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9869671452039217680003715 14804507178058826520005573)
                    ·
                      refine ⟨2775845095886029972501045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14804507178058826520005573 2775845095886029972501045)
                      ·
                        rfl

theorem cell23_5405939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_5405939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405939 prefixEnd_5405939 := by exact prefixLift 5405939
  have htrace : WordTrace (prefixWord ++ tailWord_5405939) baseStart_5405939 baseEnd_5405939 := by
    simpa [prefixWord, tailWord_5405939, baseEnd_5405939] using wordTrace_append hprefix tailTrace_5405939
  have hstable : (prefixWord ++ tailWord_5405939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405939).length < 2 ^ (prefixWord ++ tailWord_5405939).sum := by decide
  have hdescent : baseEnd_5405939 < baseStart_5405939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405940 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5405940 : Nat := 118140960795 + 5405940 * 2 ^ 59
def prefixEnd_5405940 : Nat := 4983230072969 + 3 ^ 40 * 5405940 * 2
def baseEnd_5405940 : Nat := 308427289929631607620949

theorem tailTrace_5405940 : CollatzResearch.WordTrace tailWord_5405940 prefixEnd_5405940 308427289929631607620949 := by
  unfold tailWord_5405940
  simp only [CollatzResearch.WordTrace]
  refine ⟨98585415017605057946271637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131447220023473410595028849 98585415017605057946271637)
  ·
    refine ⟨4621191328950237091231483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98585415017605057946271637 4621191328950237091231483)
    ·
      refine ⟨6931786993425355636847225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621191328950237091231483 6931786993425355636847225)
      ·
        refine ⟨5198840245069016727635419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6931786993425355636847225 5198840245069016727635419)
        ·
          refine ⟨7798260367603525091453129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198840245069016727635419 7798260367603525091453129)
          ·
            refine ⟨5848695275702643818589847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7798260367603525091453129 5848695275702643818589847)
            ·
              refine ⟨8773042913553965727884771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848695275702643818589847 8773042913553965727884771)
              ·
                refine ⟨13159564370330948591827157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773042913553965727884771 13159564370330948591827157)
                ·
                  refine ⟨308427289929631607620949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13159564370330948591827157 308427289929631607620949)
                  ·
                    rfl

theorem cell23_5405940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5405940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405940 prefixEnd_5405940 := by exact prefixLift 5405940
  have htrace : WordTrace (prefixWord ++ tailWord_5405940) baseStart_5405940 baseEnd_5405940 := by
    simpa [prefixWord, tailWord_5405940, baseEnd_5405940] using wordTrace_append hprefix tailTrace_5405940
  have hstable : (prefixWord ++ tailWord_5405940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405940).length < 2 ^ (prefixWord ++ tailWord_5405940).sum := by decide
  have hdescent : baseEnd_5405940 < baseStart_5405940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405976 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5405976 : Nat := 118140960795 + 5405976 * 2 ^ 59
def prefixEnd_5405976 : Nat := 4983230072969 + 3 ^ 40 * 5405976 * 2
def baseEnd_5405976 : Nat := 2775864094670246327738375

theorem tailTrace_5405976 : CollatzResearch.WordTrace tailWord_5405976 prefixEnd_5405976 2775864094670246327738375 := by
  unfold tailWord_5405976
  simp only [CollatzResearch.WordTrace]
  refine ⟨98586071531539847020426891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131448095375386462693902521 98586071531539847020426891)
  ·
    refine ⟨147879107297309770530640337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98586071531539847020426891 147879107297309770530640337)
    ·
      refine ⟨110909330472982327897980253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147879107297309770530640337 110909330472982327897980253)
      ·
        refine ⟨41590998927368372961742595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110909330472982327897980253 41590998927368372961742595)
        ·
          refine ⟨62386498391052559442613893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41590998927368372961742595 62386498391052559442613893)
          ·
            refine ⟨11697468448322354895490105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62386498391052559442613893 11697468448322354895490105)
            ·
              refine ⟨8773101336241766171617579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11697468448322354895490105 8773101336241766171617579)
              ·
                refine ⟨13159652004362649257426369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773101336241766171617579 13159652004362649257426369)
                ·
                  refine ⟨9869739003271986943069777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13159652004362649257426369 9869739003271986943069777)
                  ·
                    refine ⟨7402304252453990207302333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9869739003271986943069777 7402304252453990207302333)
                    ·
                      refine ⟨2775864094670246327738375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402304252453990207302333 2775864094670246327738375)
                      ·
                        rfl

theorem cell23_5405976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5405976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405976 prefixEnd_5405976 := by exact prefixLift 5405976
  have htrace : WordTrace (prefixWord ++ tailWord_5405976) baseStart_5405976 baseEnd_5405976 := by
    simpa [prefixWord, tailWord_5405976, baseEnd_5405976] using wordTrace_append hprefix tailTrace_5405976
  have hstable : (prefixWord ++ tailWord_5405976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405976).length < 2 ^ (prefixWord ++ tailWord_5405976).sum := by decide
  have hdescent : baseEnd_5405976 < baseStart_5405976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5405999 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 5, 2]
def baseStart_5405999 : Nat := 118140960795 + 5405999 * 2 ^ 59
def prefixEnd_5405999 : Nat := 4983230072969 + 3 ^ 40 * 5405999 * 2
def baseEnd_5405999 : Nat := 2775875904725299737750769

theorem tailTrace_5405999 : CollatzResearch.WordTrace tailWord_5405999 prefixEnd_5405999 2775875904725299737750769 := by
  unfold tailWord_5405999
  simp only [CollatzResearch.WordTrace]
  refine ⟨197172981941996368968941051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131448654627997579312627367 197172981941996368968941051)
  ·
    refine ⟨295759472912994553453411577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197172981941996368968941051 295759472912994553453411577)
    ·
      refine ⟨221819604684745915090058683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295759472912994553453411577 221819604684745915090058683)
      ·
        refine ⟨332729407027118872635088025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221819604684745915090058683 332729407027118872635088025)
        ·
          refine ⟨249547055270339154476316019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332729407027118872635088025 249547055270339154476316019)
          ·
            refine ⟨374320582905508731714474029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249547055270339154476316019 374320582905508731714474029)
            ·
              refine ⟨140370218589565774392927761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374320582905508731714474029 140370218589565774392927761)
              ·
                refine ⟨105277663942174330794695821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140370218589565774392927761 105277663942174330794695821)
                ·
                  refine ⟨39479123978315374048010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105277663942174330794695821 39479123978315374048010933)
                  ·
                    refine ⟨3701167872967066317001025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39479123978315374048010933 3701167872967066317001025)
                    ·
                      refine ⟨2775875904725299737750769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701167872967066317001025 2775875904725299737750769)
                      ·
                        rfl

theorem cell23_5405999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 5, 2].length) (baseStart_5405999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5405999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5405999 prefixEnd_5405999 := by exact prefixLift 5405999
  have htrace : WordTrace (prefixWord ++ tailWord_5405999) baseStart_5405999 baseEnd_5405999 := by
    simpa [prefixWord, tailWord_5405999, baseEnd_5405999] using wordTrace_append hprefix tailTrace_5405999
  have hstable : (prefixWord ++ tailWord_5405999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5405999).length < 2 ^ (prefixWord ++ tailWord_5405999).sum := by decide
  have hdescent : baseEnd_5405999 < baseStart_5405999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5405999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406039 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 1, 6]
def baseStart_5406039 : Nat := 118140960795 + 5406039 * 2 ^ 59
def prefixEnd_5406039 : Nat := 4983230072969 + 3 ^ 40 * 5406039 * 2
def baseEnd_5406039 : Nat := 925298814650493193750195

theorem tailTrace_5406039 : CollatzResearch.WordTrace tailWord_5406039 prefixEnd_5406039 925298814650493193750195 := by
  unfold tailWord_5406039
  simp only [CollatzResearch.WordTrace]
  refine ⟨197174440861851455800397171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131449627241234303866931447 197174440861851455800397171)
  ·
    refine ⟨295761661292777183700595757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197174440861851455800397171 295761661292777183700595757)
    ·
      refine ⟨110910622984791443887723409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295761661292777183700595757 110910622984791443887723409)
      ·
        refine ⟨83182967238593582915792557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110910622984791443887723409 83182967238593582915792557)
        ·
          refine ⟨31193612714472593593422209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83182967238593582915792557 31193612714472593593422209)
          ·
            refine ⟨23395209535854445195066657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31193612714472593593422209 23395209535854445195066657)
            ·
              refine ⟨17546407151890833896299993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23395209535854445195066657 17546407151890833896299993)
              ·
                refine ⟨13159805363918125422224995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17546407151890833896299993 13159805363918125422224995)
                ·
                  refine ⟨19739708045877188133337493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13159805363918125422224995 19739708045877188133337493)
                  ·
                    refine ⟨925298814650493193750195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19739708045877188133337493 925298814650493193750195)
                    ·
                      rfl

theorem cell23_5406039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_5406039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406039 prefixEnd_5406039 := by exact prefixLift 5406039
  have htrace : WordTrace (prefixWord ++ tailWord_5406039) baseStart_5406039 baseEnd_5406039 := by
    simpa [prefixWord, tailWord_5406039, baseEnd_5406039] using wordTrace_append hprefix tailTrace_5406039
  have hstable : (prefixWord ++ tailWord_5406039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406039).length < 2 ^ (prefixWord ++ tailWord_5406039).sum := by decide
  have hdescent : baseEnd_5406039 < baseStart_5406039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406063 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 3, 2, 2]
def baseStart_5406063 : Nat := 118140960795 + 5406063 * 2 ^ 59
def prefixEnd_5406063 : Nat := 4983230072969 + 3 ^ 40 * 5406063 * 2
def baseEnd_5406063 : Nat := 2775908767487187487350475

theorem tailTrace_5406063 : CollatzResearch.WordTrace tailWord_5406063 prefixEnd_5406063 2775908767487187487350475 := by
  unfold tailWord_5406063
  simp only [CollatzResearch.WordTrace]
  refine ⟨197175316213764507899270843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131450210809176338599513895 197175316213764507899270843)
  ·
    refine ⟨295762974320646761848906265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197175316213764507899270843 295762974320646761848906265)
    ·
      refine ⟨221822230740485071386679699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295762974320646761848906265 221822230740485071386679699)
      ·
        refine ⟨332733346110727607080019549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221822230740485071386679699 332733346110727607080019549)
        ·
          refine ⟨124775004791522852655007331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332733346110727607080019549 124775004791522852655007331)
          ·
            refine ⟨187162507187284278982510997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124775004791522852655007331 187162507187284278982510997)
            ·
              refine ⟨8773242524403950577305203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187162507187284278982510997 8773242524403950577305203)
              ·
                refine ⟨13159863786605925865957805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773242524403950577305203 13159863786605925865957805)
                ·
                  refine ⟨4934948919977222199734177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13159863786605925865957805 4934948919977222199734177)
                  ·
                    refine ⟨3701211689982916649800633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934948919977222199734177 3701211689982916649800633)
                    ·
                      refine ⟨2775908767487187487350475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701211689982916649800633 2775908767487187487350475)
                      ·
                        rfl

theorem cell23_5406063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2, 2].length) (baseStart_5406063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406063 prefixEnd_5406063 := by exact prefixLift 5406063
  have htrace : WordTrace (prefixWord ++ tailWord_5406063) baseStart_5406063 baseEnd_5406063 := by
    simpa [prefixWord, tailWord_5406063, baseEnd_5406063] using wordTrace_append hprefix tailTrace_5406063
  have hstable : (prefixWord ++ tailWord_5406063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406063).length < 2 ^ (prefixWord ++ tailWord_5406063).sum := by decide
  have hdescent : baseEnd_5406063 < baseStart_5406063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406083 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 3]
def baseStart_5406083 : Nat := 118140960795 + 5406083 * 2 ^ 59
def prefixEnd_5406083 : Nat := 4983230072969 + 3 ^ 40 * 5406083 * 2
def baseEnd_5406083 : Nat := 2775919037100277409100383

theorem tailTrace_5406083 : CollatzResearch.WordTrace tailWord_5406083 prefixEnd_5406083 2775919037100277409100383 := by
  unfold tailWord_5406083
  simp only [CollatzResearch.WordTrace]
  refine ⟨197176045673692051314998903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131450697115794700876665935 197176045673692051314998903)
  ·
    refine ⟨295764068510538076972498355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197176045673692051314998903 295764068510538076972498355)
    ·
      refine ⟨443646102765807115458747533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295764068510538076972498355 443646102765807115458747533)
      ·
        refine ⟨166367288537177668297030325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443646102765807115458747533 166367288537177668297030325)
        ·
          refine ⟨15596933300360406402846593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166367288537177668297030325 15596933300360406402846593)
          ·
            refine ⟨11697699975270304802134945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15596933300360406402846593 11697699975270304802134945)
            ·
              refine ⟨8773274981452728601601209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11697699975270304802134945 8773274981452728601601209)
              ·
                refine ⟨6579956236089546451200907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8773274981452728601601209 6579956236089546451200907)
                ·
                  refine ⟨9869934354134319676801361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579956236089546451200907 9869934354134319676801361)
                  ·
                    refine ⟨7402450765600739757601021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9869934354134319676801361 7402450765600739757601021)
                    ·
                      refine ⟨2775919037100277409100383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402450765600739757601021 2775919037100277409100383)
                      ·
                        rfl

theorem cell23_5406083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_5406083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406083 prefixEnd_5406083 := by exact prefixLift 5406083
  have htrace : WordTrace (prefixWord ++ tailWord_5406083) baseStart_5406083 baseEnd_5406083 := by
    simpa [prefixWord, tailWord_5406083, baseEnd_5406083] using wordTrace_append hprefix tailTrace_5406083
  have hstable : (prefixWord ++ tailWord_5406083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406083).length < 2 ^ (prefixWord ++ tailWord_5406083).sum := by decide
  have hdescent : baseEnd_5406083 < baseStart_5406083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406114 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_5406114 : Nat := 118140960795 + 5406114 * 2 ^ 59
def prefixEnd_5406114 : Nat := 4983230072969 + 3 ^ 40 * 5406114 * 2
def baseEnd_5406114 : Nat := 2775934955000566787812741

theorem tailTrace_5406114 : CollatzResearch.WordTrace tailWord_5406114 prefixEnd_5406114 2775934955000566787812741 := by
  unfold tailWord_5406114
  simp only [CollatzResearch.WordTrace]
  refine ⟨49294294084144935902344349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131451450891053162406251597 49294294084144935902344349)
  ·
    refine ⟨18485360281554350963379131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49294294084144935902344349 18485360281554350963379131)
    ·
      refine ⟨27728040422331526445068697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18485360281554350963379131 27728040422331526445068697)
      ·
        refine ⟨20796030316748644833801523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27728040422331526445068697 20796030316748644833801523)
        ·
          refine ⟨31194045475122967250702285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20796030316748644833801523 31194045475122967250702285)
          ·
            refine ⟨11697767053171112719013357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31194045475122967250702285 11697767053171112719013357)
            ·
              refine ⟨4386662644939167269630009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11697767053171112719013357 4386662644939167269630009)
              ·
                refine ⟨3289996983704375452222507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386662644939167269630009 3289996983704375452222507)
                ·
                  refine ⟨4934995475556563178333761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289996983704375452222507 4934995475556563178333761)
                  ·
                    refine ⟨3701246606667422383750321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4934995475556563178333761 3701246606667422383750321)
                    ·
                      refine ⟨2775934955000566787812741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701246606667422383750321 2775934955000566787812741)
                      ·
                        rfl

theorem cell23_5406114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_5406114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406114 prefixEnd_5406114 := by exact prefixLift 5406114
  have htrace : WordTrace (prefixWord ++ tailWord_5406114) baseStart_5406114 baseEnd_5406114 := by
    simpa [prefixWord, tailWord_5406114, baseEnd_5406114] using wordTrace_append hprefix tailTrace_5406114
  have hstable : (prefixWord ++ tailWord_5406114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406114).length < 2 ^ (prefixWord ++ tailWord_5406114).sum := by decide
  have hdescent : baseEnd_5406114 < baseStart_5406114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406129 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_5406129 : Nat := 118140960795 + 5406129 * 2 ^ 59
def prefixEnd_5406129 : Nat := 4983230072969 + 3 ^ 40 * 5406129 * 2
def baseEnd_5406129 : Nat := 925314219070128076375057

theorem tailTrace_5406129 : CollatzResearch.WordTrace tailWord_5406129 prefixEnd_5406129 925314219070128076375057 := by
  unfold tailWord_5406129
  simp only [CollatzResearch.WordTrace]
  refine ⟨197177723431525401171173441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131451815621016934114115627 197177723431525401171173441)
  ·
    refine ⟨147883292573644050878380081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197177723431525401171173441 147883292573644050878380081)
    ·
      refine ⟨110912469430233038158785061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147883292573644050878380081 110912469430233038158785061)
      ·
        refine ⟨20796088018168694654772199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110912469430233038158785061 20796088018168694654772199)
        ·
          refine ⟨31194132027253041982158299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20796088018168694654772199 31194132027253041982158299)
          ·
            refine ⟨46791198040879562973237449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31194132027253041982158299 46791198040879562973237449)
            ·
              refine ⟨35093398530659672229928087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46791198040879562973237449 35093398530659672229928087)
              ·
                refine ⟨52640097795989508344892131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35093398530659672229928087 52640097795989508344892131)
                ·
                  refine ⟨78960146693984262517338197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52640097795989508344892131 78960146693984262517338197)
                  ·
                    refine ⟨925314219070128076375057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78960146693984262517338197 925314219070128076375057)
                    ·
                      rfl

theorem cell23_5406129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_5406129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406129 prefixEnd_5406129 := by exact prefixLift 5406129
  have htrace : WordTrace (prefixWord ++ tailWord_5406129) baseStart_5406129 baseEnd_5406129 := by
    simpa [prefixWord, tailWord_5406129, baseEnd_5406129] using wordTrace_append hprefix tailTrace_5406129
  have hstable : (prefixWord ++ tailWord_5406129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406129).length < 2 ^ (prefixWord ++ tailWord_5406129).sum := by decide
  have hdescent : baseEnd_5406129 < baseStart_5406129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406140 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_5406140 : Nat := 118140960795 + 5406140 * 2 ^ 59
def prefixEnd_5406140 : Nat := 4983230072969 + 3 ^ 40 * 5406140 * 2
def baseEnd_5406140 : Nat := 2775948305497583686087621

theorem tailTrace_5406140 : CollatzResearch.WordTrace tailWord_5406140 prefixEnd_5406140 2775948305497583686087621 := by
  unfold tailWord_5406140
  simp only [CollatzResearch.WordTrace]
  refine ⟨98589062317242775024911937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131452083089657033366549249 98589062317242775024911937)
  ·
    refine ⟨73941796737932081268683953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98589062317242775024911937 73941796737932081268683953)
    ·
      refine ⟨55456347553449060951512965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73941796737932081268683953 55456347553449060951512965)
      ·
        refine ⟨10398065166271698928408681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55456347553449060951512965 10398065166271698928408681)
        ·
          refine ⟨7798548874703774196306511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10398065166271698928408681 7798548874703774196306511)
          ·
            refine ⟨11697823312055661294459767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7798548874703774196306511 11697823312055661294459767)
            ·
              refine ⟨17546734968083491941689651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11697823312055661294459767 17546734968083491941689651)
              ·
                refine ⟨26320102452125237912534477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17546734968083491941689651 26320102452125237912534477)
                ·
                  refine ⟨9870038419546964217200429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26320102452125237912534477 9870038419546964217200429)
                  ·
                    refine ⟨3701264407330111581450161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9870038419546964217200429 3701264407330111581450161)
                    ·
                      refine ⟨2775948305497583686087621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701264407330111581450161 2775948305497583686087621)
                      ·
                        rfl

theorem cell23_5406140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_5406140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406140 prefixEnd_5406140 := by exact prefixLift 5406140
  have htrace : WordTrace (prefixWord ++ tailWord_5406140) baseStart_5406140 baseEnd_5406140 := by
    simpa [prefixWord, tailWord_5406140, baseEnd_5406140] using wordTrace_append hprefix tailTrace_5406140
  have hstable : (prefixWord ++ tailWord_5406140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406140).length < 2 ^ (prefixWord ++ tailWord_5406140).sum := by decide
  have hdescent : baseEnd_5406140 < baseStart_5406140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406156 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5406156 : Nat := 118140960795 + 5406156 * 2 ^ 59
def prefixEnd_5406156 : Nat := 4983230072969 + 3 ^ 40 * 5406156 * 2
def baseEnd_5406156 : Nat := 2775956521188055623487547

theorem tailTrace_5406156 : CollatzResearch.WordTrace tailWord_5406156 prefixEnd_5406156 2775956521188055623487547 := by
  unfold tailWord_5406156
  simp only [CollatzResearch.WordTrace]
  refine ⟨98589354101213792391203161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131452472134951723188270881 98589354101213792391203161)
  ·
    refine ⟨73942015575910344293402371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98589354101213792391203161 73942015575910344293402371)
    ·
      refine ⟨110913023363865516440103557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73942015575910344293402371 110913023363865516440103557)
      ·
        refine ⟨20796191880724784332519417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110913023363865516440103557 20796191880724784332519417)
        ·
          refine ⟨15597143910543588249389563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20796191880724784332519417 15597143910543588249389563)
          ·
            refine ⟨23395715865815382374084345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15597143910543588249389563 23395715865815382374084345)
            ·
              refine ⟨17546786899361536780563259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23395715865815382374084345 17546786899361536780563259)
              ·
                refine ⟨26320180349042305170844889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17546786899361536780563259 26320180349042305170844889)
                ·
                  refine ⟨19740135261781728878133667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26320180349042305170844889 19740135261781728878133667)
                  ·
                    refine ⟨29610202892672593317200501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19740135261781728878133667 29610202892672593317200501)
                    ·
                      refine ⟨2775956521188055623487547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29610202892672593317200501 2775956521188055623487547)
                      ·
                        rfl

theorem cell23_5406156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5406156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406156 prefixEnd_5406156 := by exact prefixLift 5406156
  have htrace : WordTrace (prefixWord ++ tailWord_5406156) baseStart_5406156 baseEnd_5406156 := by
    simpa [prefixWord, tailWord_5406156, baseEnd_5406156] using wordTrace_append hprefix tailTrace_5406156
  have hstable : (prefixWord ++ tailWord_5406156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406156).length < 2 ^ (prefixWord ++ tailWord_5406156).sum := by decide
  have hdescent : baseEnd_5406156 < baseStart_5406156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406170 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_5406170 : Nat := 118140960795 + 5406170 * 2 ^ 59
def prefixEnd_5406170 : Nat := 4983230072969 + 3 ^ 40 * 5406170 * 2
def baseEnd_5406170 : Nat := 2775963709917218568712483

theorem tailTrace_5406170 : CollatzResearch.WordTrace tailWord_5406170 prefixEnd_5406170 2775963709917218568712483 := by
  unfold tailWord_5406170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49294804706094216293353991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131452812549584576782277309 49294804706094216293353991)
  ·
    refine ⟨73942207059141324440030987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49294804706094216293353991 73942207059141324440030987)
    ·
      refine ⟨110913310588711986660046481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73942207059141324440030987 110913310588711986660046481)
      ·
        refine ⟨83184982941533989995034861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110913310588711986660046481 83184982941533989995034861)
        ·
          refine ⟨31194368603075246248138073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83184982941533989995034861 31194368603075246248138073)
          ·
            refine ⟨23395776452306434686103555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31194368603075246248138073 23395776452306434686103555)
            ·
              refine ⟨35093664678459652029155333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23395776452306434686103555 35093664678459652029155333)
              ·
                refine ⟨6580062127211184755466625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35093664678459652029155333 6580062127211184755466625)
                ·
                  refine ⟨4935046595408388566599969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6580062127211184755466625 4935046595408388566599969)
                  ·
                    refine ⟨3701284946556291424949977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935046595408388566599969 3701284946556291424949977)
                    ·
                      refine ⟨2775963709917218568712483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701284946556291424949977 2775963709917218568712483)
                      ·
                        rfl

theorem cell23_5406170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_5406170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406170 prefixEnd_5406170 := by exact prefixLift 5406170
  have htrace : WordTrace (prefixWord ++ tailWord_5406170) baseStart_5406170 baseEnd_5406170 := by
    simpa [prefixWord, tailWord_5406170, baseEnd_5406170] using wordTrace_append hprefix tailTrace_5406170
  have hstable : (prefixWord ++ tailWord_5406170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406170).length < 2 ^ (prefixWord ++ tailWord_5406170).sum := by decide
  have hdescent : baseEnd_5406170 < baseStart_5406170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406199 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_5406199 : Nat := 118140960795 + 5406199 * 2 ^ 59
def prefixEnd_5406199 : Nat := 4983230072969 + 3 ^ 40 * 5406199 * 2
def baseEnd_5406199 : Nat := 2775978600856198955249849

theorem tailTrace_5406199 : CollatzResearch.WordTrace tailWord_5406199 prefixEnd_5406199 2775978600856198955249849 := by
  unfold tailWord_5406199
  simp only [CollatzResearch.WordTrace]
  refine ⟨197180276541271803126221651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131453517694181202084147767 197180276541271803126221651)
  ·
    refine ⟨295770414811907704689332477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197180276541271803126221651 295770414811907704689332477)
    ·
      refine ⟨110913905554465389258499679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295770414811907704689332477 110913905554465389258499679)
      ·
        refine ⟨166370858331698083887749519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110913905554465389258499679 166370858331698083887749519)
        ·
          refine ⟨249556287497547125831624279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166370858331698083887749519 249556287497547125831624279)
          ·
            refine ⟨374334431246320688747436419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249556287497547125831624279 374334431246320688747436419)
            ·
              refine ⟨561501646869481033121154629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374334431246320688747436419 561501646869481033121154629)
              ·
                refine ⟨105281558788027693710216493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561501646869481033121154629 105281558788027693710216493)
                ·
                  refine ⟨39480584545510385141331185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105281558788027693710216493 39480584545510385141331185)
                  ·
                    refine ⟨29610438409132788855998389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39480584545510385141331185 29610438409132788855998389)
                    ·
                      refine ⟨2775978600856198955249849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29610438409132788855998389 2775978600856198955249849)
                      ·
                        rfl

theorem cell23_5406199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_5406199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406199 prefixEnd_5406199 := by exact prefixLift 5406199
  have htrace : WordTrace (prefixWord ++ tailWord_5406199) baseStart_5406199 baseEnd_5406199 := by
    simpa [prefixWord, tailWord_5406199, baseEnd_5406199] using wordTrace_append hprefix tailTrace_5406199
  have hstable : (prefixWord ++ tailWord_5406199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406199).length < 2 ^ (prefixWord ++ tailWord_5406199).sum := by decide
  have hdescent : baseEnd_5406199 < baseStart_5406199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406210 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_5406210 : Nat := 118140960795 + 5406210 * 2 ^ 59
def prefixEnd_5406210 : Nat := 4983230072969 + 3 ^ 40 * 5406210 * 2
def baseEnd_5406210 : Nat := 308442694349266490245811

theorem tailTrace_5406210 : CollatzResearch.WordTrace tailWord_5406210 prefixEnd_5406210 308442694349266490245811 := by
  unfold tailWord_5406210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49295169436057988001218021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131453785162821301336581389 49295169436057988001218021)
  ·
    refine ⟨9242844269260872750228379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49295169436057988001218021 9242844269260872750228379)
    ·
      refine ⟨13864266403891309125342569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9242844269260872750228379 13864266403891309125342569)
      ·
        refine ⟨10398199802918481844006927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13864266403891309125342569 10398199802918481844006927)
        ·
          refine ⟨15597299704377722766010391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10398199802918481844006927 15597299704377722766010391)
          ·
            refine ⟨23395949556566584149015587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15597299704377722766010391 23395949556566584149015587)
            ·
              refine ⟨35093924334849876223523381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23395949556566584149015587 35093924334849876223523381)
              ·
                refine ⟨3290055406392175895955317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35093924334849876223523381 3290055406392175895955317)
                ·
                  refine ⟨308442694349266490245811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290055406392175895955317 308442694349266490245811)
                  ·
                    rfl

theorem cell23_5406210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_5406210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406210 prefixEnd_5406210 := by exact prefixLift 5406210
  have htrace : WordTrace (prefixWord ++ tailWord_5406210) baseStart_5406210 baseEnd_5406210 := by
    simpa [prefixWord, tailWord_5406210, baseEnd_5406210] using wordTrace_append hprefix tailTrace_5406210
  have hstable : (prefixWord ++ tailWord_5406210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406210).length < 2 ^ (prefixWord ++ tailWord_5406210).sum := by decide
  have hdescent : baseEnd_5406210 < baseStart_5406210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406238 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5406238 : Nat := 118140960795 + 5406238 * 2 ^ 59
def prefixEnd_5406238 : Nat := 4983230072969 + 3 ^ 40 * 5406238 * 2
def baseEnd_5406238 : Nat := 2775998626601724302662171

theorem tailTrace_5406238 : CollatzResearch.WordTrace tailWord_5406238 prefixEnd_5406238 2775998626601724302662171 := by
  unfold tailWord_5406238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24647712373516314098361421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131454465992087008524594245 24647712373516314098361421)
  ·
    refine ⟨9242892140068617786885533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24647712373516314098361421 9242892140068617786885533)
    ·
      refine ⟨3466084552525731670082075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9242892140068617786885533 3466084552525731670082075)
      ·
        refine ⟨5199126828788597505123113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466084552525731670082075 5199126828788597505123113)
        ·
          refine ⟨3899345121591448128842335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199126828788597505123113 3899345121591448128842335)
          ·
            refine ⟨5849017682387172193263503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899345121591448128842335 5849017682387172193263503)
            ·
              refine ⟨8773526523580758289895255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849017682387172193263503 8773526523580758289895255)
              ·
                refine ⟨13160289785371137434842883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773526523580758289895255 13160289785371137434842883)
                ·
                  refine ⟨19740434678056706152264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13160289785371137434842883 19740434678056706152264325)
                  ·
                    refine ⟨3701331502135632403549561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19740434678056706152264325 3701331502135632403549561)
                    ·
                      refine ⟨2775998626601724302662171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701331502135632403549561 2775998626601724302662171)
                      ·
                        rfl

theorem cell23_5406238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5406238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406238 prefixEnd_5406238 := by exact prefixLift 5406238
  have htrace : WordTrace (prefixWord ++ tailWord_5406238) baseStart_5406238 baseEnd_5406238 := by
    simpa [prefixWord, tailWord_5406238, baseEnd_5406238] using wordTrace_append hprefix tailTrace_5406238
  have hstable : (prefixWord ++ tailWord_5406238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406238).length < 2 ^ (prefixWord ++ tailWord_5406238).sum := by decide
  have hdescent : baseEnd_5406238 < baseStart_5406238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406296 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 3, 5]
def baseStart_5406296 : Nat := 118140960795 + 5406296 * 2 ^ 59
def prefixEnd_5406296 : Nat := 4983230072969 + 3 ^ 40 * 5406296 * 2
def baseEnd_5406296 : Nat := 925342802826561691912301

theorem tailTrace_5406296 : CollatzResearch.WordTrace tailWord_5406296 prefixEnd_5406296 925342802826561691912301 := by
  unfold tailWord_5406296
  simp only [CollatzResearch.WordTrace]
  refine ⟨98591907210960194346251371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131455876281280259128335161 98591907210960194346251371)
  ·
    refine ⟨147887860816440291519377057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98591907210960194346251371 147887860816440291519377057)
    ·
      refine ⟨110915895612330218639532793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147887860816440291519377057 110915895612330218639532793)
      ·
        refine ⟨83186921709247663979649595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110915895612330218639532793 83186921709247663979649595)
        ·
          refine ⟨124780382563871495969474393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83186921709247663979649595 124780382563871495969474393)
          ·
            refine ⟨93585286922903621977105795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124780382563871495969474393 93585286922903621977105795)
            ·
              refine ⟨140377930384355432965658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93585286922903621977105795 140377930384355432965658693)
              ·
                refine ⟨26320861947066643681061005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140377930384355432965658693 26320861947066643681061005)
                ·
                  refine ⟨9870323230149991380397877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26320861947066643681061005 9870323230149991380397877)
                  ·
                    refine ⟨925342802826561691912301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9870323230149991380397877 925342802826561691912301)
                    ·
                      rfl

theorem cell23_5406296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_5406296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406296 prefixEnd_5406296 := by exact prefixLift 5406296
  have htrace : WordTrace (prefixWord ++ tailWord_5406296) baseStart_5406296 baseEnd_5406296 := by
    simpa [prefixWord, tailWord_5406296, baseEnd_5406296] using wordTrace_append hprefix tailTrace_5406296
  have hstable : (prefixWord ++ tailWord_5406296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406296).length < 2 ^ (prefixWord ++ tailWord_5406296).sum := by decide
  have hdescent : baseEnd_5406296 < baseStart_5406296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406300 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 6]
def baseStart_5406300 : Nat := 118140960795 + 5406300 * 2 ^ 59
def prefixEnd_5406300 : Nat := 4983230072969 + 3 ^ 40 * 5406300 * 2
def baseEnd_5406300 : Nat := 308447829155811451120765

theorem tailTrace_5406300 : CollatzResearch.WordTrace tailWord_5406300 prefixEnd_5406300 308447829155811451120765 := by
  unfold tailWord_5406300
  simp only [CollatzResearch.WordTrace]
  refine ⟨98591980156952948687824177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131455973542603931583765569 98591980156952948687824177)
  ·
    refine ⟨73943985117714711515868133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98591980156952948687824177 73943985117714711515868133)
    ·
      refine ⟨13864497209571508409225275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73943985117714711515868133 13864497209571508409225275)
      ·
        refine ⟨20796745814357262613837913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13864497209571508409225275 20796745814357262613837913)
        ·
          refine ⟨15597559360767946960378435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20796745814357262613837913 15597559360767946960378435)
          ·
            refine ⟨23396339041151920440567653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15597559360767946960378435 23396339041151920440567653)
            ·
              refine ⟨4386813570215985082606435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23396339041151920440567653 4386813570215985082606435)
              ·
                refine ⟨6580220355323977623909653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386813570215985082606435 6580220355323977623909653)
                ·
                  refine ⟨308447829155811451120765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6580220355323977623909653 308447829155811451120765)
                  ·
                    rfl

theorem cell23_5406300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_5406300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406300 prefixEnd_5406300 := by exact prefixLift 5406300
  have htrace : WordTrace (prefixWord ++ tailWord_5406300) baseStart_5406300 baseEnd_5406300 := by
    simpa [prefixWord, tailWord_5406300, baseEnd_5406300] using wordTrace_append hprefix tailTrace_5406300
  have hstable : (prefixWord ++ tailWord_5406300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406300).length < 2 ^ (prefixWord ++ tailWord_5406300).sum := by decide
  have hdescent : baseEnd_5406300 < baseStart_5406300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406313 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_5406313 : Nat := 118140960795 + 5406313 * 2 ^ 59
def prefixEnd_5406313 : Nat := 4983230072969 + 3 ^ 40 * 5406313 * 2
def baseEnd_5406313 : Nat := 925345712550270503074775

theorem tailTrace_5406313 : CollatzResearch.WordTrace tailWord_5406313 prefixEnd_5406313 925345712550270503074775 := by
  unfold tailWord_5406313
  simp only [CollatzResearch.WordTrace]
  refine ⟨197184434462858800595871593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131456289641905867063914395 197184434462858800595871593)
  ·
    refine ⟨147888325847144100446903695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197184434462858800595871593 147888325847144100446903695)
    ·
      refine ⟨221832488770716150670355543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147888325847144100446903695 221832488770716150670355543)
      ·
        refine ⟨332748733156074226005533315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221832488770716150670355543 332748733156074226005533315)
        ·
          refine ⟨499123099734111339008299973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332748733156074226005533315 499123099734111339008299973)
          ·
            refine ⟨93585581200145876064056245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 499123099734111339008299973 93585581200145876064056245)
            ·
              refine ⟨8773648237513675881005273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93585581200145876064056245 8773648237513675881005273)
              ·
                refine ⟨6580236178135256910753955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8773648237513675881005273 6580236178135256910753955)
                ·
                  refine ⟨9870354267202885366130933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580236178135256910753955 9870354267202885366130933)
                  ·
                    refine ⟨925345712550270503074775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9870354267202885366130933 925345712550270503074775)
                    ·
                      rfl

theorem cell23_5406313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_5406313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406313 prefixEnd_5406313 := by exact prefixLift 5406313
  have htrace : WordTrace (prefixWord ++ tailWord_5406313) baseStart_5406313 baseEnd_5406313 := by
    simpa [prefixWord, tailWord_5406313, baseEnd_5406313] using wordTrace_append hprefix tailTrace_5406313
  have hstable : (prefixWord ++ tailWord_5406313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406313).length < 2 ^ (prefixWord ++ tailWord_5406313).sum := by decide
  have hdescent : baseEnd_5406313 < baseStart_5406313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406320 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2]
def baseStart_5406320 : Nat := 118140960795 + 5406320 * 2 ^ 59
def prefixEnd_5406320 : Nat := 4983230072969 + 3 ^ 40 * 5406320 * 2
def baseEnd_5406320 : Nat := 2776040732015392981836793

theorem tailTrace_5406320 : CollatzResearch.WordTrace tailWord_5406320 prefixEnd_5406320 2776040732015392981836793 := by
  unfold tailWord_5406320
  simp only [CollatzResearch.WordTrace]
  refine ⟨98592344886916720395688207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131456459849222293860917609 98592344886916720395688207)
  ·
    refine ⟨147888517330375080593532311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98592344886916720395688207 147888517330375080593532311)
    ·
      refine ⟨221832775995562620890298467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147888517330375080593532311 221832775995562620890298467)
      ·
        refine ⟨332749163993343931335447701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221832775995562620890298467 332749163993343931335447701)
        ·
          refine ⟨15597617062187996781349111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 332749163993343931335447701 15597617062187996781349111)
          ·
            refine ⟨23396425593281995172023667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15597617062187996781349111 23396425593281995172023667)
            ·
              refine ⟨35094638389922992758035501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23396425593281995172023667 35094638389922992758035501)
              ·
                refine ⟨13160489396221122284263313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35094638389922992758035501 13160489396221122284263313)
                ·
                  refine ⟨9870367047165841713197485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13160489396221122284263313 9870367047165841713197485)
                  ·
                    refine ⟨3701387642687190642449057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9870367047165841713197485 3701387642687190642449057)
                    ·
                      refine ⟨2776040732015392981836793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701387642687190642449057 2776040732015392981836793)
                      ·
                        rfl

theorem cell23_5406320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2].length) (baseStart_5406320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406320 prefixEnd_5406320 := by exact prefixLift 5406320
  have htrace : WordTrace (prefixWord ++ tailWord_5406320) baseStart_5406320 baseEnd_5406320 := by
    simpa [prefixWord, tailWord_5406320, baseEnd_5406320] using wordTrace_append hprefix tailTrace_5406320
  have hstable : (prefixWord ++ tailWord_5406320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406320).length < 2 ^ (prefixWord ++ tailWord_5406320).sum := by decide
  have hdescent : baseEnd_5406320 < baseStart_5406320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406360 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 2, 4]
def baseStart_5406360 : Nat := 118140960795 + 5406360 * 2 ^ 59
def prefixEnd_5406360 : Nat := 4983230072969 + 3 ^ 40 * 5406360 * 2
def baseEnd_5406360 : Nat := 925353757080524275112203

theorem tailTrace_5406360 : CollatzResearch.WordTrace tailWord_5406360 prefixEnd_5406360 925353757080524275112203 := by
  unfold tailWord_5406360
  simp only [CollatzResearch.WordTrace]
  refine ⟨98593074346844263811416267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131457432462459018415221689 98593074346844263811416267)
  ·
    refine ⟨147889611520266395717124401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98593074346844263811416267 147889611520266395717124401)
    ·
      refine ⟨110917208640199796787843301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147889611520266395717124401 110917208640199796787843301)
      ·
        refine ⟨20796976620037461897720619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110917208640199796787843301 20796976620037461897720619)
        ·
          refine ⟨31195464930056192846580929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20796976620037461897720619 31195464930056192846580929)
          ·
            refine ⟨23396598697542144634935697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31195464930056192846580929 23396598697542144634935697)
            ·
              refine ⟨17547449023156608476201773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23396598697542144634935697 17547449023156608476201773)
              ·
                refine ⟨6580293383683728178575665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17547449023156608476201773 6580293383683728178575665)
                ·
                  refine ⟨4935220037762796133931749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6580293383683728178575665 4935220037762796133931749)
                  ·
                    refine ⟨925353757080524275112203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935220037762796133931749 925353757080524275112203)
                    ·
                      rfl

theorem cell23_5406360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_5406360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406360 prefixEnd_5406360 := by exact prefixLift 5406360
  have htrace : WordTrace (prefixWord ++ tailWord_5406360) baseStart_5406360 baseEnd_5406360 := by
    simpa [prefixWord, tailWord_5406360, baseEnd_5406360] using wordTrace_append hprefix tailTrace_5406360
  have hstable : (prefixWord ++ tailWord_5406360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406360).length < 2 ^ (prefixWord ++ tailWord_5406360).sum := by decide
  have hdescent : baseEnd_5406360 < baseStart_5406360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406383 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3]
def baseStart_5406383 : Nat := 118140960795 + 5406383 * 2 ^ 59
def prefixEnd_5406383 : Nat := 4983230072969 + 3 ^ 40 * 5406383 * 2
def baseEnd_5406383 : Nat := 2776073081296626235349003

theorem tailTrace_5406383 : CollatzResearch.WordTrace tailWord_5406383 prefixEnd_5406383 2776073081296626235349003 := by
  unfold tailWord_5406383
  simp only [CollatzResearch.WordTrace]
  refine ⟨197186987572605202550919803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131457991715070135033946535 197186987572605202550919803)
  ·
    refine ⟨295780481358907803826379705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197186987572605202550919803 295780481358907803826379705)
    ·
      refine ⟨221835361019180852869784779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295780481358907803826379705 221835361019180852869784779)
      ·
        refine ⟨332753041528771279304677169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221835361019180852869784779 332753041528771279304677169)
        ·
          refine ⟨249564781146578459478507877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332753041528771279304677169 249564781146578459478507877)
          ·
            refine ⟨46793396464983461152220227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249564781146578459478507877 46793396464983461152220227)
            ·
              refine ⟨70190094697475191728330341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46793396464983461152220227 70190094697475191728330341)
              ·
                refine ⟨13160642755776598449061939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70190094697475191728330341 13160642755776598449061939)
                ·
                  refine ⟨19740964133664897673592909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13160642755776598449061939 19740964133664897673592909)
                  ·
                    refine ⟨7402861550124336627597341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19740964133664897673592909 7402861550124336627597341)
                    ·
                      refine ⟨2776073081296626235349003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402861550124336627597341 2776073081296626235349003)
                      ·
                        rfl

theorem cell23_5406383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_5406383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406383 prefixEnd_5406383 := by exact prefixLift 5406383
  have htrace : WordTrace (prefixWord ++ tailWord_5406383) baseStart_5406383 baseEnd_5406383 := by
    simpa [prefixWord, tailWord_5406383, baseEnd_5406383] using wordTrace_append hprefix tailTrace_5406383
  have hstable : (prefixWord ++ tailWord_5406383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406383).length < 2 ^ (prefixWord ++ tailWord_5406383).sum := by decide
  have hdescent : baseEnd_5406383 < baseStart_5406383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406390 : List Nat := [5, 1, 3, 1, 1, 2, 10]
def baseStart_5406390 : Nat := 118140960795 + 5406390 * 2 ^ 59
def prefixEnd_5406390 : Nat := 4983230072969 + 3 ^ 40 * 5406390 * 2
def baseEnd_5406390 : Nat := 34272551551372934666191

theorem tailTrace_5406390 : CollatzResearch.WordTrace tailWord_5406390 prefixEnd_5406390 34272551551372934666191 := by
  unfold tailWord_5406390
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324202680223740171651539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131458161922386561830949749 12324202680223740171651539)
  ·
    refine ⟨18486304020335610257477309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12324202680223740171651539 18486304020335610257477309)
    ·
      refine ⟨6932364007625853846553991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18486304020335610257477309 6932364007625853846553991)
      ·
        refine ⟨10398546011438780769830987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6932364007625853846553991 10398546011438780769830987)
        ·
          refine ⟨15597819017158171154746481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10398546011438780769830987 15597819017158171154746481)
          ·
            refine ⟨11698364262868628366059861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15597819017158171154746481 11698364262868628366059861)
            ·
              refine ⟨34272551551372934666191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11698364262868628366059861 34272551551372934666191)
              ·
                rfl

theorem cell23_5406390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 10].length) (baseStart_5406390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406390 prefixEnd_5406390 := by exact prefixLift 5406390
  have htrace : WordTrace (prefixWord ++ tailWord_5406390) baseStart_5406390 baseEnd_5406390 := by
    simpa [prefixWord, tailWord_5406390, baseEnd_5406390] using wordTrace_append hprefix tailTrace_5406390
  have hstable : (prefixWord ++ tailWord_5406390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406390).length < 2 ^ (prefixWord ++ tailWord_5406390).sum := by decide
  have hdescent : baseEnd_5406390 < baseStart_5406390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406400 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3]
def baseStart_5406400 : Nat := 118140960795 + 5406400 * 2 ^ 59
def prefixEnd_5406400 : Nat := 4983230072969 + 3 ^ 40 * 5406400 * 2
def baseEnd_5406400 : Nat := 2776081810467752668836425

theorem tailTrace_5406400 : CollatzResearch.WordTrace tailWord_5406400 prefixEnd_5406400 2776081810467752668836425 := by
  unfold tailWord_5406400
  simp only [CollatzResearch.WordTrace]
  refine ⟨98593803806771807227144327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131458405075695742969525769 98593803806771807227144327)
  ·
    refine ⟨147890705710157710840716491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98593803806771807227144327 147890705710157710840716491)
    ·
      refine ⟨221836058565236566261074737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147890705710157710840716491 221836058565236566261074737)
      ·
        refine ⟨166377043923927424695806053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221836058565236566261074737 166377043923927424695806053)
        ·
          refine ⟨31195695735736392130463635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166377043923927424695806053 31195695735736392130463635)
          ·
            refine ⟨46793543603604588195695453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31195695735736392130463635 46793543603604588195695453)
            ·
              refine ⟨17547578851351720573385795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46793543603604588195695453 17547578851351720573385795)
              ·
                refine ⟨26321368277027580860078693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17547578851351720573385795 26321368277027580860078693)
                ·
                  refine ⟨4935256551942671411264755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26321368277027580860078693 4935256551942671411264755)
                  ·
                    refine ⟨7402884827914007116897133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4935256551942671411264755 7402884827914007116897133)
                    ·
                      refine ⟨2776081810467752668836425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402884827914007116897133 2776081810467752668836425)
                      ·
                        rfl

theorem cell23_5406400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_5406400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406400 prefixEnd_5406400 := by exact prefixLift 5406400
  have htrace : WordTrace (prefixWord ++ tailWord_5406400) baseStart_5406400 baseEnd_5406400 := by
    simpa [prefixWord, tailWord_5406400, baseEnd_5406400] using wordTrace_append hprefix tailTrace_5406400
  have hstable : (prefixWord ++ tailWord_5406400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406400).length < 2 ^ (prefixWord ++ tailWord_5406400).sum := by decide
  have hdescent : baseEnd_5406400 < baseStart_5406400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406416 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 8]
def baseStart_5406416 : Nat := 118140960795 + 5406416 * 2 ^ 59
def prefixEnd_5406416 : Nat := 4983230072969 + 3 ^ 40 * 5406416 * 2
def baseEnd_5406416 : Nat := 925363342052741535412117

theorem tailTrace_5406416 : CollatzResearch.WordTrace tailWord_5406416 prefixEnd_5406416 925363342052741535412117 := by
  unfold tailWord_5406416
  simp only [CollatzResearch.WordTrace]
  refine ⟨98594095590742824593435551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131458794120990432791247401 98594095590742824593435551)
  ·
    refine ⟨147891143386114236890153327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98594095590742824593435551 147891143386114236890153327)
    ·
      refine ⟨221836715079171355335229991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147891143386114236890153327 221836715079171355335229991)
      ·
        refine ⟨332755072618757033002844987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221836715079171355335229991 332755072618757033002844987)
        ·
          refine ⟨499132608928135549504267481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332755072618757033002844987 499132608928135549504267481)
          ·
            refine ⟨374349456696101662128200611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499132608928135549504267481 374349456696101662128200611)
            ·
              refine ⟨561524185044152493192300917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374349456696101662128200611 561524185044152493192300917)
              ·
                refine ⟨52642892347889296236778211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561524185044152493192300917 52642892347889296236778211)
                ·
                  refine ⟨78964338521833944355167317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52642892347889296236778211 78964338521833944355167317)
                  ·
                    refine ⟨925363342052741535412117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78964338521833944355167317 925363342052741535412117)
                    ·
                      rfl

theorem cell23_5406416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_5406416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406416 prefixEnd_5406416 := by exact prefixLift 5406416
  have htrace : WordTrace (prefixWord ++ tailWord_5406416) baseStart_5406416 baseEnd_5406416 := by
    simpa [prefixWord, tailWord_5406416, baseEnd_5406416] using wordTrace_append hprefix tailTrace_5406416
  have hstable : (prefixWord ++ tailWord_5406416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406416).length < 2 ^ (prefixWord ++ tailWord_5406416).sum := by decide
  have hdescent : baseEnd_5406416 < baseStart_5406416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406463 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 7]
def baseStart_5406463 : Nat := 118140960795 + 5406463 * 2 ^ 59
def prefixEnd_5406463 : Nat := 4983230072969 + 3 ^ 40 * 5406463 * 2
def baseEnd_5406463 : Nat := 308457128860998435816515

theorem tailTrace_5406463 : CollatzResearch.WordTrace tailWord_5406463 prefixEnd_5406463 308457128860998435816515 := by
  unfold tailWord_5406463
  simp only [CollatzResearch.WordTrace]
  refine ⟨197189905412315376213832043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131459936941543584142554695 197189905412315376213832043)
  ·
    refine ⟨295784858118473064320748065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197189905412315376213832043 295784858118473064320748065)
    ·
      refine ⟨221838643588854798240561049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295784858118473064320748065 221838643588854798240561049)
      ·
        refine ⟨166378982691641098680420787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221838643588854798240561049 166378982691641098680420787)
        ·
          refine ⟨249568474037461648020631181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166378982691641098680420787 249568474037461648020631181)
          ·
            refine ⟨93588177764048118007736693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249568474037461648020631181 93588177764048118007736693)
            ·
              refine ⟨8773891665379511063225315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93588177764048118007736693 8773891665379511063225315)
              ·
                refine ⟨13160837498069266594837973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773891665379511063225315 13160837498069266594837973)
                ·
                  refine ⟨308457128860998435816515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13160837498069266594837973 308457128860998435816515)
                  ·
                    rfl

theorem cell23_5406463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 7].length) (baseStart_5406463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406463 prefixEnd_5406463 := by exact prefixLift 5406463
  have htrace : WordTrace (prefixWord ++ tailWord_5406463) baseStart_5406463 baseEnd_5406463 := by
    simpa [prefixWord, tailWord_5406463, baseEnd_5406463] using wordTrace_append hprefix tailTrace_5406463
  have hstable : (prefixWord ++ tailWord_5406463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406463).length < 2 ^ (prefixWord ++ tailWord_5406463).sum := by decide
  have hdescent : baseEnd_5406463 < baseStart_5406463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406473 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_5406473 : Nat := 118140960795 + 5406473 * 2 ^ 59
def prefixEnd_5406473 : Nat := 4983230072969 + 3 ^ 40 * 5406473 * 2
def baseEnd_5406473 : Nat := 2776119294555530883223589

theorem tailTrace_5406473 : CollatzResearch.WordTrace tailWord_5406473 prefixEnd_5406473 2776119294555530883223589 := by
  unfold tailWord_5406473
  simp only [CollatzResearch.WordTrace]
  refine ⟨197190270142279147921696073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131460180094852765281130715 197190270142279147921696073)
  ·
    refine ⟨147892702606709360941272055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197190270142279147921696073 147892702606709360941272055)
    ·
      refine ⟨221839053910064041411908083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147892702606709360941272055 221839053910064041411908083)
      ·
        refine ⟨332758580865096062117862125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221839053910064041411908083 332758580865096062117862125)
        ·
          refine ⟨124784467824411023294198297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332758580865096062117862125 124784467824411023294198297)
          ·
            refine ⟨93588350868308267470648723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124784467824411023294198297 93588350868308267470648723)
            ·
              refine ⟨140382526302462401205973085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93588350868308267470648723 140382526302462401205973085)
              ·
                refine ⟨52643447363423400452239907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140382526302462401205973085 52643447363423400452239907)
                ·
                  refine ⟨78965171045135100678359861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52643447363423400452239907 78965171045135100678359861)
                  ·
                    refine ⟨7402984785481415688596237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78965171045135100678359861 7402984785481415688596237)
                    ·
                      refine ⟨2776119294555530883223589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7402984785481415688596237 2776119294555530883223589)
                      ·
                        rfl

theorem cell23_5406473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_5406473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406473 prefixEnd_5406473 := by exact prefixLift 5406473
  have htrace : WordTrace (prefixWord ++ tailWord_5406473) baseStart_5406473 baseEnd_5406473 := by
    simpa [prefixWord, tailWord_5406473, baseEnd_5406473] using wordTrace_append hprefix tailTrace_5406473
  have hstable : (prefixWord ++ tailWord_5406473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406473).length < 2 ^ (prefixWord ++ tailWord_5406473).sum := by decide
  have hdescent : baseEnd_5406473 < baseStart_5406473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406474 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_5406474 : Nat := 118140960795 + 5406474 * 2 ^ 59
def prefixEnd_5406474 : Nat := 4983230072969 + 3 ^ 40 * 5406474 * 2
def baseEnd_5406474 : Nat := 2776119808036185379311085

theorem tailTrace_5406474 : CollatzResearch.WordTrace tailWord_5406474 prefixEnd_5406474 2776119808036185379311085 := by
  unfold tailWord_5406474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49297576653818881273120619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131460204410183683394988317 49297576653818881273120619)
  ·
    refine ⟨73946364980728321909680929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49297576653818881273120619 73946364980728321909680929)
    ·
      refine ⟨55459773735546241432260697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73946364980728321909680929 55459773735546241432260697)
      ·
        refine ⟨41594830301659681074195523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55459773735546241432260697 41594830301659681074195523)
        ·
          refine ⟨62392245452489521611293285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41594830301659681074195523 62392245452489521611293285)
          ·
            refine ⟨11698546022341785302117491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62392245452489521611293285 11698546022341785302117491)
            ·
              refine ⟨17547819033512677953176237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11698546022341785302117491 17547819033512677953176237)
              ·
                refine ⟨6580432137567254232441089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17547819033512677953176237 6580432137567254232441089)
                ·
                  refine ⟨4935324103175440674330817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6580432137567254232441089 4935324103175440674330817)
                  ·
                    refine ⟨3701493077381580505748113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935324103175440674330817 3701493077381580505748113)
                    ·
                      refine ⟨2776119808036185379311085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701493077381580505748113 2776119808036185379311085)
                      ·
                        rfl

theorem cell23_5406474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_5406474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406474 prefixEnd_5406474 := by exact prefixLift 5406474
  have htrace : WordTrace (prefixWord ++ tailWord_5406474) baseStart_5406474 baseEnd_5406474 := by
    simpa [prefixWord, tailWord_5406474, baseEnd_5406474] using wordTrace_append hprefix tailTrace_5406474
  have hstable : (prefixWord ++ tailWord_5406474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406474).length < 2 ^ (prefixWord ++ tailWord_5406474).sum := by decide
  have hdescent : baseEnd_5406474 < baseStart_5406474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406514 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_5406514 : Nat := 118140960795 + 5406514 * 2 ^ 59
def prefixEnd_5406514 : Nat := 4983230072969 + 3 ^ 40 * 5406514 * 2
def baseEnd_5406514 : Nat := 308460038584707246978989

theorem tailTrace_5406514 : CollatzResearch.WordTrace tailWord_5406514 prefixEnd_5406514 308460038584707246978989 := by
  unfold tailWord_5406514
  simp only [CollatzResearch.WordTrace]
  refine ⟨49297941383782652980984649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131461177023420407949292397 49297941383782652980984649)
  ·
    refine ⟨36973456037836989735738487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49297941383782652980984649 36973456037836989735738487)
    ·
      refine ⟨55460184056755484603607731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36973456037836989735738487 55460184056755484603607731)
      ·
        refine ⟨83190276085133226905411597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55460184056755484603607731 83190276085133226905411597)
        ·
          refine ⟨31196353531924960089529349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83190276085133226905411597 31196353531924960089529349)
          ·
            refine ⟨5849316287235930016786753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31196353531924960089529349 5849316287235930016786753)
            ·
              refine ⟨4386987215426947512590065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849316287235930016786753 4386987215426947512590065)
              ·
                refine ⟨3290240411570210634442549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386987215426947512590065 3290240411570210634442549)
                ·
                  refine ⟨308460038584707246978989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290240411570210634442549 308460038584707246978989)
                  ·
                    rfl

theorem cell23_5406514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_5406514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406514 prefixEnd_5406514 := by exact prefixLift 5406514
  have htrace : WordTrace (prefixWord ++ tailWord_5406514) baseStart_5406514 baseEnd_5406514 := by
    simpa [prefixWord, tailWord_5406514, baseEnd_5406514] using wordTrace_append hprefix tailTrace_5406514
  have hstable : (prefixWord ++ tailWord_5406514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406514).length < 2 ^ (prefixWord ++ tailWord_5406514).sum := by decide
  have hdescent : baseEnd_5406514 < baseStart_5406514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406553 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 8]
def baseStart_5406553 : Nat := 118140960795 + 5406553 * 2 ^ 59
def prefixEnd_5406553 : Nat := 4983230072969 + 3 ^ 40 * 5406553 * 2
def baseEnd_5406553 : Nat := 308462263667543396691469

theorem tailTrace_5406553 : CollatzResearch.WordTrace tailWord_5406553 prefixEnd_5406553 308462263667543396691469 := by
  unfold tailWord_5406553
  simp only [CollatzResearch.WordTrace]
  refine ⟨197193187981989321584608313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131462125321326214389738875 197193187981989321584608313)
  ·
    refine ⟨147894890986491991188456235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197193187981989321584608313 147894890986491991188456235)
    ·
      refine ⟨221842336479737986782684353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147894890986491991188456235 221842336479737986782684353)
      ·
        refine ⟨166381752359803490087013265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221842336479737986782684353 166381752359803490087013265)
        ·
          refine ⟨124786314269852617565259949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166381752359803490087013265 124786314269852617565259949)
          ·
            refine ⟨46794867851194731586972481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124786314269852617565259949 46794867851194731586972481)
            ·
              refine ⟨35096150888396048690229361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46794867851194731586972481 35096150888396048690229361)
              ·
                refine ⟨26322113166297036517672021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35096150888396048690229361 26322113166297036517672021)
                ·
                  refine ⟨308462263667543396691469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26322113166297036517672021 308462263667543396691469)
                  ·
                    rfl

theorem cell23_5406553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_5406553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406553 prefixEnd_5406553 := by exact prefixLift 5406553
  have htrace : WordTrace (prefixWord ++ tailWord_5406553) baseStart_5406553 baseEnd_5406553 := by
    simpa [prefixWord, tailWord_5406553, baseEnd_5406553] using wordTrace_append hprefix tailTrace_5406553
  have hstable : (prefixWord ++ tailWord_5406553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406553).length < 2 ^ (prefixWord ++ tailWord_5406553).sum := by decide
  have hdescent : baseEnd_5406553 < baseStart_5406553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406574 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_5406574 : Nat := 118140960795 + 5406574 * 2 ^ 59
def prefixEnd_5406574 : Nat := 4983230072969 + 3 ^ 40 * 5406574 * 2
def baseEnd_5406574 : Nat := 925390385367211662686875

theorem tailTrace_5406574 : CollatzResearch.WordTrace tailWord_5406574 prefixEnd_5406574 925390385367211662686875 := by
  unfold tailWord_5406574
  simp only [CollatzResearch.WordTrace]
  refine ⟨24649244239364155271390347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131462635943275494780748517 24649244239364155271390347)
  ·
    refine ⟨36973866359046232907085521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24649244239364155271390347 36973866359046232907085521)
    ·
      refine ⟨27730399769284674680314141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36973866359046232907085521 27730399769284674680314141)
      ·
        refine ⟨10398899913481753005117803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27730399769284674680314141 10398899913481753005117803)
        ·
          refine ⟨15598349870222629507676705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10398899913481753005117803 15598349870222629507676705)
          ·
            refine ⟨11698762402666972130757529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15598349870222629507676705 11698762402666972130757529)
            ·
              refine ⟨8774071802000229098068147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11698762402666972130757529 8774071802000229098068147)
              ·
                refine ⟨13161107703000343647102221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8774071802000229098068147 13161107703000343647102221)
                ·
                  refine ⟨4935415388625128867663333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13161107703000343647102221 4935415388625128867663333)
                  ·
                    refine ⟨925390385367211662686875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935415388625128867663333 925390385367211662686875)
                    ·
                      rfl

theorem cell23_5406574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_5406574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406574 prefixEnd_5406574 := by exact prefixLift 5406574
  have htrace : WordTrace (prefixWord ++ tailWord_5406574) baseStart_5406574 baseEnd_5406574 := by
    simpa [prefixWord, tailWord_5406574, baseEnd_5406574] using wordTrace_append hprefix tailTrace_5406574
  have hstable : (prefixWord ++ tailWord_5406574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406574).length < 2 ^ (prefixWord ++ tailWord_5406574).sum := by decide
  have hdescent : baseEnd_5406574 < baseStart_5406574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406597 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_5406597 : Nat := 118140960795 + 5406597 * 2 ^ 59
def prefixEnd_5406597 : Nat := 4983230072969 + 3 ^ 40 * 5406597 * 2
def baseEnd_5406597 : Nat := 2776182966156688398073019

theorem tailTrace_5406597 : CollatzResearch.WordTrace tailWord_5406597 prefixEnd_5406597 2776182966156688398073019 := by
  unfold tailWord_5406597
  simp only [CollatzResearch.WordTrace]
  refine ⟨197194792793829917099210045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131463195195886611399473363 197194792793829917099210045)
  ·
    refine ⟨73948047297686218912203767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197194792793829917099210045 73948047297686218912203767)
    ·
      refine ⟨110922070946529328368305651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73948047297686218912203767 110922070946529328368305651)
      ·
        refine ⟨166383106419793992552458477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110922070946529328368305651 166383106419793992552458477)
        ·
          refine ⟨62393664907422747207171929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166383106419793992552458477 62393664907422747207171929)
          ·
            refine ⟨46795248680567060405378947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62393664907422747207171929 46795248680567060405378947)
            ·
              refine ⟨70192873020850590608068421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46795248680567060405378947 70192873020850590608068421)
              ·
                refine ⟨13161163691409485739012829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70192873020850590608068421 13161163691409485739012829)
                ·
                  refine ⟨4935436384278557152129811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13161163691409485739012829 4935436384278557152129811)
                  ·
                    refine ⟨7403154576417835728194717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4935436384278557152129811 7403154576417835728194717)
                    ·
                      refine ⟨2776182966156688398073019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7403154576417835728194717 2776182966156688398073019)
                      ·
                        rfl

theorem cell23_5406597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_5406597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406597 prefixEnd_5406597 := by exact prefixLift 5406597
  have htrace : WordTrace (prefixWord ++ tailWord_5406597) baseStart_5406597 baseEnd_5406597 := by
    simpa [prefixWord, tailWord_5406597, baseEnd_5406597] using wordTrace_append hprefix tailTrace_5406597
  have hstable : (prefixWord ++ tailWord_5406597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406597).length < 2 ^ (prefixWord ++ tailWord_5406597).sum := by decide
  have hdescent : baseEnd_5406597 < baseStart_5406597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406631 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5406631 : Nat := 118140960795 + 5406631 * 2 ^ 59
def prefixEnd_5406631 : Nat := 4983230072969 + 3 ^ 40 * 5406631 * 2
def baseEnd_5406631 : Nat := 2776200424498941265047863

theorem tailTrace_5406631 : CollatzResearch.WordTrace tailWord_5406631 prefixEnd_5406631 2776200424498941265047863 := by
  unfold tailWord_5406631
  simp only [CollatzResearch.WordTrace]
  refine ⟨197196032875706740905947747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131464021917137827270631831 197196032875706740905947747)
  ·
    refine ⟨295794049313560111358921621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197196032875706740905947747 295794049313560111358921621)
    ·
      refine ⟨13865346061573130219949451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 295794049313560111358921621 13865346061573130219949451)
      ·
        refine ⟨20798019092359695329924177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865346061573130219949451 20798019092359695329924177)
        ·
          refine ⟨15598514319269771497443133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798019092359695329924177 15598514319269771497443133)
          ·
            refine ⟨5849442869726164311541175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15598514319269771497443133 5849442869726164311541175)
            ·
              refine ⟨8774164304589246467311763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849442869726164311541175 8774164304589246467311763)
              ·
                refine ⟨13161246456883869700967645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8774164304589246467311763 13161246456883869700967645)
                ·
                  refine ⟨4935467421331451137862867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13161246456883869700967645 4935467421331451137862867)
                  ·
                    refine ⟨7403201131997176706794301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4935467421331451137862867 7403201131997176706794301)
                    ·
                      refine ⟨2776200424498941265047863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7403201131997176706794301 2776200424498941265047863)
                      ·
                        rfl

theorem cell23_5406631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5406631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406631 prefixEnd_5406631 := by exact prefixLift 5406631
  have htrace : WordTrace (prefixWord ++ tailWord_5406631) baseStart_5406631 baseEnd_5406631 := by
    simpa [prefixWord, tailWord_5406631, baseEnd_5406631] using wordTrace_append hprefix tailTrace_5406631
  have hstable : (prefixWord ++ tailWord_5406631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406631).length < 2 ^ (prefixWord ++ tailWord_5406631).sum := by decide
  have hdescent : baseEnd_5406631 < baseStart_5406631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406654 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_5406654 : Nat := 118140960795 + 5406654 * 2 ^ 59
def prefixEnd_5406654 : Nat := 4983230072969 + 3 ^ 40 * 5406654 * 2
def baseEnd_5406654 : Nat := 2776212234553994675060257

theorem tailTrace_5406654 : CollatzResearch.WordTrace tailWord_5406654 prefixEnd_5406654 2776212234553994675060257 := by
  unfold tailWord_5406654
  simp only [CollatzResearch.WordTrace]
  refine ⟨24649608969327926979254377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131464581169748943889356677 24649608969327926979254377)
  ·
    refine ⟨18487206726995945234440783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24649608969327926979254377 18487206726995945234440783)
    ·
      refine ⟨27730810090493917851661175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18487206726995945234440783 27730810090493917851661175)
      ·
        refine ⟨41596215135740876777491763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27730810090493917851661175 41596215135740876777491763)
        ·
          refine ⟨62394322703611315166237645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41596215135740876777491763 62394322703611315166237645)
          ·
            refine ⟨23397871013854243187339117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62394322703611315166237645 23397871013854243187339117)
            ·
              refine ⟨8774201630195341195252169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23397871013854243187339117 8774201630195341195252169)
              ·
                refine ⟨6580651222646505896439127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774201630195341195252169 6580651222646505896439127)
                ·
                  refine ⟨9870976833969758844658691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580651222646505896439127 9870976833969758844658691)
                  ·
                    refine ⟨14806465250954638266988037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9870976833969758844658691 14806465250954638266988037)
                    ·
                      refine ⟨2776212234553994675060257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14806465250954638266988037 2776212234553994675060257)
                      ·
                        rfl

theorem cell23_5406654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_5406654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406654 prefixEnd_5406654 := by exact prefixLift 5406654
  have htrace : WordTrace (prefixWord ++ tailWord_5406654) baseStart_5406654 baseEnd_5406654 := by
    simpa [prefixWord, tailWord_5406654, baseEnd_5406654] using wordTrace_append hprefix tailTrace_5406654
  have hstable : (prefixWord ++ tailWord_5406654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406654).length < 2 ^ (prefixWord ++ tailWord_5406654).sum := by decide
  have hdescent : baseEnd_5406654 < baseStart_5406654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406671 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 1, 2, 2]
def baseStart_5406671 : Nat := 118140960795 + 5406671 * 2 ^ 59
def prefixEnd_5406671 : Nat := 4983230072969 + 3 ^ 40 * 5406671 * 2
def baseEnd_5406671 : Nat := 2776220963725121108547679

theorem tailTrace_5406671 : CollatzResearch.WordTrace tailWord_5406671 prefixEnd_5406671 2776220963725121108547679 := by
  unfold tailWord_5406671
  simp only [CollatzResearch.WordTrace]
  refine ⟨197197491795561827737403867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131464994530374551824935911 197197491795561827737403867)
  ·
    refine ⟨295796237693342741606105801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197197491795561827737403867 295796237693342741606105801)
    ·
      refine ⟨221847178270007056204579351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295796237693342741606105801 221847178270007056204579351)
      ·
        refine ⟨332770767405010584306869027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221847178270007056204579351 332770767405010584306869027)
        ·
          refine ⟨499156151107515876460303541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332770767405010584306869027 499156151107515876460303541)
          ·
            refine ⟨46795889166329613418153457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 499156151107515876460303541 46795889166329613418153457)
            ·
              refine ⟨35096916874747210063615093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46795889166329613418153457 35096916874747210063615093)
              ·
                refine ⟨3290335957007550943463915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35096916874747210063615093 3290335957007550943463915)
                ·
                  refine ⟨4935503935511326415195873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290335957007550943463915 4935503935511326415195873)
                  ·
                    refine ⟨3701627951633494811396905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935503935511326415195873 3701627951633494811396905)
                    ·
                      refine ⟨2776220963725121108547679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701627951633494811396905 2776220963725121108547679)
                      ·
                        rfl

theorem cell23_5406671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 2, 2].length) (baseStart_5406671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406671 prefixEnd_5406671 := by exact prefixLift 5406671
  have htrace : WordTrace (prefixWord ++ tailWord_5406671) baseStart_5406671 baseEnd_5406671 := by
    simpa [prefixWord, tailWord_5406671, baseEnd_5406671] using wordTrace_append hprefix tailTrace_5406671
  have hstable : (prefixWord ++ tailWord_5406671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406671).length < 2 ^ (prefixWord ++ tailWord_5406671).sum := by decide
  have hdescent : baseEnd_5406671 < baseStart_5406671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406701 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5406701 : Nat := 118140960795 + 5406701 * 2 ^ 59
def prefixEnd_5406701 : Nat := 4983230072969 + 3 ^ 40 * 5406701 * 2
def baseEnd_5406701 : Nat := 2776236368144755991172541

theorem tailTrace_5406701 : CollatzResearch.WordTrace tailWord_5406701 prefixEnd_5406701 2776236368144755991172541 := by
  unfold tailWord_5406701
  simp only [CollatzResearch.WordTrace]
  refine ⟨197198585985453142860995957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131465723990302095240663971 197198585985453142860995957)
  ·
    refine ⟨18487367436136232143218371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197198585985453142860995957 18487367436136232143218371)
    ·
      refine ⟨27731051154204348214827557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18487367436136232143218371 27731051154204348214827557)
      ·
        refine ⟨5199572091413315290280167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27731051154204348214827557 5199572091413315290280167)
        ·
          refine ⟨7799358137119972935420251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199572091413315290280167 7799358137119972935420251)
          ·
            refine ⟨11699037205679959403130377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7799358137119972935420251 11699037205679959403130377)
            ·
              refine ⟨8774277904259969552347783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11699037205679959403130377 8774277904259969552347783)
              ·
                refine ⟨13161416856389954328521675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8774277904259969552347783 13161416856389954328521675)
                ·
                  refine ⟨19742125284584931492782513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13161416856389954328521675 19742125284584931492782513)
                  ·
                    refine ⟨14806593963438698619586885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19742125284584931492782513 14806593963438698619586885)
                    ·
                      refine ⟨2776236368144755991172541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14806593963438698619586885 2776236368144755991172541)
                      ·
                        rfl

theorem cell23_5406701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5406701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406701 prefixEnd_5406701 := by exact prefixLift 5406701
  have htrace : WordTrace (prefixWord ++ tailWord_5406701) baseStart_5406701 baseEnd_5406701 := by
    simpa [prefixWord, tailWord_5406701, baseEnd_5406701] using wordTrace_append hprefix tailTrace_5406701
  have hstable : (prefixWord ++ tailWord_5406701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406701).length < 2 ^ (prefixWord ++ tailWord_5406701).sum := by decide
  have hdescent : baseEnd_5406701 < baseStart_5406701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406704 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3]
def baseStart_5406704 : Nat := 118140960795 + 5406704 * 2 ^ 59
def prefixEnd_5406704 : Nat := 4983230072969 + 3 ^ 40 * 5406704 * 2
def baseEnd_5406704 : Nat := 2776237908586719479435027

theorem tailTrace_5406704 : CollatzResearch.WordTrace tailWord_5406704 prefixEnd_5406704 2776237908586719479435027 := by
  unfold tailWord_5406704
  simp only [CollatzResearch.WordTrace]
  refine ⟨98599347702221137186677583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131465796936294849582236777 98599347702221137186677583)
  ·
    refine ⟨147899021553331705780016375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98599347702221137186677583 147899021553331705780016375)
    ·
      refine ⟨221848532329997558670024563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147899021553331705780016375 221848532329997558670024563)
      ·
        refine ⟨332772798494996338005036845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221848532329997558670024563 332772798494996338005036845)
        ·
          refine ⟨124789799435623626751888817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332772798494996338005036845 124789799435623626751888817)
          ·
            refine ⟨93592349576717720063916613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124789799435623626751888817 93592349576717720063916613)
            ·
              refine ⟨17548565545634572511984365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93592349576717720063916613 17548565545634572511984365)
              ·
                refine ⟨6580712079612964691994137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17548565545634572511984365 6580712079612964691994137)
                ·
                  refine ⟨4935534059709723518995603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6580712079612964691994137 4935534059709723518995603)
                  ·
                    refine ⟨7403301089564585278493405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4935534059709723518995603 7403301089564585278493405)
                    ·
                      refine ⟨2776237908586719479435027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7403301089564585278493405 2776237908586719479435027)
                      ·
                        rfl

theorem cell23_5406704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 1, 3].length) (baseStart_5406704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406704 prefixEnd_5406704 := by exact prefixLift 5406704
  have htrace : WordTrace (prefixWord ++ tailWord_5406704) baseStart_5406704 baseEnd_5406704 := by
    simpa [prefixWord, tailWord_5406704, baseEnd_5406704] using wordTrace_append hprefix tailTrace_5406704
  have hstable : (prefixWord ++ tailWord_5406704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406704).length < 2 ^ (prefixWord ++ tailWord_5406704).sum := by decide
  have hdescent : baseEnd_5406704 < baseStart_5406704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406757 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_5406757 : Nat := 118140960795 + 5406757 * 2 ^ 59
def prefixEnd_5406757 : Nat := 4983230072969 + 3 ^ 40 * 5406757 * 2
def baseEnd_5406757 : Nat := 2776265123061407772072283

theorem tailTrace_5406757 : CollatzResearch.WordTrace tailWord_5406757 prefixEnd_5406757 2776265123061407772072283 := by
  unfold tailWord_5406757
  simp only [CollatzResearch.WordTrace]
  refine ⟨197200628473250264425034525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131467085648833509616689683 197200628473250264425034525)
  ·
    refine ⟨73950235677468849159387947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197200628473250264425034525 73950235677468849159387947)
    ·
      refine ⟨110925353516203273739081921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73950235677468849159387947 110925353516203273739081921)
      ·
        refine ⟨83194015137152455304311441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110925353516203273739081921 83194015137152455304311441)
        ·
          refine ⟨62395511352864341478233581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83194015137152455304311441 62395511352864341478233581)
          ·
            refine ⟨23398316757324128054337593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62395511352864341478233581 23398316757324128054337593)
            ·
              refine ⟨17548737567993096040753195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23398316757324128054337593 17548737567993096040753195)
              ·
                refine ⟨26323106351989644061129793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17548737567993096040753195 26323106351989644061129793)
                ·
                  refine ⟨19742329763992233045847345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26323106351989644061129793 19742329763992233045847345)
                  ·
                    refine ⟨14806747322994174784385509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19742329763992233045847345 14806747322994174784385509)
                    ·
                      refine ⟨2776265123061407772072283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14806747322994174784385509 2776265123061407772072283)
                      ·
                        rfl

theorem cell23_5406757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_5406757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406757 prefixEnd_5406757 := by exact prefixLift 5406757
  have htrace : WordTrace (prefixWord ++ tailWord_5406757) baseStart_5406757 baseEnd_5406757 := by
    simpa [prefixWord, tailWord_5406757, baseEnd_5406757] using wordTrace_append hprefix tailTrace_5406757
  have hstable : (prefixWord ++ tailWord_5406757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406757).length < 2 ^ (prefixWord ++ tailWord_5406757).sum := by decide
  have hdescent : baseEnd_5406757 < baseStart_5406757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406784 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 5]
def baseStart_5406784 : Nat := 118140960795 + 5406784 * 2 ^ 59
def prefixEnd_5406784 : Nat := 4983230072969 + 3 ^ 40 * 5406784 * 2
def baseEnd_5406784 : Nat := 308475443004342129603851

theorem tailTrace_5406784 : CollatzResearch.WordTrace tailWord_5406784 prefixEnd_5406784 308475443004342129603851 := by
  unfold tailWord_5406784
  simp only [CollatzResearch.WordTrace]
  refine ⟨98600806622076224018133703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131467742162768298690844937 98600806622076224018133703)
  ·
    refine ⟨147901209933114336027200555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98600806622076224018133703 147901209933114336027200555)
    ·
      refine ⟨221851814899671504040800833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147901209933114336027200555 221851814899671504040800833)
      ·
        refine ⟨166388861174753628030600625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221851814899671504040800833 166388861174753628030600625)
        ·
          refine ⟨124791645881065221022950469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166388861174753628030600625 124791645881065221022950469)
          ·
            refine ⟨23398433602699728941803213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124791645881065221022950469 23398433602699728941803213)
            ·
              refine ⟨8774412601012398353176205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23398433602699728941803213 8774412601012398353176205)
              ·
                refine ⟨3290404725379649382441077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8774412601012398353176205 3290404725379649382441077)
                ·
                  refine ⟨308475443004342129603851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290404725379649382441077 308475443004342129603851)
                  ·
                    rfl

theorem cell23_5406784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 5].length) (baseStart_5406784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406784 prefixEnd_5406784 := by exact prefixLift 5406784
  have htrace : WordTrace (prefixWord ++ tailWord_5406784) baseStart_5406784 baseEnd_5406784 := by
    simpa [prefixWord, tailWord_5406784, baseEnd_5406784] using wordTrace_append hprefix tailTrace_5406784
  have hstable : (prefixWord ++ tailWord_5406784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406784).length < 2 ^ (prefixWord ++ tailWord_5406784).sum := by decide
  have hdescent : baseEnd_5406784 < baseStart_5406784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406800 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_5406800 : Nat := 118140960795 + 5406800 * 2 ^ 59
def prefixEnd_5406800 : Nat := 4983230072969 + 3 ^ 40 * 5406800 * 2
def baseEnd_5406800 : Nat := 2776287202729551103834585

theorem tailTrace_5406800 : CollatzResearch.WordTrace tailWord_5406800 prefixEnd_5406800 2776287202729551103834585 := by
  unfold tailWord_5406800
  simp only [CollatzResearch.WordTrace]
  refine ⟨98601098406047241384424927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131468131208062988512566569 98601098406047241384424927)
  ·
    refine ⟨147901647609070862076637391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98601098406047241384424927 147901647609070862076637391)
    ·
      refine ⟨221852471413606293114956087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147901647609070862076637391 221852471413606293114956087)
      ·
        refine ⟨332778707120409439672434131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221852471413606293114956087 332778707120409439672434131)
        ·
          refine ⟨499168060680614159508651197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332778707120409439672434131 499168060680614159508651197)
          ·
            refine ⟨187188022755230309815744199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499168060680614159508651197 187188022755230309815744199)
            ·
              refine ⟨280782034132845464723616299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187188022755230309815744199 280782034132845464723616299)
              ·
                refine ⟨421173051199268197085424449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280782034132845464723616299 421173051199268197085424449)
                ·
                  refine ⟨315879788399451147814068337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421173051199268197085424449 315879788399451147814068337)
                  ·
                    refine ⟨236909841299588360860551253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315879788399451147814068337 236909841299588360860551253)
                    ·
                      refine ⟨2776287202729551103834585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 236909841299588360860551253 2776287202729551103834585)
                      ·
                        rfl

theorem cell23_5406800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_5406800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406800 prefixEnd_5406800 := by exact prefixLift 5406800
  have htrace : WordTrace (prefixWord ++ tailWord_5406800) baseStart_5406800 baseEnd_5406800 := by
    simpa [prefixWord, tailWord_5406800, baseEnd_5406800] using wordTrace_append hprefix tailTrace_5406800
  have hstable : (prefixWord ++ tailWord_5406800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406800).length < 2 ^ (prefixWord ++ tailWord_5406800).sum := by decide
  have hdescent : baseEnd_5406800 < baseStart_5406800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406804 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 5, 2]
def baseStart_5406804 : Nat := 118140960795 + 5406804 * 2 ^ 59
def prefixEnd_5406804 : Nat := 4983230072969 + 3 ^ 40 * 5406804 * 2
def baseEnd_5406804 : Nat := 2776289256652169088184567

theorem tailTrace_5406804 : CollatzResearch.WordTrace tailWord_5406804 prefixEnd_5406804 2776289256652169088184567 := by
  unfold tailWord_5406804
  simp only [CollatzResearch.WordTrace]
  refine ⟨98601171352039995725997733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131468228469386660967996977 98601171352039995725997733)
  ·
    refine ⟨18487719628507499198624575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98601171352039995725997733 18487719628507499198624575)
    ·
      refine ⟨27731579442761248797936863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18487719628507499198624575 27731579442761248797936863)
      ·
        refine ⟨41597369164141873196905295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27731579442761248797936863 41597369164141873196905295)
        ·
          refine ⟨62396053746212809795357943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41597369164141873196905295 62396053746212809795357943)
          ·
            refine ⟨93594080619319214693036915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62396053746212809795357943 93594080619319214693036915)
            ·
              refine ⟨140391120928978822039555373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93594080619319214693036915 140391120928978822039555373)
              ·
                refine ⟨52646670348367058264833265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140391120928978822039555373 52646670348367058264833265)
                ·
                  refine ⟨39485002761275293698624949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52646670348367058264833265 39485002761275293698624949)
                  ·
                    refine ⟨3701719008869558784246089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39485002761275293698624949 3701719008869558784246089)
                    ·
                      refine ⟨2776289256652169088184567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701719008869558784246089 2776289256652169088184567)
                      ·
                        rfl

theorem cell23_5406804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_5406804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406804 prefixEnd_5406804 := by exact prefixLift 5406804
  have htrace : WordTrace (prefixWord ++ tailWord_5406804) baseStart_5406804 baseEnd_5406804 := by
    simpa [prefixWord, tailWord_5406804, baseEnd_5406804] using wordTrace_append hprefix tailTrace_5406804
  have hstable : (prefixWord ++ tailWord_5406804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406804).length < 2 ^ (prefixWord ++ tailWord_5406804).sum := by decide
  have hdescent : baseEnd_5406804 < baseStart_5406804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406817 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_5406817 : Nat := 118140960795 + 5406817 * 2 ^ 59
def prefixEnd_5406817 : Nat := 4983230072969 + 3 ^ 40 * 5406817 * 2
def baseEnd_5406817 : Nat := 2776295931900677537322007

theorem tailTrace_5406817 : CollatzResearch.WordTrace tailWord_5406817 prefixEnd_5406817 2776295931900677537322007 := by
  unfold tailWord_5406817
  simp only [CollatzResearch.WordTrace]
  refine ⟨197202816853032894672218705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131468544568688596448145803 197202816853032894672218705)
  ·
    refine ⟨147902112639774671004164029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197202816853032894672218705 147902112639774671004164029)
    ·
      refine ⟨55463292239915501626561511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147902112639774671004164029 55463292239915501626561511)
      ·
        refine ⟨83194938359873252439842267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55463292239915501626561511 83194938359873252439842267)
        ·
          refine ⟨124792407539809878659763401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83194938359873252439842267 124792407539809878659763401)
          ·
            refine ⟨93594305654857408994822551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124792407539809878659763401 93594305654857408994822551)
            ·
              refine ⟨140391458482286113492233827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93594305654857408994822551 140391458482286113492233827)
              ·
                refine ⟨210587187723429170238350741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140391458482286113492233827 210587187723429170238350741)
                ·
                  refine ⟨9871274424535742354922691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210587187723429170238350741 9871274424535742354922691)
                  ·
                    refine ⟨14806911636803613532384037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9871274424535742354922691 14806911636803613532384037)
                    ·
                      refine ⟨2776295931900677537322007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14806911636803613532384037 2776295931900677537322007)
                      ·
                        rfl

theorem cell23_5406817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_5406817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406817 prefixEnd_5406817 := by exact prefixLift 5406817
  have htrace : WordTrace (prefixWord ++ tailWord_5406817) baseStart_5406817 baseEnd_5406817 := by
    simpa [prefixWord, tailWord_5406817, baseEnd_5406817] using wordTrace_append hprefix tailTrace_5406817
  have hstable : (prefixWord ++ tailWord_5406817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406817).length < 2 ^ (prefixWord ++ tailWord_5406817).sum := by decide
  have hdescent : baseEnd_5406817 < baseStart_5406817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406834 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5406834 : Nat := 118140960795 + 5406834 * 2 ^ 59
def prefixEnd_5406834 : Nat := 4983230072969 + 3 ^ 40 * 5406834 * 2
def baseEnd_5406834 : Nat := 2776304661071803970809429

theorem tailTrace_5406834 : CollatzResearch.WordTrace tailWord_5406834 prefixEnd_5406834 2776304661071803970809429 := by
  unfold tailWord_5406834
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300859223492826643896889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131468957929314204383725037 49300859223492826643896889)
  ·
    refine ⟨36975644417619619982922667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49300859223492826643896889 36975644417619619982922667)
    ·
      refine ⟨55463466626429429974384001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36975644417619619982922667 55463466626429429974384001)
      ·
        refine ⟨41597599969822072480788001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55463466626429429974384001 41597599969822072480788001)
        ·
          refine ⟨31198199977366554360591001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41597599969822072480788001 31198199977366554360591001)
          ·
            refine ⟨23398649983024915770443251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31198199977366554360591001 23398649983024915770443251)
            ·
              refine ⟨35097974974537373655664877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23398649983024915770443251 35097974974537373655664877)
              ·
                refine ⟨13161740615451515120874329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35097974974537373655664877 13161740615451515120874329)
                ·
                  refine ⟨9871305461588636340655747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13161740615451515120874329 9871305461588636340655747)
                  ·
                    refine ⟨14806958192382954510983621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9871305461588636340655747 14806958192382954510983621)
                    ·
                      refine ⟨2776304661071803970809429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14806958192382954510983621 2776304661071803970809429)
                      ·
                        rfl

theorem cell23_5406834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5406834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406834 prefixEnd_5406834 := by exact prefixLift 5406834
  have htrace : WordTrace (prefixWord ++ tailWord_5406834) baseStart_5406834 baseEnd_5406834 := by
    simpa [prefixWord, tailWord_5406834, baseEnd_5406834] using wordTrace_append hprefix tailTrace_5406834
  have hstable : (prefixWord ++ tailWord_5406834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406834).length < 2 ^ (prefixWord ++ tailWord_5406834).sum := by decide
  have hdescent : baseEnd_5406834 < baseStart_5406834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406867 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3]
def baseStart_5406867 : Nat := 118140960795 + 5406867 * 2 ^ 59
def prefixEnd_5406867 : Nat := 4983230072969 + 3 ^ 40 * 5406867 * 2
def baseEnd_5406867 : Nat := 2776321605933402341696777

theorem tailTrace_5406867 : CollatzResearch.WordTrace tailWord_5406867 prefixEnd_5406867 2776321605933402341696777 := by
  unfold tailWord_5406867
  simp only [CollatzResearch.WordTrace]
  refine ⟨197204640502851753211538855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131469760335234502141025903 197204640502851753211538855)
  ·
    refine ⟨295806960754277629817308283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197204640502851753211538855 295806960754277629817308283)
    ·
      refine ⟨443710441131416444725962425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295806960754277629817308283 443710441131416444725962425)
      ·
        refine ⟨332782830848562333544471819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443710441131416444725962425 332782830848562333544471819)
        ·
          refine ⟨499174246272843500316707729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332782830848562333544471819 499174246272843500316707729)
          ·
            refine ⟨374380684704632625237530797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499174246272843500316707729 374380684704632625237530797)
            ·
              refine ⟨140392756764237234464074049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374380684704632625237530797 140392756764237234464074049)
              ·
                refine ⟨105294567573177925848055537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140392756764237234464074049 105294567573177925848055537)
                ·
                  refine ⟨78970925679883444386041653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105294567573177925848055537 78970925679883444386041653)
                  ·
                    refine ⟨7403524282489072911191405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78970925679883444386041653 7403524282489072911191405)
                    ·
                      refine ⟨2776321605933402341696777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7403524282489072911191405 2776321605933402341696777)
                      ·
                        rfl

theorem cell23_5406867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_5406867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406867 prefixEnd_5406867 := by exact prefixLift 5406867
  have htrace : WordTrace (prefixWord ++ tailWord_5406867) baseStart_5406867 baseEnd_5406867 := by
    simpa [prefixWord, tailWord_5406867, baseEnd_5406867] using wordTrace_append hprefix tailTrace_5406867
  have hstable : (prefixWord ++ tailWord_5406867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406867).length < 2 ^ (prefixWord ++ tailWord_5406867).sum := by decide
  have hdescent : baseEnd_5406867 < baseStart_5406867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406878 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_5406878 : Nat := 118140960795 + 5406878 * 2 ^ 59
def prefixEnd_5406878 : Nat := 4983230072969 + 3 ^ 40 * 5406878 * 2
def baseEnd_5406878 : Nat := 925442418073533932886409

theorem tailTrace_5406878 : CollatzResearch.WordTrace tailWord_5406878 prefixEnd_5406878 925442418073533932886409 := by
  unfold tailWord_5406878
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650630213226487761273661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131470027803874601393459525 24650630213226487761273661)
  ·
    refine ⟨9243986329959932910477623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24650630213226487761273661 9243986329959932910477623)
    ·
      refine ⟨13865979494939899365716435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9243986329959932910477623 13865979494939899365716435)
      ·
        refine ⟨20798969242409849048574653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865979494939899365716435 20798969242409849048574653)
        ·
          refine ⟨7799613465903693393215495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20798969242409849048574653 7799613465903693393215495)
          ·
            refine ⟨11699420198855540089823243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7799613465903693393215495 11699420198855540089823243)
            ·
              refine ⟨17549130298283310134734865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11699420198855540089823243 17549130298283310134734865)
              ·
                refine ⟨13161847723712482601051149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17549130298283310134734865 13161847723712482601051149)
                ·
                  refine ⟨4935692896392180975394181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13161847723712482601051149 4935692896392180975394181)
                  ·
                    refine ⟨925442418073533932886409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935692896392180975394181 925442418073533932886409)
                    ·
                      rfl

theorem cell23_5406878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_5406878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406878 prefixEnd_5406878 := by exact prefixLift 5406878
  have htrace : WordTrace (prefixWord ++ tailWord_5406878) baseStart_5406878 baseEnd_5406878 := by
    simpa [prefixWord, tailWord_5406878, baseEnd_5406878] using wordTrace_append hprefix tailTrace_5406878
  have hstable : (prefixWord ++ tailWord_5406878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406878).length < 2 ^ (prefixWord ++ tailWord_5406878).sum := by decide
  have hdescent : baseEnd_5406878 < baseStart_5406878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406904 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_5406904 : Nat := 118140960795 + 5406904 * 2 ^ 59
def prefixEnd_5406904 : Nat := 4983230072969 + 3 ^ 40 * 5406904 * 2
def baseEnd_5406904 : Nat := 925446868239206232311369

theorem tailTrace_5406904 : CollatzResearch.WordTrace tailWord_5406904 prefixEnd_5406904 925446868239206232311369 := by
  unfold tailWord_5406904
  simp only [CollatzResearch.WordTrace]
  refine ⟨98602995001858854265317883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131470660002478472353757177 98602995001858854265317883)
  ·
    refine ⟨147904492502788281397976825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98602995001858854265317883 147904492502788281397976825)
    ·
      refine ⟨110928369377091211048482619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147904492502788281397976825 110928369377091211048482619)
      ·
        refine ⟨166392554065636816572723929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110928369377091211048482619 166392554065636816572723929)
        ·
          refine ⟨124794415549227612429542947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166392554065636816572723929 124794415549227612429542947)
          ·
            refine ⟨187191623323841418644314421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124794415549227612429542947 187191623323841418644314421)
            ·
              refine ⟨17549214686610132997904477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187191623323841418644314421 17549214686610132997904477)
              ·
                refine ⟨6580955507478799874214179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17549214686610132997904477 6580955507478799874214179)
                ·
                  refine ⟨9871433261218199811321269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580955507478799874214179 9871433261218199811321269)
                  ·
                    refine ⟨925446868239206232311369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9871433261218199811321269 925446868239206232311369)
                    ·
                      rfl

theorem cell23_5406904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_5406904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406904 prefixEnd_5406904 := by exact prefixLift 5406904
  have htrace : WordTrace (prefixWord ++ tailWord_5406904) baseStart_5406904 baseEnd_5406904 := by
    simpa [prefixWord, tailWord_5406904, baseEnd_5406904] using wordTrace_append hprefix tailTrace_5406904
  have hstable : (prefixWord ++ tailWord_5406904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406904).length < 2 ^ (prefixWord ++ tailWord_5406904).sum := by decide
  have hdescent : baseEnd_5406904 < baseStart_5406904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406908 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 6]
def baseStart_5406908 : Nat := 118140960795 + 5406908 * 2 ^ 59
def prefixEnd_5406908 : Nat := 4983230072969 + 3 ^ 40 * 5406908 * 2
def baseEnd_5406908 : Nat := 308482517626692964587121

theorem tailTrace_5406908 : CollatzResearch.WordTrace tailWord_5406908 prefixEnd_5406908 308482517626692964587121 := by
  unfold tailWord_5406908
  simp only [CollatzResearch.WordTrace]
  refine ⟨98603067947851608606890689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131470757263802144809187585 98603067947851608606890689)
  ·
    refine ⟨73952300960888706455168017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98603067947851608606890689 73952300960888706455168017)
    ·
      refine ⟨55464225720666529841376013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73952300960888706455168017 55464225720666529841376013)
      ·
        refine ⟨20799084645249948690516005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55464225720666529841376013 20799084645249948690516005)
        ·
          refine ⟨3899828370984365379471751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20799084645249948690516005 3899828370984365379471751)
          ·
            refine ⟨5849742556476548069207627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899828370984365379471751 5849742556476548069207627)
            ·
              refine ⟨8774613834714822103811441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849742556476548069207627 8774613834714822103811441)
              ·
                refine ⟨6580960376036116577858581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774613834714822103811441 6580960376036116577858581)
                ·
                  refine ⟨308482517626692964587121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6580960376036116577858581 308482517626692964587121)
                  ·
                    rfl

theorem cell23_5406908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_5406908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406908 prefixEnd_5406908 := by exact prefixLift 5406908
  have htrace : WordTrace (prefixWord ++ tailWord_5406908) baseStart_5406908 baseEnd_5406908 := by
    simpa [prefixWord, tailWord_5406908, baseEnd_5406908] using wordTrace_append hprefix tailTrace_5406908
  have hstable : (prefixWord ++ tailWord_5406908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406908).length < 2 ^ (prefixWord ++ tailWord_5406908).sum := by decide
  have hdescent : baseEnd_5406908 < baseStart_5406908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406917 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_5406917 : Nat := 118140960795 + 5406917 * 2 ^ 59
def prefixEnd_5406917 : Nat := 4983230072969 + 3 ^ 40 * 5406917 * 2
def baseEnd_5406917 : Nat := 925449093322042382023849

theorem tailTrace_5406917 : CollatzResearch.WordTrace tailWord_5406917 prefixEnd_5406917 925449093322042382023849 := by
  unfold tailWord_5406917
  simp only [CollatzResearch.WordTrace]
  refine ⟨197206464152670611750859005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131470976101780407833906003 197206464152670611750859005)
  ·
    refine ⟨73952424057251479406572127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197206464152670611750859005 73952424057251479406572127)
    ·
      refine ⟨110928636085877219109858191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73952424057251479406572127 110928636085877219109858191)
      ·
        refine ⟨166392954128815828664787287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110928636085877219109858191 166392954128815828664787287)
        ·
          refine ⟨249589431193223742997180931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166392954128815828664787287 249589431193223742997180931)
          ·
            refine ⟨374384146789835614495771397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249589431193223742997180931 374384146789835614495771397)
            ·
              refine ⟨70197027523094177717957137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374384146789835614495771397 70197027523094177717957137)
              ·
                refine ⟨52647770642320633288467853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70197027523094177717957137 52647770642320633288467853)
                ·
                  refine ⟨19742913990870237483175445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52647770642320633288467853 19742913990870237483175445)
                  ·
                    refine ⟨925449093322042382023849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19742913990870237483175445 925449093322042382023849)
                    ·
                      rfl

theorem cell23_5406917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_5406917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406917 prefixEnd_5406917 := by exact prefixLift 5406917
  have htrace : WordTrace (prefixWord ++ tailWord_5406917) baseStart_5406917 baseEnd_5406917 := by
    simpa [prefixWord, tailWord_5406917, baseEnd_5406917] using wordTrace_append hprefix tailTrace_5406917
  have hstable : (prefixWord ++ tailWord_5406917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406917).length < 2 ^ (prefixWord ++ tailWord_5406917).sum := by decide
  have hdescent : baseEnd_5406917 < baseStart_5406917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406946 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5406946 : Nat := 118140960795 + 5406946 * 2 ^ 59
def prefixEnd_5406946 : Nat := 4983230072969 + 3 ^ 40 * 5406946 * 2
def baseEnd_5406946 : Nat := 925454056968369177536305

theorem tailTrace_5406946 : CollatzResearch.WordTrace tailWord_5406946 prefixEnd_5406946 925454056968369177536305 := by
  unfold tailWord_5406946
  simp only [CollatzResearch.WordTrace]
  refine ⟨49301880467391387425916173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131471681246377033135776461 49301880467391387425916173)
  ·
    refine ⟨18488205175271770284718565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49301880467391387425916173 18488205175271770284718565)
    ·
      refine ⟨3466538470363456928384731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18488205175271770284718565 3466538470363456928384731)
      ·
        refine ⟨5199807705545185392577097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466538470363456928384731 5199807705545185392577097)
        ·
          refine ⟨3899855779158889044432823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199807705545185392577097 3899855779158889044432823)
          ·
            refine ⟨5849783668738333566649235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899855779158889044432823 5849783668738333566649235)
            ·
              refine ⟨8774675503107500349973853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849783668738333566649235 8774675503107500349973853)
              ·
                refine ⟨3290503313665312631240195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8774675503107500349973853 3290503313665312631240195)
                ·
                  refine ⟨4935754970497968946860293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290503313665312631240195 4935754970497968946860293)
                  ·
                    refine ⟨925454056968369177536305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935754970497968946860293 925454056968369177536305)
                    ·
                      rfl

theorem cell23_5406946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5406946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406946 prefixEnd_5406946 := by exact prefixLift 5406946
  have htrace : WordTrace (prefixWord ++ tailWord_5406946) baseStart_5406946 baseEnd_5406946 := by
    simpa [prefixWord, tailWord_5406946, baseEnd_5406946] using wordTrace_append hprefix tailTrace_5406946
  have hstable : (prefixWord ++ tailWord_5406946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406946).length < 2 ^ (prefixWord ++ tailWord_5406946).sum := by decide
  have hdescent : baseEnd_5406946 < baseStart_5406946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406951 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 4, 4]
def baseStart_5406951 : Nat := 118140960795 + 5406951 * 2 ^ 59
def prefixEnd_5406951 : Nat := 4983230072969 + 3 ^ 40 * 5406951 * 2
def baseEnd_5406951 : Nat := 925454912769460004348797

theorem tailTrace_5406951 : CollatzResearch.WordTrace tailWord_5406951 prefixEnd_5406951 925454912769460004348797 := by
  unfold tailWord_5406951
  simp only [CollatzResearch.WordTrace]
  refine ⟨197207704234547435557596707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131471802823031623705064471 197207704234547435557596707)
  ·
    refine ⟨295811556351821153336395061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197207704234547435557596707 295811556351821153336395061)
    ·
      refine ⟨27732333407983233125287037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295811556351821153336395061 27732333407983233125287037)
      ·
        refine ⟨10399625027993712421982639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27732333407983233125287037 10399625027993712421982639)
        ·
          refine ⟨15599437541990568632973959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399625027993712421982639 15599437541990568632973959)
          ·
            refine ⟨23399156312985852949460939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15599437541990568632973959 23399156312985852949460939)
            ·
              refine ⟨35098734469478779424191409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23399156312985852949460939 35098734469478779424191409)
              ·
                refine ⟨26324050852109084568143557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35098734469478779424191409 26324050852109084568143557)
                ·
                  refine ⟨4935759534770453356526917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26324050852109084568143557 4935759534770453356526917)
                  ·
                    refine ⟨925454912769460004348797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935759534770453356526917 925454912769460004348797)
                    ·
                      rfl

theorem cell23_5406951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_5406951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406951 prefixEnd_5406951 := by exact prefixLift 5406951
  have htrace : WordTrace (prefixWord ++ tailWord_5406951) baseStart_5406951 baseEnd_5406951 := by
    simpa [prefixWord, tailWord_5406951, baseEnd_5406951] using wordTrace_append hprefix tailTrace_5406951
  have hstable : (prefixWord ++ tailWord_5406951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406951).length < 2 ^ (prefixWord ++ tailWord_5406951).sum := by decide
  have hdescent : baseEnd_5406951 < baseStart_5406951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406954 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5406954 : Nat := 118140960795 + 5406954 * 2 ^ 59
def prefixEnd_5406954 : Nat := 4983230072969 + 3 ^ 40 * 5406954 * 2
def baseEnd_5406954 : Nat := 2776366278750343501308877

theorem tailTrace_5406954 : CollatzResearch.WordTrace tailWord_5406954 prefixEnd_5406954 2776366278750343501308877 := by
  unfold tailWord_5406954
  simp only [CollatzResearch.WordTrace]
  refine ⟨49301953413384141767488979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131471875769024378046637277 49301953413384141767488979)
  ·
    refine ⟨73952930120076212651233469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49301953413384141767488979 73952930120076212651233469)
    ·
      refine ⟨27732348795028579744212551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73952930120076212651233469 27732348795028579744212551)
      ·
        refine ⟨41598523192542869616318827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27732348795028579744212551 41598523192542869616318827)
        ·
          refine ⟨62397784788814304424478241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41598523192542869616318827 62397784788814304424478241)
          ·
            refine ⟨46798338591610728318358681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62397784788814304424478241 46798338591610728318358681)
            ·
              refine ⟨35098753943708046238769011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46798338591610728318358681 35098753943708046238769011)
              ·
                refine ⟨52648130915562069358153517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35098753943708046238769011 52648130915562069358153517)
                ·
                  refine ⟨19743049093335776009307569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52648130915562069358153517 19743049093335776009307569)
                  ·
                    refine ⟨14807286820001832006980677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19743049093335776009307569 14807286820001832006980677)
                    ·
                      refine ⟨2776366278750343501308877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14807286820001832006980677 2776366278750343501308877)
                      ·
                        rfl

theorem cell23_5406954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5406954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406954 prefixEnd_5406954 := by exact prefixLift 5406954
  have htrace : WordTrace (prefixWord ++ tailWord_5406954) baseStart_5406954 baseEnd_5406954 := by
    simpa [prefixWord, tailWord_5406954, baseEnd_5406954] using wordTrace_append hprefix tailTrace_5406954
  have hstable : (prefixWord ++ tailWord_5406954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406954).length < 2 ^ (prefixWord ++ tailWord_5406954).sum := by decide
  have hdescent : baseEnd_5406954 < baseStart_5406954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406961 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_5406961 : Nat := 118140960795 + 5406961 * 2 ^ 59
def prefixEnd_5406961 : Nat := 4983230072969 + 3 ^ 40 * 5406961 * 2
def baseEnd_5406961 : Nat := 2776369873114924973921345

theorem tailTrace_5406961 : CollatzResearch.WordTrace tailWord_5406961 prefixEnd_5406961 2776369873114924973921345 := by
  unfold tailWord_5406961
  simp only [CollatzResearch.WordTrace]
  refine ⟨197208068964511207265460737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131472045976340804843640491 197208068964511207265460737)
  ·
    refine ⟨147906051723383405449095553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197208068964511207265460737 147906051723383405449095553)
    ·
      refine ⟨110929538792537554086821665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147906051723383405449095553 110929538792537554086821665)
      ·
        refine ⟨83197154094403165565116249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110929538792537554086821665 83197154094403165565116249)
        ·
          refine ⟨62397865570802374173837187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83197154094403165565116249 62397865570802374173837187)
          ·
            refine ⟨93596798356203561260755781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62397865570802374173837187 93596798356203561260755781)
            ·
              refine ⟨17549399691788167736391709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93596798356203561260755781 17549399691788167736391709)
              ·
                refine ⟨6581024884420562901146891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17549399691788167736391709 6581024884420562901146891)
                ·
                  refine ⟨9871537326630844351720337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6581024884420562901146891 9871537326630844351720337)
                  ·
                    refine ⟨7403652994973133263790253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9871537326630844351720337 7403652994973133263790253)
                    ·
                      refine ⟨2776369873114924973921345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7403652994973133263790253 2776369873114924973921345)
                      ·
                        rfl

theorem cell23_5406961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_5406961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406961 prefixEnd_5406961 := by exact prefixLift 5406961
  have htrace : WordTrace (prefixWord ++ tailWord_5406961) baseStart_5406961 baseEnd_5406961 := by
    simpa [prefixWord, tailWord_5406961, baseEnd_5406961] using wordTrace_append hprefix tailTrace_5406961
  have hstable : (prefixWord ++ tailWord_5406961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406961).length < 2 ^ (prefixWord ++ tailWord_5406961).sum := by decide
  have hdescent : baseEnd_5406961 < baseStart_5406961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5406967 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_5406967 : Nat := 118140960795 + 5406967 * 2 ^ 59
def prefixEnd_5406967 : Nat := 4983230072969 + 3 ^ 40 * 5406967 * 2
def baseEnd_5406967 : Nat := 2776372953998851950446317

theorem tailTrace_5406967 : CollatzResearch.WordTrace tailWord_5406967 prefixEnd_5406967 2776372953998851950446317 := by
  unfold tailWord_5406967
  simp only [CollatzResearch.WordTrace]
  refine ⟨197208287802489470290179155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131472191868326313526786103 197208287802489470290179155)
  ·
    refine ⟨295812431703734205435268733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197208287802489470290179155 295812431703734205435268733)
    ·
      refine ⟨110929661888900327038225775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295812431703734205435268733 110929661888900327038225775)
      ·
        refine ⟨166394492833350490557338663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110929661888900327038225775 166394492833350490557338663)
        ·
          refine ⟨249591739250025735836007995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166394492833350490557338663 249591739250025735836007995)
          ·
            refine ⟨374387608875038603754011993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249591739250025735836007995 374387608875038603754011993)
            ·
              refine ⟨280790706656278952815508995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374387608875038603754011993 280790706656278952815508995)
              ·
                refine ⟨421186059984418429223263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280790706656278952815508995 421186059984418429223263493)
                ·
                  refine ⟨78972386247078455479361905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421186059984418429223263493 78972386247078455479361905)
                  ·
                    refine ⟨59229289685308841609521429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78972386247078455479361905 59229289685308841609521429)
                    ·
                      refine ⟨2776372953998851950446317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59229289685308841609521429 2776372953998851950446317)
                      ·
                        rfl

theorem cell23_5406967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_5406967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5406967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5406967 prefixEnd_5406967 := by exact prefixLift 5406967
  have htrace : WordTrace (prefixWord ++ tailWord_5406967) baseStart_5406967 baseEnd_5406967 := by
    simpa [prefixWord, tailWord_5406967, baseEnd_5406967] using wordTrace_append hprefix tailTrace_5406967
  have hstable : (prefixWord ++ tailWord_5406967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5406967).length < 2 ^ (prefixWord ++ tailWord_5406967).sum := by decide
  have hdescent : baseEnd_5406967 < baseStart_5406967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5406967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407025 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_5407025 : Nat := 118140960795 + 5407025 * 2 ^ 59
def prefixEnd_5407025 : Nat := 4983230072969 + 3 ^ 40 * 5407025 * 2
def baseEnd_5407025 : Nat := 2776402735876812723521051

theorem tailTrace_5407025 : CollatzResearch.WordTrace tailWord_5407025 prefixEnd_5407025 2776402735876812723521051 := by
  unfold tailWord_5407025
  simp only [CollatzResearch.WordTrace]
  refine ⟨197210403236279346195790529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131473602157519564130527019 197210403236279346195790529)
  ·
    refine ⟨147907802427209509646842897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197210403236279346195790529 147907802427209509646842897)
    ·
      refine ⟨110930851820407132235132173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147907802427209509646842897 110930851820407132235132173)
      ·
        refine ⟨41599069432652674588174565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110930851820407132235132173 41599069432652674588174565)
        ·
          refine ⟨7799825518622376485282731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41599069432652674588174565 7799825518622376485282731)
          ·
            refine ⟨11699738277933564727924097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7799825518622376485282731 11699738277933564727924097)
            ·
              refine ⟨8774803708450173545943073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11699738277933564727924097 8774803708450173545943073)
              ·
                refine ⟨6581102781337630159457305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774803708450173545943073 6581102781337630159457305)
                ·
                  refine ⟨4935827086003222619592979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581102781337630159457305 4935827086003222619592979)
                  ·
                    refine ⟨7403740629004833929389469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4935827086003222619592979 7403740629004833929389469)
                    ·
                      refine ⟨2776402735876812723521051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7403740629004833929389469 2776402735876812723521051)
                      ·
                        rfl

theorem cell23_5407025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_5407025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407025 prefixEnd_5407025 := by exact prefixLift 5407025
  have htrace : WordTrace (prefixWord ++ tailWord_5407025) baseStart_5407025 baseEnd_5407025 := by
    simpa [prefixWord, tailWord_5407025, baseEnd_5407025] using wordTrace_append hprefix tailTrace_5407025
  have hstable : (prefixWord ++ tailWord_5407025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407025).length < 2 ^ (prefixWord ++ tailWord_5407025).sum := by decide
  have hdescent : baseEnd_5407025 < baseStart_5407025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407026 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_5407026 : Nat := 118140960795 + 5407026 * 2 ^ 59
def prefixEnd_5407026 : Nat := 4983230072969 + 3 ^ 40 * 5407026 * 2
def baseEnd_5407026 : Nat := 2776403249357467219608547

theorem tailTrace_5407026 : CollatzResearch.WordTrace tailWord_5407026 prefixEnd_5407026 2776403249357467219608547 := by
  unfold tailWord_5407026
  simp only [CollatzResearch.WordTrace]
  refine ⟨49302609927318930841644233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131473626472850482244384621 49302609927318930841644233)
  ·
    refine ⟨36976957445489198131233175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49302609927318930841644233 36976957445489198131233175)
    ·
      refine ⟨55465436168233797196849763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36976957445489198131233175 55465436168233797196849763)
      ·
        refine ⟨83198154252350695795274645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55465436168233797196849763 83198154252350695795274645)
        ·
          refine ⟨3899913480578938865403499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83198154252350695795274645 3899913480578938865403499)
          ·
            refine ⟨5849870220868408298105249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899913480578938865403499 5849870220868408298105249)
            ·
              refine ⟨4387402665651306223578937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849870220868408298105249 4387402665651306223578937)
              ·
                refine ⟨3290551999238479667684203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4387402665651306223578937 3290551999238479667684203)
                ·
                  refine ⟨4935827998857719501526305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290551999238479667684203 4935827998857719501526305)
                  ·
                    refine ⟨3701870999143289626144729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935827998857719501526305 3701870999143289626144729)
                    ·
                      refine ⟨2776403249357467219608547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701870999143289626144729 2776403249357467219608547)
                      ·
                        rfl

theorem cell23_5407026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_5407026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407026 prefixEnd_5407026 := by exact prefixLift 5407026
  have htrace : WordTrace (prefixWord ++ tailWord_5407026) baseStart_5407026 baseEnd_5407026 := by
    simpa [prefixWord, tailWord_5407026, baseEnd_5407026] using wordTrace_append hprefix tailTrace_5407026
  have hstable : (prefixWord ++ tailWord_5407026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407026).length < 2 ^ (prefixWord ++ tailWord_5407026).sum := by decide
  have hdescent : baseEnd_5407026 < baseStart_5407026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407071 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 5]
def baseStart_5407071 : Nat := 118140960795 + 5407071 * 2 ^ 59
def prefixEnd_5407071 : Nat := 4983230072969 + 3 ^ 40 * 5407071 * 2
def baseEnd_5407071 : Nat := 308491817331879949282871

theorem tailTrace_5407071 : CollatzResearch.WordTrace tailWord_5407071 prefixEnd_5407071 308491817331879949282871 := by
  unfold tailWord_5407071
  simp only [CollatzResearch.WordTrace]
  refine ⟨197212080994112696051965067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131474720662741797367976711 197212080994112696051965067)
  ·
    refine ⟨295818121491169044077947601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197212080994112696051965067 295818121491169044077947601)
    ·
      refine ⟨221863591118376783058460701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295818121491169044077947601 221863591118376783058460701)
      ·
        refine ⟨83198846669391293646922763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221863591118376783058460701 83198846669391293646922763)
        ·
          refine ⟨124798270004086940470384145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83198846669391293646922763 124798270004086940470384145)
          ·
            refine ⟨93598702503065205352788109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124798270004086940470384145 93598702503065205352788109)
            ·
              refine ⟨35099513438649452007295541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93598702503065205352788109 35099513438649452007295541)
              ·
                refine ⟨3290579384873386125683957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35099513438649452007295541 3290579384873386125683957)
                ·
                  refine ⟨308491817331879949282871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290579384873386125683957 308491817331879949282871)
                  ·
                    rfl

theorem cell23_5407071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 5].length) (baseStart_5407071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407071 prefixEnd_5407071 := by exact prefixLift 5407071
  have htrace : WordTrace (prefixWord ++ tailWord_5407071) baseStart_5407071 baseEnd_5407071 := by
    simpa [prefixWord, tailWord_5407071, baseEnd_5407071] using wordTrace_append hprefix tailTrace_5407071
  have hstable : (prefixWord ++ tailWord_5407071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407071).length < 2 ^ (prefixWord ++ tailWord_5407071).sum := by decide
  have hdescent : baseEnd_5407071 < baseStart_5407071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407082 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5407082 : Nat := 118140960795 + 5407082 * 2 ^ 59
def prefixEnd_5407082 : Nat := 4983230072969 + 3 ^ 40 * 5407082 * 2
def baseEnd_5407082 : Nat := 2776432004274119000508289

theorem tailTrace_5407082 : CollatzResearch.WordTrace tailWord_5407082 prefixEnd_5407082 2776432004274119000508289 := by
  unfold tailWord_5407082
  simp only [CollatzResearch.WordTrace]
  refine ⟨49303120549268211232653875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131474988131381896620410333 49303120549268211232653875)
  ·
    refine ⟨73954680823902316848980813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49303120549268211232653875 73954680823902316848980813)
    ·
      refine ⟨27733005308963368818367805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73954680823902316848980813 27733005308963368818367805)
      ·
        refine ⟨10399876990861263306887927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27733005308963368818367805 10399876990861263306887927)
        ·
          refine ⟨15599815486291894960331891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399876990861263306887927 15599815486291894960331891)
          ·
            refine ⟨23399723229437842440497837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15599815486291894960331891 23399723229437842440497837)
            ·
              refine ⟨8774896211039190915186689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23399723229437842440497837 8774896211039190915186689)
              ·
                refine ⟨6581172158279393186390017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774896211039190915186689 6581172158279393186390017)
                ·
                  refine ⟨4935879118709544889792513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581172158279393186390017 4935879118709544889792513)
                  ·
                    refine ⟨3701909339032158667344385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935879118709544889792513 3701909339032158667344385)
                    ·
                      refine ⟨2776432004274119000508289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3701909339032158667344385 2776432004274119000508289)
                      ·
                        rfl

theorem cell23_5407082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5407082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407082 prefixEnd_5407082 := by exact prefixLift 5407082
  have htrace : WordTrace (prefixWord ++ tailWord_5407082) baseStart_5407082 baseEnd_5407082 := by
    simpa [prefixWord, tailWord_5407082, baseEnd_5407082] using wordTrace_append hprefix tailTrace_5407082
  have hstable : (prefixWord ++ tailWord_5407082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407082).length < 2 ^ (prefixWord ++ tailWord_5407082).sum := by decide
  have hdescent : baseEnd_5407082 < baseStart_5407082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407138 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_5407138 : Nat := 118140960795 + 5407138 * 2 ^ 59
def prefixEnd_5407138 : Nat := 4983230072969 + 3 ^ 40 * 5407138 * 2
def baseEnd_5407138 : Nat := 2776460759190770781408031

theorem tailTrace_5407138 : CollatzResearch.WordTrace tailWord_5407138 prefixEnd_5407138 2776460759190770781408031 := by
  unfold tailWord_5407138
  simp only [CollatzResearch.WordTrace]
  refine ⟨49303631171217491623663517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131476349789913310996436045 49303631171217491623663517)
  ·
    refine ⟨18488861689206559358873819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49303631171217491623663517 18488861689206559358873819)
    ·
      refine ⟨27733292533809839038310729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18488861689206559358873819 27733292533809839038310729)
      ·
        refine ⟨20799969400357379278733047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27733292533809839038310729 20799969400357379278733047)
        ·
          refine ⟨31199954100536068918099571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20799969400357379278733047 31199954100536068918099571)
          ·
            refine ⟨46799931150804103377149357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31199954100536068918099571 46799931150804103377149357)
            ·
              refine ⟨17549974181551538766431009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46799931150804103377149357 17549974181551538766431009)
              ·
                refine ⟨13162480636163654074823257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17549974181551538766431009 13162480636163654074823257)
                ·
                  refine ⟨9871860477122740556117443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13162480636163654074823257 9871860477122740556117443)
                  ·
                    refine ⟨14807790715684110834176165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9871860477122740556117443 14807790715684110834176165)
                    ·
                      refine ⟨2776460759190770781408031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14807790715684110834176165 2776460759190770781408031)
                      ·
                        rfl

theorem cell23_5407138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_5407138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407138 prefixEnd_5407138 := by exact prefixLift 5407138
  have htrace : WordTrace (prefixWord ++ tailWord_5407138) baseStart_5407138 baseEnd_5407138 := by
    simpa [prefixWord, tailWord_5407138, baseEnd_5407138] using wordTrace_append hprefix tailTrace_5407138
  have hstable : (prefixWord ++ tailWord_5407138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407138).length < 2 ^ (prefixWord ++ tailWord_5407138).sum := by decide
  have hdescent : baseEnd_5407138 < baseStart_5407138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407211 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4]
def baseStart_5407211 : Nat := 118140960795 + 5407211 * 2 ^ 59
def prefixEnd_5407211 : Nat := 4983230072969 + 3 ^ 40 * 5407211 * 2
def baseEnd_5407211 : Nat := 2776498243278548995795195

theorem tailTrace_5407211 : CollatzResearch.WordTrace tailWord_5407211 prefixEnd_5407211 2776498243278548995795195 := by
  unfold tailWord_5407211
  simp only [CollatzResearch.WordTrace]
  refine ⟨197217187213605499962061487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131478124809070333308040991 197217187213605499962061487)
  ·
    refine ⟨295825780820408249943092231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197217187213605499962061487 295825780820408249943092231)
    ·
      refine ⟨443738671230612374914638347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295825780820408249943092231 443738671230612374914638347)
      ·
        refine ⟨665608006845918562371957521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443738671230612374914638347 665608006845918562371957521)
        ·
          refine ⟨499206005134438921778968141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665608006845918562371957521 499206005134438921778968141)
          ·
            refine ⟨187202251925414595667113053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499206005134438921778968141 187202251925414595667113053)
            ·
              refine ⟨70200844472030473375167395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187202251925414595667113053 70200844472030473375167395)
              ·
                refine ⟨105301266708045710062751093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70200844472030473375167395 105301266708045710062751093)
                ·
                  refine ⟨9871993753879285318382915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105301266708045710062751093 9871993753879285318382915)
                  ·
                    refine ⟨14807990630818927977574373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9871993753879285318382915 14807990630818927977574373)
                    ·
                      refine ⟨2776498243278548995795195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14807990630818927977574373 2776498243278548995795195)
                      ·
                        rfl

theorem cell23_5407211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 4].length) (baseStart_5407211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407211 prefixEnd_5407211 := by exact prefixLift 5407211
  have htrace : WordTrace (prefixWord ++ tailWord_5407211) baseStart_5407211 baseEnd_5407211 := by
    simpa [prefixWord, tailWord_5407211, baseEnd_5407211] using wordTrace_append hprefix tailTrace_5407211
  have hstable : (prefixWord ++ tailWord_5407211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407211).length < 2 ^ (prefixWord ++ tailWord_5407211).sum := by decide
  have hdescent : baseEnd_5407211 < baseStart_5407211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407228 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 1, 1, 4]
def baseStart_5407228 : Nat := 118140960795 + 5407228 * 2 ^ 59
def prefixEnd_5407228 : Nat := 4983230072969 + 3 ^ 40 * 5407228 * 2
def baseEnd_5407228 : Nat := 2776506972449675429282617

theorem tailTrace_5407228 : CollatzResearch.WordTrace tailWord_5407228 prefixEnd_5407228 2776506972449675429282617 := by
  unfold tailWord_5407228
  simp only [CollatzResearch.WordTrace]
  refine ⟨98608903627271955932715169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131478538169695941243620225 98608903627271955932715169)
  ·
    refine ⟨73956677720453966949536377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98608903627271955932715169 73956677720453966949536377)
    ·
      refine ⟨55467508290340475212152283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73956677720453966949536377 55467508290340475212152283)
      ·
        refine ⟨83201262435510712818228425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55467508290340475212152283 83201262435510712818228425)
        ·
          refine ⟨62400946826633034613671319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83201262435510712818228425 62400946826633034613671319)
          ·
            refine ⟨93601420239949551920506979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62400946826633034613671319 93601420239949551920506979)
            ·
              refine ⟨140402130359924327880760469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93601420239949551920506979 140402130359924327880760469)
              ·
                refine ⟨6581349860621452869410647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140402130359924327880760469 6581349860621452869410647)
                ·
                  refine ⟨9872024790932179304115971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6581349860621452869410647 9872024790932179304115971)
                  ·
                    refine ⟨14808037186398268956173957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9872024790932179304115971 14808037186398268956173957)
                    ·
                      refine ⟨2776506972449675429282617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14808037186398268956173957 2776506972449675429282617)
                      ·
                        rfl

theorem cell23_5407228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_5407228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407228 prefixEnd_5407228 := by exact prefixLift 5407228
  have htrace : WordTrace (prefixWord ++ tailWord_5407228) baseStart_5407228 baseEnd_5407228 := by
    simpa [prefixWord, tailWord_5407228, baseEnd_5407228] using wordTrace_append hprefix tailTrace_5407228
  have hstable : (prefixWord ++ tailWord_5407228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407228).length < 2 ^ (prefixWord ++ tailWord_5407228).sum := by decide
  have hdescent : baseEnd_5407228 < baseStart_5407228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407239 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_5407239 : Nat := 118140960795 + 5407239 * 2 ^ 59
def prefixEnd_5407239 : Nat := 4983230072969 + 3 ^ 40 * 5407239 * 2
def baseEnd_5407239 : Nat := 2776512620736874886245067

theorem tailTrace_5407239 : CollatzResearch.WordTrace tailWord_5407239 prefixEnd_5407239 2776512620736874886245067 := by
  unfold tailWord_5407239
  simp only [CollatzResearch.WordTrace]
  refine ⟨197218208457504060744080771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131478805638336040496053847 197218208457504060744080771)
  ·
    refine ⟨295827312686256091116121157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197218208457504060744080771 295827312686256091116121157)
    ·
      refine ⟨55467621128673017084272717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295827312686256091116121157 55467621128673017084272717)
      ·
        refine ⟨20800357923252381406602269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55467621128673017084272717 20800357923252381406602269)
        ·
          refine ⟨7800134221219643027475851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20800357923252381406602269 7800134221219643027475851)
          ·
            refine ⟨11700201331829464541213777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7800134221219643027475851 11700201331829464541213777)
            ·
              refine ⟨8775150998872098405910333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11700201331829464541213777 8775150998872098405910333)
              ·
                refine ⟨3290681624577036902216375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8775150998872098405910333 3290681624577036902216375)
                ·
                  refine ⟨4936022436865555353324563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290681624577036902216375 4936022436865555353324563)
                  ·
                    refine ⟨7404033655298333029986845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936022436865555353324563 7404033655298333029986845)
                    ·
                      refine ⟨2776512620736874886245067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404033655298333029986845 2776512620736874886245067)
                      ·
                        rfl

theorem cell23_5407239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_5407239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407239 prefixEnd_5407239 := by exact prefixLift 5407239
  have htrace : WordTrace (prefixWord ++ tailWord_5407239) baseStart_5407239 baseEnd_5407239 := by
    simpa [prefixWord, tailWord_5407239, baseEnd_5407239] using wordTrace_append hprefix tailTrace_5407239
  have hstable : (prefixWord ++ tailWord_5407239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407239).length < 2 ^ (prefixWord ++ tailWord_5407239).sum := by decide
  have hdescent : baseEnd_5407239 < baseStart_5407239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407241 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_5407241 : Nat := 118140960795 + 5407241 * 2 ^ 59
def prefixEnd_5407241 : Nat := 4983230072969 + 3 ^ 40 * 5407241 * 2
def baseEnd_5407241 : Nat := 2776513647698183878420057

theorem tailTrace_5407241 : CollatzResearch.WordTrace tailWord_5407241 prefixEnd_5407241 2776513647698183878420057 := by
  unfold tailWord_5407241
  simp only [CollatzResearch.WordTrace]
  refine ⟨197218281403496815085653577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131478854268997876723769051 197218281403496815085653577)
  ·
    refine ⟨147913711052622611314240183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197218281403496815085653577 147913711052622611314240183)
    ·
      refine ⟨221870566578933916971360275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147913711052622611314240183 221870566578933916971360275)
      ·
        refine ⟨332805849868400875457040413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221870566578933916971360275 332805849868400875457040413)
        ·
          refine ⟨124802193700650328296390155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332805849868400875457040413 124802193700650328296390155)
          ·
            refine ⟨187203290550975492444585233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124802193700650328296390155 187203290550975492444585233)
            ·
              refine ⟨140402467913231619333438925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187203290550975492444585233 140402467913231619333438925)
              ·
                refine ⟨52650925467461857250039597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140402467913231619333438925 52650925467461857250039597)
                ·
                  refine ⟨19744097050298196468764849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52650925467461857250039597 19744097050298196468764849)
                  ·
                    refine ⟨14808072787723647351573637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19744097050298196468764849 14808072787723647351573637)
                    ·
                      refine ⟨2776513647698183878420057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14808072787723647351573637 2776513647698183878420057)
                      ·
                        rfl

theorem cell23_5407241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_5407241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407241 prefixEnd_5407241 := by exact prefixLift 5407241
  have htrace : WordTrace (prefixWord ++ tailWord_5407241) baseStart_5407241 baseEnd_5407241 := by
    simpa [prefixWord, tailWord_5407241, baseEnd_5407241] using wordTrace_append hprefix tailTrace_5407241
  have hstable : (prefixWord ++ tailWord_5407241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407241).length < 2 ^ (prefixWord ++ tailWord_5407241).sum := by decide
  have hdescent : baseEnd_5407241 < baseStart_5407241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407281 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_5407281 : Nat := 118140960795 + 5407281 * 2 ^ 59
def prefixEnd_5407281 : Nat := 4983230072969 + 3 ^ 40 * 5407281 * 2
def baseEnd_5407281 : Nat := 925511395641454573973291

theorem tailTrace_5407281 : CollatzResearch.WordTrace tailWord_5407281 prefixEnd_5407281 925511395641454573973291 := by
  unfold tailWord_5407281
  simp only [CollatzResearch.WordTrace]
  refine ⟨197219740323351901917109697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131479826882234601278073131 197219740323351901917109697)
  ·
    refine ⟨147914805242513926437832273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197219740323351901917109697 147914805242513926437832273)
    ·
      refine ⟨110936103931885444828374205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147914805242513926437832273 110936103931885444828374205)
      ·
        refine ⟨41601038974457041810640327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110936103931885444828374205 41601038974457041810640327)
        ·
          refine ⟨62401558461685562715960491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41601038974457041810640327 62401558461685562715960491)
          ·
            refine ⟨93602337692528344073940737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62401558461685562715960491 93602337692528344073940737)
            ·
              refine ⟨70201753269396258055455553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93602337692528344073940737 70201753269396258055455553)
              ·
                refine ⟨52651314952047193541591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70201753269396258055455553 52651314952047193541591665)
                ·
                  refine ⟨39488486214035395156193749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52651314952047193541591665 39488486214035395156193749)
                  ·
                    refine ⟨925511395641454573973291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39488486214035395156193749 925511395641454573973291)
                    ·
                      rfl

theorem cell23_5407281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_5407281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407281 prefixEnd_5407281 := by exact prefixLift 5407281
  have htrace : WordTrace (prefixWord ++ tailWord_5407281) baseStart_5407281 baseEnd_5407281 := by
    simpa [prefixWord, tailWord_5407281, baseEnd_5407281] using wordTrace_append hprefix tailTrace_5407281
  have hstable : (prefixWord ++ tailWord_5407281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407281).length < 2 ^ (prefixWord ++ tailWord_5407281).sum := by decide
  have hdescent : baseEnd_5407281 < baseStart_5407281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407311 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 4, 6]
def baseStart_5407311 : Nat := 118140960795 + 5407311 * 2 ^ 59
def prefixEnd_5407311 : Nat := 4983230072969 + 3 ^ 40 * 5407311 * 2
def baseEnd_5407311 : Nat := 925516530447999534848245

theorem tailTrace_5407311 : CollatzResearch.WordTrace tailWord_5407311 prefixEnd_5407311 925516530447999534848245 := by
  unfold tailWord_5407311
  simp only [CollatzResearch.WordTrace]
  refine ⟨197220834513243217040701787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131480556342162144693801191 197220834513243217040701787)
  ·
    refine ⟨295831251769864825561052681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197220834513243217040701787 295831251769864825561052681)
    ·
      refine ⟨221873438827398619170789511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295831251769864825561052681 221873438827398619170789511)
      ·
        refine ⟨332810158241097928756184267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221873438827398619170789511 332810158241097928756184267)
        ·
          refine ⟨499215237361646893134276401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332810158241097928756184267 499215237361646893134276401)
          ·
            refine ⟨374411428021235169850707301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499215237361646893134276401 374411428021235169850707301)
            ·
              refine ⟨70202142753981594347007619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374411428021235169850707301 70202142753981594347007619)
              ·
                refine ⟨105303214130972391520511429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70202142753981594347007619 105303214130972391520511429)
                ·
                  refine ⟨19744352649557323410095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105303214130972391520511429 19744352649557323410095893)
                  ·
                    refine ⟨925516530447999534848245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19744352649557323410095893 925516530447999534848245)
                    ·
                      rfl

theorem cell23_5407311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_5407311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407311 prefixEnd_5407311 := by exact prefixLift 5407311
  have htrace : WordTrace (prefixWord ++ tailWord_5407311) baseStart_5407311 baseEnd_5407311 := by
    simpa [prefixWord, tailWord_5407311, baseEnd_5407311] using wordTrace_append hprefix tailTrace_5407311
  have hstable : (prefixWord ++ tailWord_5407311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407311).length < 2 ^ (prefixWord ++ tailWord_5407311).sum := by decide
  have hdescent : baseEnd_5407311 < baseStart_5407311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407329 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_5407329 : Nat := 118140960795 + 5407329 * 2 ^ 59
def prefixEnd_5407329 : Nat := 4983230072969 + 3 ^ 40 * 5407329 * 2
def baseEnd_5407329 : Nat := 2776558833995779534119653

theorem tailTrace_5407329 : CollatzResearch.WordTrace tailWord_5407329 prefixEnd_5407329 2776558833995779534119653 := by
  unfold tailWord_5407329
  simp only [CollatzResearch.WordTrace]
  refine ⟨197221491027178006114857041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131480994018118670743238027 197221491027178006114857041)
  ·
    refine ⟨147916118270383504586142781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197221491027178006114857041 147916118270383504586142781)
    ·
      refine ⟨55468544351393814219803543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147916118270383504586142781 55468544351393814219803543)
      ·
        refine ⟨83202816527090721329705315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55468544351393814219803543 83202816527090721329705315)
        ·
          refine ⟨124804224790636081994557973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83202816527090721329705315 124804224790636081994557973)
          ·
            refine ⟨5850198037061066343494905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124804224790636081994557973 5850198037061066343494905)
            ·
              refine ⟨4387648527795799757621179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5850198037061066343494905 4387648527795799757621179)
              ·
                refine ⟨6581472791693699636431769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387648527795799757621179 6581472791693699636431769)
                ·
                  refine ⟨4936104593770274727323827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581472791693699636431769 4936104593770274727323827)
                  ·
                    refine ⟨7404156890655412090985741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936104593770274727323827 7404156890655412090985741)
                    ·
                      refine ⟨2776558833995779534119653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404156890655412090985741 2776558833995779534119653)
                      ·
                        rfl

theorem cell23_5407329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_5407329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407329 prefixEnd_5407329 := by exact prefixLift 5407329
  have htrace : WordTrace (prefixWord ++ tailWord_5407329) baseStart_5407329 baseEnd_5407329 := by
    simpa [prefixWord, tailWord_5407329, baseEnd_5407329] using wordTrace_append hprefix tailTrace_5407329
  have hstable : (prefixWord ++ tailWord_5407329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407329).length < 2 ^ (prefixWord ++ tailWord_5407329).sum := by decide
  have hdescent : baseEnd_5407329 < baseStart_5407329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407335 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_5407335 : Nat := 118140960795 + 5407335 * 2 ^ 59
def prefixEnd_5407335 : Nat := 4983230072969 + 3 ^ 40 * 5407335 * 2
def baseEnd_5407335 : Nat := 2776561914879706510644625

theorem tailTrace_5407335 : CollatzResearch.WordTrace tailWord_5407335 prefixEnd_5407335 2776561914879706510644625 := by
  unfold tailWord_5407335
  simp only [CollatzResearch.WordTrace]
  refine ⟨197221709865156269139575459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131481139910104179426383639 197221709865156269139575459)
  ·
    refine ⟨295832564797734403709363189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197221709865156269139575459 295832564797734403709363189)
    ·
      refine ⟨27734302949787600347752799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295832564797734403709363189 27734302949787600347752799)
      ·
        refine ⟨41601454424681400521629199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27734302949787600347752799 41601454424681400521629199)
        ·
          refine ⟨62402181637022100782443799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41601454424681400521629199 62402181637022100782443799)
          ·
            refine ⟨93603272455533151173665699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62402181637022100782443799 93603272455533151173665699)
            ·
              refine ⟨140404908683299726760498549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93603272455533151173665699 140404908683299726760498549)
              ·
                refine ⟨13162960189059349383796739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140404908683299726760498549 13162960189059349383796739)
                ·
                  refine ⟨19744440283589024075695109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13162960189059349383796739 19744440283589024075695109)
                  ·
                    refine ⟨3702082553172942014192833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19744440283589024075695109 3702082553172942014192833)
                    ·
                      refine ⟨2776561914879706510644625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702082553172942014192833 2776561914879706510644625)
                      ·
                        rfl

theorem cell23_5407335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_5407335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407335 prefixEnd_5407335 := by exact prefixLift 5407335
  have htrace : WordTrace (prefixWord ++ tailWord_5407335) baseStart_5407335 baseEnd_5407335 := by
    simpa [prefixWord, tailWord_5407335, baseEnd_5407335] using wordTrace_append hprefix tailTrace_5407335
  have hstable : (prefixWord ++ tailWord_5407335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407335).length < 2 ^ (prefixWord ++ tailWord_5407335).sum := by decide
  have hdescent : baseEnd_5407335 < baseStart_5407335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407338 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5407338 : Nat := 118140960795 + 5407338 * 2 ^ 59
def prefixEnd_5407338 : Nat := 4983230072969 + 3 ^ 40 * 5407338 * 2
def baseEnd_5407338 : Nat := 2776563455321669998907111

theorem tailTrace_5407338 : CollatzResearch.WordTrace tailWord_5407338 prefixEnd_5407338 2776563455321669998907111 := by
  unfold tailWord_5407338
  simp only [CollatzResearch.WordTrace]
  refine ⟨49305454821036350162983667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131481212856096933767956445 49305454821036350162983667)
  ·
    refine ⟨73958182231554525244475501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49305454821036350162983667 73958182231554525244475501)
    ·
      refine ⟨27734318336832946966678313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73958182231554525244475501 27734318336832946966678313)
      ·
        refine ⟨20800738752624710225008735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27734318336832946966678313 20800738752624710225008735)
        ·
          refine ⟨31201108128937065337513103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20800738752624710225008735 31201108128937065337513103)
          ·
            refine ⟨46801662193405598006269655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31201108128937065337513103 46801662193405598006269655)
            ·
              refine ⟨70202493290108397009404483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46801662193405598006269655 70202493290108397009404483)
              ·
                refine ⟨105303739935162595514106725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70202493290108397009404483 105303739935162595514106725)
                ·
                  refine ⟨19744451237842986658895011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105303739935162595514106725 19744451237842986658895011)
                  ·
                    refine ⟨29616676856764479988342517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19744451237842986658895011 29616676856764479988342517)
                    ·
                      refine ⟨2776563455321669998907111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29616676856764479988342517 2776563455321669998907111)
                      ·
                        rfl

theorem cell23_5407338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5407338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407338 prefixEnd_5407338 := by exact prefixLift 5407338
  have htrace : WordTrace (prefixWord ++ tailWord_5407338) baseStart_5407338 baseEnd_5407338 := by
    simpa [prefixWord, tailWord_5407338, baseEnd_5407338] using wordTrace_append hprefix tailTrace_5407338
  have hstable : (prefixWord ++ tailWord_5407338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407338).length < 2 ^ (prefixWord ++ tailWord_5407338).sum := by decide
  have hdescent : baseEnd_5407338 < baseStart_5407338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407405 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5407405 : Nat := 118140960795 + 5407405 * 2 ^ 59
def prefixEnd_5407405 : Nat := 4983230072969 + 3 ^ 40 * 5407405 * 2
def baseEnd_5407405 : Nat := 925532619508507078923101

theorem tailTrace_5407405 : CollatzResearch.WordTrace tailWord_5407405 prefixEnd_5407405 925532619508507078923101 := by
  unfold tailWord_5407405
  simp only [CollatzResearch.WordTrace]
  refine ⟨197224262974902671094623669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131482841983268447396415779 197224262974902671094623669)
  ·
    refine ⟨18489774653897125415120969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197224262974902671094623669 18489774653897125415120969)
    ·
      refine ⟨13867330990422844061340727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18489774653897125415120969 13867330990422844061340727)
      ·
        refine ⟨20800996485634266092011091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13867330990422844061340727 20800996485634266092011091)
        ·
          refine ⟨31201494728451399138016637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20800996485634266092011091 31201494728451399138016637)
          ·
            refine ⟨11700560523169274676756239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31201494728451399138016637 11700560523169274676756239)
            ·
              refine ⟨17550840784753912015134359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11700560523169274676756239 17550840784753912015134359)
              ·
                refine ⟨26326261177130868022701539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17550840784753912015134359 26326261177130868022701539)
                ·
                  refine ⟨39489391765696302034052309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26326261177130868022701539 39489391765696302034052309)
                  ·
                    refine ⟨925532619508507078923101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39489391765696302034052309 925532619508507078923101)
                    ·
                      rfl

theorem cell23_5407405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5407405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407405 prefixEnd_5407405 := by exact prefixLift 5407405
  have htrace : WordTrace (prefixWord ++ tailWord_5407405) baseStart_5407405 baseEnd_5407405 := by
    simpa [prefixWord, tailWord_5407405, baseEnd_5407405] using wordTrace_append hprefix tailTrace_5407405
  have hstable : (prefixWord ++ tailWord_5407405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407405).length < 2 ^ (prefixWord ++ tailWord_5407405).sum := by decide
  have hdescent : baseEnd_5407405 < baseStart_5407405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407409 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 5]
def baseStart_5407409 : Nat := 118140960795 + 5407409 * 2 ^ 59
def prefixEnd_5407409 : Nat := 4983230072969 + 3 ^ 40 * 5407409 * 2
def baseEnd_5407409 : Nat := 308511101383126580124365

theorem tailTrace_5407409 : CollatzResearch.WordTrace tailWord_5407409 prefixEnd_5407409 308511101383126580124365 := by
  unfold tailWord_5407409
  simp only [CollatzResearch.WordTrace]
  refine ⟨197224408866888179777769281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131482939244592119851846187 197224408866888179777769281)
  ·
    refine ⟨147918306650166134833326961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197224408866888179777769281 147918306650166134833326961)
    ·
      refine ⟨110938729987624601124995221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147918306650166134833326961 110938729987624601124995221)
      ·
        refine ⟨5200252968169903177734151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110938729987624601124995221 5200252968169903177734151)
        ·
          refine ⟨7800379452254854766601227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200252968169903177734151 7800379452254854766601227)
          ·
            refine ⟨11700569178382282149901841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7800379452254854766601227 11700569178382282149901841)
            ·
              refine ⟨8775426883786711612426381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11700569178382282149901841 8775426883786711612426381)
              ·
                refine ⟨3290785081420016854659893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8775426883786711612426381 3290785081420016854659893)
                ·
                  refine ⟨308511101383126580124365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290785081420016854659893 308511101383126580124365)
                  ·
                    rfl

theorem cell23_5407409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 5].length) (baseStart_5407409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407409 prefixEnd_5407409 := by exact prefixLift 5407409
  have htrace : WordTrace (prefixWord ++ tailWord_5407409) baseStart_5407409 baseEnd_5407409 := by
    simpa [prefixWord, tailWord_5407409, baseEnd_5407409] using wordTrace_append hprefix tailTrace_5407409
  have hstable : (prefixWord ++ tailWord_5407409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407409).length < 2 ^ (prefixWord ++ tailWord_5407409).sum := by decide
  have hdescent : baseEnd_5407409 < baseStart_5407409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407476 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5407476 : Nat := 118140960795 + 5407476 * 2 ^ 59
def prefixEnd_5407476 : Nat := 4983230072969 + 3 ^ 40 * 5407476 * 2
def baseEnd_5407476 : Nat := 2776634315651990458981477

theorem tailTrace_5407476 : CollatzResearch.WordTrace tailWord_5407476 prefixEnd_5407476 2776634315651990458981477 := by
  unfold tailWord_5407476
  simp only [CollatzResearch.WordTrace]
  refine ⟨98613426278822725110229141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131484568371763633480305521 98613426278822725110229141)
  ·
    refine ⟨4622504356819815239541991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98613426278822725110229141 4622504356819815239541991)
    ·
      refine ⟨6933756535229722859312987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4622504356819815239541991 6933756535229722859312987)
      ·
        refine ⟨10400634802844584288969481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6933756535229722859312987 10400634802844584288969481)
        ·
          refine ⟨7800476102133438216727111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10400634802844584288969481 7800476102133438216727111)
          ·
            refine ⟨11700714153200157325090667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7800476102133438216727111 11700714153200157325090667)
            ·
              refine ⟨17551071229800235987636001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11700714153200157325090667 17551071229800235987636001)
              ·
                refine ⟨13163303422350176990727001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17551071229800235987636001 13163303422350176990727001)
                ·
                  refine ⟨9872477566762632743045251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13163303422350176990727001 9872477566762632743045251)
                  ·
                    refine ⟨14808716350143949114567877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9872477566762632743045251 14808716350143949114567877)
                    ·
                      refine ⟨2776634315651990458981477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14808716350143949114567877 2776634315651990458981477)
                      ·
                        rfl

theorem cell23_5407476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5407476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407476 prefixEnd_5407476 := by exact prefixLift 5407476
  have htrace : WordTrace (prefixWord ++ tailWord_5407476) baseStart_5407476 baseEnd_5407476 := by
    simpa [prefixWord, tailWord_5407476, baseEnd_5407476] using wordTrace_append hprefix tailTrace_5407476
  have hstable : (prefixWord ++ tailWord_5407476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407476).length < 2 ^ (prefixWord ++ tailWord_5407476).sum := by decide
  have hdescent : baseEnd_5407476 < baseStart_5407476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407502 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5407502 : Nat := 118140960795 + 5407502 * 2 ^ 59
def prefixEnd_5407502 : Nat := 4983230072969 + 3 ^ 40 * 5407502 * 2
def baseEnd_5407502 : Nat := 2776647666149007357256357

theorem tailTrace_5407502 : CollatzResearch.WordTrace tailWord_5407502 prefixEnd_5407502 2776647666149007357256357 := by
  unfold tailWord_5407502
  simp only [CollatzResearch.WordTrace]
  refine ⟨24653475106943907082613095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131485200570367504440603173 24653475106943907082613095)
  ·
    refine ⟨36980212660415860623919643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24653475106943907082613095 36980212660415860623919643)
    ·
      refine ⟨55470318990623790935879465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36980212660415860623919643 55470318990623790935879465)
      ·
        refine ⟨41602739242967843201909599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55470318990623790935879465 41602739242967843201909599)
        ·
          refine ⟨62404108864451764802864399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41602739242967843201909599 62404108864451764802864399)
          ·
            refine ⟨93606163296677647204296599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62404108864451764802864399 93606163296677647204296599)
            ·
              refine ⟨140409244945016470806444899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93606163296677647204296599 140409244945016470806444899)
              ·
                refine ⟨210613867417524706209667349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140409244945016470806444899 210613867417524706209667349)
                ·
                  refine ⟨9872525035196470603578157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210613867417524706209667349 9872525035196470603578157)
                  ·
                    refine ⟨3702196888198676476341809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9872525035196470603578157 3702196888198676476341809)
                    ·
                      refine ⟨2776647666149007357256357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702196888198676476341809 2776647666149007357256357)
                      ·
                        rfl

theorem cell23_5407502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5407502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407502 prefixEnd_5407502 := by exact prefixLift 5407502
  have htrace : WordTrace (prefixWord ++ tailWord_5407502) baseStart_5407502 baseEnd_5407502 := by
    simpa [prefixWord, tailWord_5407502, baseEnd_5407502] using wordTrace_append hprefix tailTrace_5407502
  have hstable : (prefixWord ++ tailWord_5407502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407502).length < 2 ^ (prefixWord ++ tailWord_5407502).sum := by decide
  have hdescent : baseEnd_5407502 < baseStart_5407502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407519 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 2, 3, 2]
def baseStart_5407519 : Nat := 118140960795 + 5407519 * 2 ^ 59
def prefixEnd_5407519 : Nat := 4983230072969 + 3 ^ 40 * 5407519 * 2
def baseEnd_5407519 : Nat := 2776656395320133790743779

theorem tailTrace_5407519 : CollatzResearch.WordTrace tailWord_5407519 prefixEnd_5407519 2776656395320133790743779 := by
  unfold tailWord_5407519
  simp only [CollatzResearch.WordTrace]
  refine ⟨197228420896489668564273611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131485613930993112376182407 197228420896489668564273611)
  ·
    refine ⟨295842631344734502846410417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197228420896489668564273611 295842631344734502846410417)
    ·
      refine ⟨221881973508550877134807813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295842631344734502846410417 221881973508550877134807813)
      ·
        refine ⟨41602870032853289462776465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221881973508550877134807813 41602870032853289462776465)
        ·
          refine ⟨31202152524639967097082349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41602870032853289462776465 31202152524639967097082349)
          ·
            refine ⟨11700807196739987661405881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31202152524639967097082349 11700807196739987661405881)
            ·
              refine ⟨8775605397554990746054411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11700807196739987661405881 8775605397554990746054411)
              ·
                refine ⟨13163408096332486119081617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8775605397554990746054411 13163408096332486119081617)
                ·
                  refine ⟨9872556072249364589311213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13163408096332486119081617 9872556072249364589311213)
                  ·
                    refine ⟨3702208527093511720991705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9872556072249364589311213 3702208527093511720991705)
                    ·
                      refine ⟨2776656395320133790743779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702208527093511720991705 2776656395320133790743779)
                      ·
                        rfl

theorem cell23_5407519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_5407519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407519 prefixEnd_5407519 := by exact prefixLift 5407519
  have htrace : WordTrace (prefixWord ++ tailWord_5407519) baseStart_5407519 baseEnd_5407519 := by
    simpa [prefixWord, tailWord_5407519, baseEnd_5407519] using wordTrace_append hprefix tailTrace_5407519
  have hstable : (prefixWord ++ tailWord_5407519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407519).length < 2 ^ (prefixWord ++ tailWord_5407519).sum := by decide
  have hdescent : baseEnd_5407519 < baseStart_5407519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407525 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_5407525 : Nat := 118140960795 + 5407525 * 2 ^ 59
def prefixEnd_5407525 : Nat := 4983230072969 + 3 ^ 40 * 5407525 * 2
def baseEnd_5407525 : Nat := 925553158734686922422917

theorem tailTrace_5407525 : CollatzResearch.WordTrace tailWord_5407525 prefixEnd_5407525 925553158734686922422917 := by
  unfold tailWord_5407525
  simp only [CollatzResearch.WordTrace]
  refine ⟨197228639734467931588992029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131485759822978621059328019 197228639734467931588992029)
  ·
    refine ⟨73960739900425474345872011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197228639734467931588992029 73960739900425474345872011)
    ·
      refine ⟨110941109850638211518808017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73960739900425474345872011 110941109850638211518808017)
      ·
        refine ⟨83205832387978658639106013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110941109850638211518808017 83205832387978658639106013)
        ·
          refine ⟨31202187145491996989664755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83205832387978658639106013 31202187145491996989664755)
          ·
            refine ⟨46803280718237995484497133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31202187145491996989664755 46803280718237995484497133)
            ·
              refine ⟨17551230269339248306686425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46803280718237995484497133 17551230269339248306686425)
              ·
                refine ⟨13163422702004436230014819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17551230269339248306686425 13163422702004436230014819)
                ·
                  refine ⟨19745134053006654345022229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13163422702004436230014819 19745134053006654345022229)
                  ·
                    refine ⟨925553158734686922422917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19745134053006654345022229 925553158734686922422917)
                    ·
                      rfl

theorem cell23_5407525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_5407525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407525 prefixEnd_5407525 := by exact prefixLift 5407525
  have htrace : WordTrace (prefixWord ++ tailWord_5407525) baseStart_5407525 baseEnd_5407525 := by
    simpa [prefixWord, tailWord_5407525, baseEnd_5407525] using wordTrace_append hprefix tailTrace_5407525
  have hstable : (prefixWord ++ tailWord_5407525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407525).length < 2 ^ (prefixWord ++ tailWord_5407525).sum := by decide
  have hdescent : baseEnd_5407525 < baseStart_5407525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407535 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3]
def baseStart_5407535 : Nat := 118140960795 + 5407535 * 2 ^ 59
def prefixEnd_5407535 : Nat := 4983230072969 + 3 ^ 40 * 5407535 * 2
def baseEnd_5407535 : Nat := 2776664611010605728143705

theorem tailTrace_5407535 : CollatzResearch.WordTrace tailWord_5407535 prefixEnd_5407535 2776664611010605728143705 := by
  unfold tailWord_5407535
  simp only [CollatzResearch.WordTrace]
  refine ⟨197229004464431703296856059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131486002976287802197904039 197229004464431703296856059)
  ·
    refine ⟨295843506696647554945284089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197229004464431703296856059 295843506696647554945284089)
    ·
      refine ⟨221882630022485666208963067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295843506696647554945284089 221882630022485666208963067)
      ·
        refine ⟨332823945033728499313444601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221882630022485666208963067 332823945033728499313444601)
        ·
          refine ⟨249617958775296374485083451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332823945033728499313444601 249617958775296374485083451)
          ·
            refine ⟨374426938162944561727625177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249617958775296374485083451 374426938162944561727625177)
            ·
              refine ⟨280820203622208421295718883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374426938162944561727625177 280820203622208421295718883)
              ·
                refine ⟨421230305433312631943578325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280820203622208421295718883 421230305433312631943578325)
                ·
                  refine ⟨9872585283593264811177617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 421230305433312631943578325 9872585283593264811177617)
                  ·
                    refine ⟨7404438962694948608383213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9872585283593264811177617 7404438962694948608383213)
                    ·
                      refine ⟨2776664611010605728143705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404438962694948608383213 2776664611010605728143705)
                      ·
                        rfl

theorem cell23_5407535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_5407535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407535 prefixEnd_5407535 := by exact prefixLift 5407535
  have htrace : WordTrace (prefixWord ++ tailWord_5407535) baseStart_5407535 baseEnd_5407535 := by
    simpa [prefixWord, tailWord_5407535, baseEnd_5407535] using wordTrace_append hprefix tailTrace_5407535
  have hstable : (prefixWord ++ tailWord_5407535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407535).length < 2 ^ (prefixWord ++ tailWord_5407535).sum := by decide
  have hdescent : baseEnd_5407535 < baseStart_5407535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407586 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5407586 : Nat := 118140960795 + 5407586 * 2 ^ 59
def prefixEnd_5407586 : Nat := 4983230072969 + 3 ^ 40 * 5407586 * 2
def baseEnd_5407586 : Nat := 2776690798523985028605971

theorem tailTrace_5407586 : CollatzResearch.WordTrace tailWord_5407586 prefixEnd_5407586 2776690798523985028605971 := by
  unfold tailWord_5407586
  simp only [CollatzResearch.WordTrace]
  refine ⟨49307716146811734751740653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131487243058164626004641741 49307716146811734751740653)
  ·
    refine ⟨18490393555054400531902745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49307716146811734751740653 18490393555054400531902745)
    ·
      refine ⟨13867795166290800398927059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18490393555054400531902745 13867795166290800398927059)
      ·
        refine ⟨20801692749436200598390589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13867795166290800398927059 20801692749436200598390589)
        ·
          refine ⟨7800634781038575224396471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20801692749436200598390589 7800634781038575224396471)
          ·
            refine ⟨11700952171557862836594707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7800634781038575224396471 11700952171557862836594707)
            ·
              refine ⟨17551428257336794254892061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11700952171557862836594707 17551428257336794254892061)
              ·
                refine ⟨6581785596501297845584523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17551428257336794254892061 6581785596501297845584523)
                ·
                  refine ⟨9872678394751946768376785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6581785596501297845584523 9872678394751946768376785)
                  ·
                    refine ⟨7404508796063960076282589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9872678394751946768376785 7404508796063960076282589)
                    ·
                      refine ⟨2776690798523985028605971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404508796063960076282589 2776690798523985028605971)
                      ·
                        rfl

theorem cell23_5407586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5407586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407586 prefixEnd_5407586 := by exact prefixLift 5407586
  have htrace : WordTrace (prefixWord ++ tailWord_5407586) baseStart_5407586 baseEnd_5407586 := by
    simpa [prefixWord, tailWord_5407586, baseEnd_5407586] using wordTrace_append hprefix tailTrace_5407586
  have hstable : (prefixWord ++ tailWord_5407586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407586).length < 2 ^ (prefixWord ++ tailWord_5407586).sum := by decide
  have hdescent : baseEnd_5407586 < baseStart_5407586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407615 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 2, 6]
def baseStart_5407615 : Nat := 118140960795 + 5407615 * 2 ^ 59
def prefixEnd_5407615 : Nat := 4983230072969 + 3 ^ 40 * 5407615 * 2
def baseEnd_5407615 : Nat := 925568563154321805047779

theorem tailTrace_5407615 : CollatzResearch.WordTrace tailWord_5407615 prefixEnd_5407615 925568563154321805047779 := by
  unfold tailWord_5407615
  simp only [CollatzResearch.WordTrace]
  refine ⟨197231922304141876959768299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131487948202761251306512199 197231922304141876959768299)
  ·
    refine ⟨295847883456212815439652449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197231922304141876959768299 295847883456212815439652449)
    ·
      refine ⟨221885912592159611579739337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295847883456212815439652449 221885912592159611579739337)
      ·
        refine ⟨166414434444119708684804503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221885912592159611579739337 166414434444119708684804503)
        ·
          refine ⟨249621651666179563027206755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166414434444119708684804503 249621651666179563027206755)
          ·
            refine ⟨374432477499269344540810133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249621651666179563027206755 374432477499269344540810133)
            ·
              refine ⟨17551522382778250525350475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 374432477499269344540810133 17551522382778250525350475)
              ·
                refine ⟨26327283574167375788025713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17551522382778250525350475 26327283574167375788025713)
                ·
                  refine ⟨19745462680625531841019285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26327283574167375788025713 19745462680625531841019285)
                  ·
                    refine ⟨925568563154321805047779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19745462680625531841019285 925568563154321805047779)
                    ·
                      rfl

theorem cell23_5407615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_5407615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407615 prefixEnd_5407615 := by exact prefixLift 5407615
  have htrace : WordTrace (prefixWord ++ tailWord_5407615) baseStart_5407615 baseEnd_5407615 := by
    simpa [prefixWord, tailWord_5407615, baseEnd_5407615] using wordTrace_append hprefix tailTrace_5407615
  have hstable : (prefixWord ++ tailWord_5407615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407615).length < 2 ^ (prefixWord ++ tailWord_5407615).sum := by decide
  have hdescent : baseEnd_5407615 < baseStart_5407615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407626 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5407626 : Nat := 118140960795 + 5407626 * 2 ^ 59
def prefixEnd_5407626 : Nat := 4983230072969 + 3 ^ 40 * 5407626 * 2
def baseEnd_5407626 : Nat := 2776711337750164872105787

theorem tailTrace_5407626 : CollatzResearch.WordTrace tailWord_5407626 prefixEnd_5407626 2776711337750164872105787 := by
  unfold tailWord_5407626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49308080876775506459604683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131488215671401350558945821 49308080876775506459604683)
  ·
    refine ⟨73962121315163259689407025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49308080876775506459604683 73962121315163259689407025)
    ·
      refine ⟨55471590986372444767055269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73962121315163259689407025 55471590986372444767055269)
      ·
        refine ⟨10400923309944833393822863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55471590986372444767055269 10400923309944833393822863)
        ·
          refine ⟨15601384964917250090734295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10400923309944833393822863 15601384964917250090734295)
          ·
            refine ⟨23402077447375875136101443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15601384964917250090734295 23402077447375875136101443)
            ·
              refine ⟨35103116171063812704152165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23402077447375875136101443 35103116171063812704152165)
              ·
                refine ⟨6581834282074464882028531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35103116171063812704152165 6581834282074464882028531)
                ·
                  refine ⟨9872751423111697323042797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6581834282074464882028531 9872751423111697323042797)
                  ·
                    refine ⟨3702281783666886496141049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9872751423111697323042797 3702281783666886496141049)
                    ·
                      refine ⟨2776711337750164872105787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702281783666886496141049 2776711337750164872105787)
                      ·
                        rfl

theorem cell23_5407626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5407626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407626 prefixEnd_5407626 := by exact prefixLift 5407626
  have htrace : WordTrace (prefixWord ++ tailWord_5407626) baseStart_5407626 baseEnd_5407626 := by
    simpa [prefixWord, tailWord_5407626, baseEnd_5407626] using wordTrace_append hprefix tailTrace_5407626
  have hstable : (prefixWord ++ tailWord_5407626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407626).length < 2 ^ (prefixWord ++ tailWord_5407626).sum := by decide
  have hdescent : baseEnd_5407626 < baseStart_5407626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407635 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_5407635 : Nat := 118140960795 + 5407635 * 2 ^ 59
def prefixEnd_5407635 : Nat := 4983230072969 + 3 ^ 40 * 5407635 * 2
def baseEnd_5407635 : Nat := 2776715959076055336893245

theorem tailTrace_5407635 : CollatzResearch.WordTrace tailWord_5407635 prefixEnd_5407635 2776715959076055336893245 := by
  unfold tailWord_5407635
  simp only [CollatzResearch.WordTrace]
  refine ⟨197232651764069420375496359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131488434509379613583664239 197232651764069420375496359)
  ·
    refine ⟨295848977646104130563244539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197232651764069420375496359 295848977646104130563244539)
    ·
      refine ⟨443773466469156195844866809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295848977646104130563244539 443773466469156195844866809)
      ·
        refine ⟨332830099851867146883650107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443773466469156195844866809 332830099851867146883650107)
        ·
          refine ⟨499245149777800720325475161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332830099851867146883650107 499245149777800720325475161)
          ·
            refine ⟨374433862333350540244106371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499245149777800720325475161 374433862333350540244106371)
            ·
              refine ⟨561650793500025810366159557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374433862333350540244106371 561650793500025810366159557)
              ·
                refine ⟨105309523781254839443654917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561650793500025810366159557 105309523781254839443654917)
                ·
                  refine ⟨19745535708985282395685297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105309523781254839443654917 19745535708985282395685297)
                  ·
                    refine ⟨14809151781738961796763973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19745535708985282395685297 14809151781738961796763973)
                    ·
                      refine ⟨2776715959076055336893245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14809151781738961796763973 2776715959076055336893245)
                      ·
                        rfl

theorem cell23_5407635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_5407635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407635 prefixEnd_5407635 := by exact prefixLift 5407635
  have htrace : WordTrace (prefixWord ++ tailWord_5407635) baseStart_5407635 baseEnd_5407635 := by
    simpa [prefixWord, tailWord_5407635, baseEnd_5407635] using wordTrace_append hprefix tailTrace_5407635
  have hstable : (prefixWord ++ tailWord_5407635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407635).length < 2 ^ (prefixWord ++ tailWord_5407635).sum := by decide
  have hdescent : baseEnd_5407635 < baseStart_5407635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407639 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 6, 2, 2]
def baseStart_5407639 : Nat := 118140960795 + 5407639 * 2 ^ 59
def prefixEnd_5407639 : Nat := 4983230072969 + 3 ^ 40 * 5407639 * 2
def baseEnd_5407639 : Nat := 2776718012998673321243227

theorem tailTrace_5407639 : CollatzResearch.WordTrace tailWord_5407639 prefixEnd_5407639 2776718012998673321243227 := by
  unfold tailWord_5407639
  simp only [CollatzResearch.WordTrace]
  refine ⟨197232797656054929058641971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131488531770703286039094647 197232797656054929058641971)
  ·
    refine ⟨295849196484082393587962957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197232797656054929058641971 295849196484082393587962957)
    ·
      refine ⟨110943448681530897595486109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295849196484082393587962957 110943448681530897595486109)
      ·
        refine ⟨41603793255574086598307291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110943448681530897595486109 41603793255574086598307291)
        ·
          refine ⟨62405689883361129897460937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41603793255574086598307291 62405689883361129897460937)
          ·
            refine ⟨46804267412520847423095703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62405689883361129897460937 46804267412520847423095703)
            ·
              refine ⟨70206401118781271134643555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46804267412520847423095703 70206401118781271134643555)
              ·
                refine ⟨105309601678171906701965333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70206401118781271134643555 105309601678171906701965333)
                ·
                  refine ⟨4936387578664308126654625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105309601678171906701965333 4936387578664308126654625)
                  ·
                    refine ⟨3702290683998231094990969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4936387578664308126654625 3702290683998231094990969)
                    ·
                      refine ⟨2776718012998673321243227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702290683998231094990969 2776718012998673321243227)
                      ·
                        rfl

theorem cell23_5407639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_5407639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407639 prefixEnd_5407639 := by exact prefixLift 5407639
  have htrace : WordTrace (prefixWord ++ tailWord_5407639) baseStart_5407639 baseEnd_5407639 := by
    simpa [prefixWord, tailWord_5407639, baseEnd_5407639] using wordTrace_append hprefix tailTrace_5407639
  have hstable : (prefixWord ++ tailWord_5407639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407639).length < 2 ^ (prefixWord ++ tailWord_5407639).sum := by decide
  have hdescent : baseEnd_5407639 < baseStart_5407639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407673 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 2, 2, 2]
def baseStart_5407673 : Nat := 118140960795 + 5407673 * 2 ^ 59
def prefixEnd_5407673 : Nat := 4983230072969 + 3 ^ 40 * 5407673 * 2
def baseEnd_5407673 : Nat := 2776735471340926188218071

theorem tailTrace_5407673 : CollatzResearch.WordTrace tailWord_5407673 prefixEnd_5407673 2776735471340926188218071 := by
  unfold tailWord_5407673
  simp only [CollatzResearch.WordTrace]
  refine ⟨197234037737931752865379673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131489358491954501910253115 197234037737931752865379673)
  ·
    refine ⟨147925528303448814649034755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197234037737931752865379673 147925528303448814649034755)
    ·
      refine ⟨221888292455173221973552133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147925528303448814649034755 221888292455173221973552133)
      ·
        refine ⟨41604054835344979120041025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221888292455173221973552133 41604054835344979120041025)
        ·
          refine ⟨31203041126508734340030769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41604054835344979120041025 31203041126508734340030769)
          ·
            refine ⟨23402280844881550755023077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31203041126508734340030769 23402280844881550755023077)
            ·
              refine ⟨4387927658415290766566827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23402280844881550755023077 4387927658415290766566827)
              ·
                refine ⟨6581891487622936149850241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387927658415290766566827 6581891487622936149850241)
                ·
                  refine ⟨4936418615717202112387681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581891487622936149850241 4936418615717202112387681)
                  ·
                    refine ⟨3702313961787901584290761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4936418615717202112387681 3702313961787901584290761)
                    ·
                      refine ⟨2776735471340926188218071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702313961787901584290761 2776735471340926188218071)
                      ·
                        rfl

theorem cell23_5407673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_5407673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407673 prefixEnd_5407673 := by exact prefixLift 5407673
  have htrace : WordTrace (prefixWord ++ tailWord_5407673) baseStart_5407673 baseEnd_5407673 := by
    simpa [prefixWord, tailWord_5407673, baseEnd_5407673] using wordTrace_append hprefix tailTrace_5407673
  have hstable : (prefixWord ++ tailWord_5407673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407673).length < 2 ^ (prefixWord ++ tailWord_5407673).sum := by decide
  have hdescent : baseEnd_5407673 < baseStart_5407673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407709 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_5407709 : Nat := 118140960795 + 5407709 * 2 ^ 59
def prefixEnd_5407709 : Nat := 4983230072969 + 3 ^ 40 * 5407709 * 2
def baseEnd_5407709 : Nat := 925584652214829349122635

theorem tailTrace_5407709 : CollatzResearch.WordTrace tailWord_5407709 prefixEnd_5407709 925584652214829349122635 := by
  unfold tailWord_5407709
  simp only [CollatzResearch.WordTrace]
  refine ⟨197235350765801331013690181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131490233843867554009126787 197235350765801331013690181)
  ·
    refine ⟨36981628268587749565066909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197235350765801331013690181 36981628268587749565066909)
    ·
      refine ⟨13868110600720406086900091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36981628268587749565066909 13868110600720406086900091)
      ·
        refine ⟨20802165901080609130350137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13868110600720406086900091 20802165901080609130350137)
        ·
          refine ⟨15601624425810456847762603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20802165901080609130350137 15601624425810456847762603)
          ·
            refine ⟨23402436638715685271643905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15601624425810456847762603 23402436638715685271643905)
            ·
              refine ⟨17551827479036763953732929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23402436638715685271643905 17551827479036763953732929)
              ·
                refine ⟨13163870609277572965299697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17551827479036763953732929 13163870609277572965299697)
                ·
                  refine ⟨9872902956958179723974773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13163870609277572965299697 9872902956958179723974773)
                  ·
                    refine ⟨925584652214829349122635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9872902956958179723974773 925584652214829349122635)
                    ·
                      rfl

theorem cell23_5407709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_5407709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407709 prefixEnd_5407709 := by exact prefixLift 5407709
  have htrace : WordTrace (prefixWord ++ tailWord_5407709) baseStart_5407709 baseEnd_5407709 := by
    simpa [prefixWord, tailWord_5407709, baseEnd_5407709] using wordTrace_append hprefix tailTrace_5407709
  have hstable : (prefixWord ++ tailWord_5407709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407709).length < 2 ^ (prefixWord ++ tailWord_5407709).sum := by decide
  have hdescent : baseEnd_5407709 < baseStart_5407709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407729 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_5407729 : Nat := 118140960795 + 5407729 * 2 ^ 59
def prefixEnd_5407729 : Nat := 4983230072969 + 3 ^ 40 * 5407729 * 2
def baseEnd_5407729 : Nat := 2776764226257577969117813

theorem tailTrace_5407729 : CollatzResearch.WordTrace tailWord_5407729 prefixEnd_5407729 2776764226257577969117813 := by
  unfold tailWord_5407729
  simp only [CollatzResearch.WordTrace]
  refine ⟨197236080225728874429418241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131490720150485916286278827 197236080225728874429418241)
  ·
    refine ⟨147927060169296655822063681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197236080225728874429418241 147927060169296655822063681)
    ·
      refine ⟨110945295126972491866547761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147927060169296655822063681 110945295126972491866547761)
      ·
        refine ⟨83208971345229368899910821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110945295126972491866547761 83208971345229368899910821)
        ·
          refine ⟨15601682127230506668733279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83208971345229368899910821 15601682127230506668733279)
          ·
            refine ⟨23402523190845760003099919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15601682127230506668733279 23402523190845760003099919)
            ·
              refine ⟨35103784786268640004649879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23402523190845760003099919 35103784786268640004649879)
              ·
                refine ⟨52655677179402960006974819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35103784786268640004649879 52655677179402960006974819)
                ·
                  refine ⟨78983515769104440010462229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52655677179402960006974819 78983515769104440010462229)
                  ·
                    refine ⟨3702352301676770625490417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78983515769104440010462229 3702352301676770625490417)
                    ·
                      refine ⟨2776764226257577969117813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702352301676770625490417 2776764226257577969117813)
                      ·
                        rfl

theorem cell23_5407729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_5407729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407729 prefixEnd_5407729 := by exact prefixLift 5407729
  have htrace : WordTrace (prefixWord ++ tailWord_5407729) baseStart_5407729 baseEnd_5407729 := by
    simpa [prefixWord, tailWord_5407729, baseEnd_5407729] using wordTrace_append hprefix tailTrace_5407729
  have hstable : (prefixWord ++ tailWord_5407729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407729).length < 2 ^ (prefixWord ++ tailWord_5407729).sum := by decide
  have hdescent : baseEnd_5407729 < baseStart_5407729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407756 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_5407756 : Nat := 118140960795 + 5407756 * 2 ^ 59
def prefixEnd_5407756 : Nat := 4983230072969 + 3 ^ 40 * 5407756 * 2
def baseEnd_5407756 : Nat := 925592696745083121160063

theorem tailTrace_5407756 : CollatzResearch.WordTrace tailWord_5407756 prefixEnd_5407756 925592696745083121160063 := by
  unfold tailWord_5407756
  simp only [CollatzResearch.WordTrace]
  refine ⟨98618532498315529020325561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131491376664420705360434081 98618532498315529020325561)
  ·
    refine ⟨73963899373736646765244171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98618532498315529020325561 73963899373736646765244171)
    ·
      refine ⟨110945849060604970147866257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73963899373736646765244171 110945849060604970147866257)
      ·
        refine ⟨83209386795453727610899693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110945849060604970147866257 83209386795453727610899693)
        ·
          refine ⟨31203520048295147854087385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83209386795453727610899693 31203520048295147854087385)
          ·
            refine ⟨23402640036221360890565539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31203520048295147854087385 23402640036221360890565539)
            ·
              refine ⟨35103960054332041335848309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23402640036221360890565539 35103960054332041335848309)
              ·
                refine ⟨3290996255093628875235779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35103960054332041335848309 3290996255093628875235779)
                ·
                  refine ⟨4936494382640443312853669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290996255093628875235779 4936494382640443312853669)
                  ·
                    refine ⟨925592696745083121160063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936494382640443312853669 925592696745083121160063)
                    ·
                      rfl

theorem cell23_5407756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_5407756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407756 prefixEnd_5407756 := by exact prefixLift 5407756
  have htrace : WordTrace (prefixWord ++ tailWord_5407756) baseStart_5407756 baseEnd_5407756 := by
    simpa [prefixWord, tailWord_5407756, baseEnd_5407756] using wordTrace_append hprefix tailTrace_5407756
  have hstable : (prefixWord ++ tailWord_5407756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407756).length < 2 ^ (prefixWord ++ tailWord_5407756).sum := by decide
  have hdescent : baseEnd_5407756 < baseStart_5407756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407813 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 1, 1, 3]
def baseStart_5407813 : Nat := 118140960795 + 5407813 * 2 ^ 59
def prefixEnd_5407813 : Nat := 4983230072969 + 3 ^ 40 * 5407813 * 2
def baseEnd_5407813 : Nat := 2776807358632555640467427

theorem tailTrace_5407813 : CollatzResearch.WordTrace tailWord_5407813 prefixEnd_5407813 2776807358632555640467427 := by
  unfold tailWord_5407813
  simp only [CollatzResearch.WordTrace]
  refine ⟨197239143957424556775476093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131492762638283037850317395 197239143957424556775476093)
  ·
    refine ⟨73964678984034208790803535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197239143957424556775476093 73964678984034208790803535)
    ·
      refine ⟨110947018476051313186205303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73964678984034208790803535 110947018476051313186205303)
      ·
        refine ⟨166420527714076969779307955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110947018476051313186205303 166420527714076969779307955)
        ·
          refine ⟨249630791571115454668961933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166420527714076969779307955 249630791571115454668961933)
          ·
            refine ⟨93611546839168295500860725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249630791571115454668961933 93611546839168295500860725)
            ·
              refine ⟨8776082516172027703205693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93611546839168295500860725 8776082516172027703205693)
              ·
                refine ⟨3291030943564510388702135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8776082516172027703205693 3291030943564510388702135)
                ·
                  refine ⟨4936546415346765583053203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291030943564510388702135 4936546415346765583053203)
                  ·
                    refine ⟨7404819623020148374579805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936546415346765583053203 7404819623020148374579805)
                    ·
                      refine ⟨2776807358632555640467427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404819623020148374579805 2776807358632555640467427)
                      ·
                        rfl

theorem cell23_5407813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_5407813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407813 prefixEnd_5407813 := by exact prefixLift 5407813
  have htrace : WordTrace (prefixWord ++ tailWord_5407813) baseStart_5407813 baseEnd_5407813 := by
    simpa [prefixWord, tailWord_5407813, baseEnd_5407813] using wordTrace_append hprefix tailTrace_5407813
  have hstable : (prefixWord ++ tailWord_5407813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407813).length < 2 ^ (prefixWord ++ tailWord_5407813).sum := by decide
  have hdescent : baseEnd_5407813 < baseStart_5407813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407829 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_5407829 : Nat := 118140960795 + 5407829 * 2 ^ 59
def prefixEnd_5407829 : Nat := 4983230072969 + 3 ^ 40 * 5407829 * 2
def baseEnd_5407829 : Nat := 925605191441009192622451

theorem tailTrace_5407829 : CollatzResearch.WordTrace tailWord_5407829 prefixEnd_5407829 925605191441009192622451 := by
  unfold tailWord_5407829
  simp only [CollatzResearch.WordTrace]
  refine ⟨197239727525366591508058541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131493151683577727672039027 197239727525366591508058541)
  ·
    refine ⟨73964897822012471815521953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197239727525366591508058541 73964897822012471815521953)
    ·
      refine ⟨55473673366509353861641465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73964897822012471815521953 55473673366509353861641465)
      ·
        refine ⟨41605255024882015396231099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55473673366509353861641465 41605255024882015396231099)
        ·
          refine ⟨62407882537323023094346649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41605255024882015396231099 62407882537323023094346649)
          ·
            refine ⟨46805911902992267320759987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62407882537323023094346649 46805911902992267320759987)
            ·
              refine ⟨70208867854488400981139981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46805911902992267320759987 70208867854488400981139981)
              ·
                refine ⟨26328325445433150367927493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70208867854488400981139981 26328325445433150367927493)
                ·
                  refine ⟨4936561021018715693986405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26328325445433150367927493 4936561021018715693986405)
                  ·
                    refine ⟨925605191441009192622451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936561021018715693986405 925605191441009192622451)
                    ·
                      rfl

theorem cell23_5407829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_5407829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407829 prefixEnd_5407829 := by exact prefixLift 5407829
  have htrace : WordTrace (prefixWord ++ tailWord_5407829) baseStart_5407829 baseEnd_5407829 := by
    simpa [prefixWord, tailWord_5407829, baseEnd_5407829] using wordTrace_append hprefix tailTrace_5407829
  have hstable : (prefixWord ++ tailWord_5407829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407829).length < 2 ^ (prefixWord ++ tailWord_5407829).sum := by decide
  have hdescent : baseEnd_5407829 < baseStart_5407829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407832 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5407832 : Nat := 118140960795 + 5407832 * 2 ^ 59
def prefixEnd_5407832 : Nat := 4983230072969 + 3 ^ 40 * 5407832 * 2
def baseEnd_5407832 : Nat := 2776817114764991066129839

theorem tailTrace_5407832 : CollatzResearch.WordTrace tailWord_5407832 prefixEnd_5407832 2776817114764991066129839 := by
  unfold tailWord_5407832
  simp only [CollatzResearch.WordTrace]
  refine ⟨98619918472177861510208875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131493224629570482013611833 98619918472177861510208875)
  ·
    refine ⟨147929877708266792265313313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98619918472177861510208875 147929877708266792265313313)
    ·
      refine ⟨110947408281200094198984985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147929877708266792265313313 110947408281200094198984985)
      ·
        refine ⟨83210556210900070649238739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110947408281200094198984985 83210556210900070649238739)
        ·
          refine ⟨124815834316350105973858109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83210556210900070649238739 124815834316350105973858109)
          ·
            refine ⟨46805937868631289740196791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124815834316350105973858109 46805937868631289740196791)
            ·
              refine ⟨70208906802946934610295187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46805937868631289740196791 70208906802946934610295187)
              ·
                refine ⟨105313360204420401915442781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70208906802946934610295187 105313360204420401915442781)
                ·
                  refine ⟨39492510076657650718291043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105313360204420401915442781 39492510076657650718291043)
                  ·
                    refine ⟨59238765114986476077436565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39492510076657650718291043 59238765114986476077436565)
                    ·
                      refine ⟨2776817114764991066129839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59238765114986476077436565 2776817114764991066129839)
                      ·
                        rfl

theorem cell23_5407832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5407832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407832 prefixEnd_5407832 := by exact prefixLift 5407832
  have htrace : WordTrace (prefixWord ++ tailWord_5407832) baseStart_5407832 baseEnd_5407832 := by
    simpa [prefixWord, tailWord_5407832, baseEnd_5407832] using wordTrace_append hprefix tailTrace_5407832
  have hstable : (prefixWord ++ tailWord_5407832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407832).length < 2 ^ (prefixWord ++ tailWord_5407832).sum := by decide
  have hdescent : baseEnd_5407832 < baseStart_5407832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407839 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3]
def baseStart_5407839 : Nat := 118140960795 + 5407839 * 2 ^ 59
def prefixEnd_5407839 : Nat := 4983230072969 + 3 ^ 40 * 5407839 * 2
def baseEnd_5407839 : Nat := 2776820709129572538742307

theorem tailTrace_5407839 : CollatzResearch.WordTrace tailWord_5407839 prefixEnd_5407839 2776820709129572538742307 := by
  unfold tailWord_5407839
  simp only [CollatzResearch.WordTrace]
  refine ⟨197240092255330363215922571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131493394836886908810615047 197240092255330363215922571)
  ·
    refine ⟨295860138382995544823883857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197240092255330363215922571 295860138382995544823883857)
    ·
      refine ⟨221895103787246658617912893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295860138382995544823883857 221895103787246658617912893)
      ·
        refine ⟨83210663920217496981717335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221895103787246658617912893 83210663920217496981717335)
        ·
          refine ⟨124815995880326245472576003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83210663920217496981717335 124815995880326245472576003)
          ·
            refine ⟨187223993820489368208864005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124815995880326245472576003 187223993820489368208864005)
            ·
              refine ⟨35104498841341756539162001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187223993820489368208864005 35104498841341756539162001)
              ·
                refine ⟨26328374131006317404371501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35104498841341756539162001 26328374131006317404371501)
                ·
                  refine ⟨9873140299127369026639313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26328374131006317404371501 9873140299127369026639313)
                  ·
                    refine ⟨7404855224345526769979485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9873140299127369026639313 7404855224345526769979485)
                    ·
                      refine ⟨2776820709129572538742307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404855224345526769979485 2776820709129572538742307)
                      ·
                        rfl

theorem cell23_5407839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_5407839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407839 prefixEnd_5407839 := by exact prefixLift 5407839
  have htrace : WordTrace (prefixWord ++ tailWord_5407839) baseStart_5407839 baseEnd_5407839 := by
    simpa [prefixWord, tailWord_5407839, baseEnd_5407839] using wordTrace_append hprefix tailTrace_5407839
  have hstable : (prefixWord ++ tailWord_5407839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407839).length < 2 ^ (prefixWord ++ tailWord_5407839).sum := by decide
  have hdescent : baseEnd_5407839 < baseStart_5407839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407853 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5407853 : Nat := 118140960795 + 5407853 * 2 ^ 59
def prefixEnd_5407853 : Nat := 4983230072969 + 3 ^ 40 * 5407853 * 2
def baseEnd_5407853 : Nat := 2776827897858735483967243

theorem tailTrace_5407853 : CollatzResearch.WordTrace tailWord_5407853 prefixEnd_5407853 2776827897858735483967243 := by
  unfold tailWord_5407853
  simp only [CollatzResearch.WordTrace]
  refine ⟨197240602877279643606932213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131493735251519762404621475 197240602877279643606932213)
  ·
    refine ⟨18491306519744966588149895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197240602877279643606932213 18491306519744966588149895)
    ·
      refine ⟨27736959779617449882224843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18491306519744966588149895 27736959779617449882224843)
      ·
        refine ⟨41605439669426174823337265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27736959779617449882224843 41605439669426174823337265)
        ·
          refine ⟨31204079752069631117502949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41605439669426174823337265 31204079752069631117502949)
          ·
            refine ⟨5850764953513055834531803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31204079752069631117502949 5850764953513055834531803)
            ·
              refine ⟨8776147430269583751797705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850764953513055834531803 8776147430269583751797705)
              ·
                refine ⟨6582110572702187813848279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8776147430269583751797705 6582110572702187813848279)
                ·
                  refine ⟨9873165859053281720772419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582110572702187813848279 9873165859053281720772419)
                  ·
                    refine ⟨14809748788579922581158629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9873165859053281720772419 14809748788579922581158629)
                    ·
                      refine ⟨2776827897858735483967243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14809748788579922581158629 2776827897858735483967243)
                      ·
                        rfl

theorem cell23_5407853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5407853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407853 prefixEnd_5407853 := by exact prefixLift 5407853
  have htrace : WordTrace (prefixWord ++ tailWord_5407853) baseStart_5407853 baseEnd_5407853 := by
    simpa [prefixWord, tailWord_5407853, baseEnd_5407853] using wordTrace_append hprefix tailTrace_5407853
  have hstable : (prefixWord ++ tailWord_5407853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407853).length < 2 ^ (prefixWord ++ tailWord_5407853).sum := by decide
  have hdescent : baseEnd_5407853 < baseStart_5407853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407903 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5407903 : Nat := 118140960795 + 5407903 * 2 ^ 59
def prefixEnd_5407903 : Nat := 4983230072969 + 3 ^ 40 * 5407903 * 2
def baseEnd_5407903 : Nat := 2776853571891460288342013

theorem tailTrace_5407903 : CollatzResearch.WordTrace tailWord_5407903 prefixEnd_5407903 2776853571891460288342013 := by
  unfold tailWord_5407903
  simp only [CollatzResearch.WordTrace]
  refine ⟨197242426527098502146252363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131494951018065668097501575 197242426527098502146252363)
  ·
    refine ⟨295863639790647753219378545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197242426527098502146252363 295863639790647753219378545)
    ·
      refine ⟨221897729842985814914533909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295863639790647753219378545 221897729842985814914533909)
      ·
        refine ⟨10401456086389960074118777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 221897729842985814914533909 10401456086389960074118777)
        ·
          refine ⟨7801092064792470055589083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10401456086389960074118777 7801092064792470055589083)
          ·
            refine ⟨11701638097188705083383625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801092064792470055589083 11701638097188705083383625)
            ·
              refine ⟨8776228572891528812537719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11701638097188705083383625 8776228572891528812537719)
              ·
                refine ⟨13164342859337293218806579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776228572891528812537719 13164342859337293218806579)
                ·
                  refine ⟨19746514289005939828209869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13164342859337293218806579 19746514289005939828209869)
                  ·
                    refine ⟨7404942858377227435578701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19746514289005939828209869 7404942858377227435578701)
                    ·
                      refine ⟨2776853571891460288342013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404942858377227435578701 2776853571891460288342013)
                      ·
                        rfl

theorem cell23_5407903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5407903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407903 prefixEnd_5407903 := by exact prefixLift 5407903
  have htrace : WordTrace (prefixWord ++ tailWord_5407903) baseStart_5407903 baseEnd_5407903 := by
    simpa [prefixWord, tailWord_5407903, baseEnd_5407903] using wordTrace_append hprefix tailTrace_5407903
  have hstable : (prefixWord ++ tailWord_5407903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407903).length < 2 ^ (prefixWord ++ tailWord_5407903).sum := by decide
  have hdescent : baseEnd_5407903 < baseStart_5407903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407937 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5407937 : Nat := 118140960795 + 5407937 * 2 ^ 59
def prefixEnd_5407937 : Nat := 4983230072969 + 3 ^ 40 * 5407937 * 2
def baseEnd_5407937 : Nat := 2776871030233713155316857

theorem tailTrace_5407937 : CollatzResearch.WordTrace tailWord_5407937 prefixEnd_5407937 2776871030233713155316857 := by
  unfold tailWord_5407937
  simp only [CollatzResearch.WordTrace]
  refine ⟨197243666608975325952990065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131495777739316883968660043 197243666608975325952990065)
  ·
    refine ⟨147932749956731494464742549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197243666608975325952990065 147932749956731494464742549)
    ·
      refine ⟨6934347654221788803034807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147932749956731494464742549 6934347654221788803034807)
      ·
        refine ⟨10401521481332683204552211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6934347654221788803034807 10401521481332683204552211)
        ·
          refine ⟨15602282221999024806828317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10401521481332683204552211 15602282221999024806828317)
          ·
            refine ⟨5850855833249634302560619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15602282221999024806828317 5850855833249634302560619)
            ·
              refine ⟨8776283749874451453840929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850855833249634302560619 8776283749874451453840929)
              ·
                refine ⟨6582212812405838590380697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8776283749874451453840929 6582212812405838590380697)
                ·
                  refine ⟨4936659609304378942785523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6582212812405838590380697 4936659609304378942785523)
                  ·
                    refine ⟨7404989413956568414178285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936659609304378942785523 7404989413956568414178285)
                    ·
                      refine ⟨2776871030233713155316857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7404989413956568414178285 2776871030233713155316857)
                      ·
                        rfl

theorem cell23_5407937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5407937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407937 prefixEnd_5407937 := by exact prefixLift 5407937
  have htrace : WordTrace (prefixWord ++ tailWord_5407937) baseStart_5407937 baseEnd_5407937 := by
    simpa [prefixWord, tailWord_5407937, baseEnd_5407937] using wordTrace_append hprefix tailTrace_5407937
  have hstable : (prefixWord ++ tailWord_5407937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407937).length < 2 ^ (prefixWord ++ tailWord_5407937).sum := by decide
  have hdescent : baseEnd_5407937 < baseStart_5407937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407960 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_5407960 : Nat := 118140960795 + 5407960 * 2 ^ 59
def prefixEnd_5407960 : Nat := 4983230072969 + 3 ^ 40 * 5407960 * 2
def baseEnd_5407960 : Nat := 2776882840288766565329251

theorem tailTrace_5407960 : CollatzResearch.WordTrace tailWord_5407960 prefixEnd_5407960 2776882840288766565329251 := by
  unfold tailWord_5407960
  simp only [CollatzResearch.WordTrace]
  refine ⟨98622252743946000440538667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131496336991928000587384889 98622252743946000440538667)
  ·
    refine ⟨147933379115919000660808001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98622252743946000440538667 147933379115919000660808001)
    ·
      refine ⟨110950034336939250495606001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147933379115919000660808001 110950034336939250495606001)
      ·
        refine ⟨83212525752704437871704501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110950034336939250495606001 83212525752704437871704501)
        ·
          refine ⟨7801174289316041050472297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83212525752704437871704501 7801174289316041050472297)
          ·
            refine ⟨5850880716987030787854223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801174289316041050472297 5850880716987030787854223)
            ·
              refine ⟨8776321075480546181781335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850880716987030787854223 8776321075480546181781335)
              ·
                refine ⟨13164481613220819272672003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776321075480546181781335 13164481613220819272672003)
                ·
                  refine ⟨19746722419831228909008005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13164481613220819272672003 19746722419831228909008005)
                  ·
                    refine ⟨3702510453718355420439001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19746722419831228909008005 3702510453718355420439001)
                    ·
                      refine ⟨2776882840288766565329251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702510453718355420439001 2776882840288766565329251)
                      ·
                        rfl

theorem cell23_5407960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_5407960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407960 prefixEnd_5407960 := by exact prefixLift 5407960
  have htrace : WordTrace (prefixWord ++ tailWord_5407960) baseStart_5407960 baseEnd_5407960 := by
    simpa [prefixWord, tailWord_5407960, baseEnd_5407960] using wordTrace_append hprefix tailTrace_5407960
  have hstable : (prefixWord ++ tailWord_5407960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407960).length < 2 ^ (prefixWord ++ tailWord_5407960).sum := by decide
  have hdescent : baseEnd_5407960 < baseStart_5407960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5407979 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 7]
def baseStart_5407979 : Nat := 118140960795 + 5407979 * 2 ^ 59
def prefixEnd_5407979 : Nat := 4983230072969 + 3 ^ 40 * 5407979 * 2
def baseEnd_5407979 : Nat := 925630865473733996997221

theorem tailTrace_5407979 : CollatzResearch.WordTrace tailWord_5407979 prefixEnd_5407979 925630865473733996997221 := by
  unfold tailWord_5407979
  simp only [CollatzResearch.WordTrace]
  refine ⟨197245198474823167126018991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131496798983215444750679327 197245198474823167126018991)
  ·
    refine ⟨295867797712234750689028487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197245198474823167126018991 295867797712234750689028487)
    ·
      refine ⟨443801696568352126033542731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295867797712234750689028487 443801696568352126033542731)
      ·
        refine ⟨665702544852528189050314097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443801696568352126033542731 665702544852528189050314097)
        ·
          refine ⟨499276908639396141787735573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665702544852528189050314097 499276908639396141787735573)
          ·
            refine ⟨23403605092471694146300105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 499276908639396141787735573 23403605092471694146300105)
            ·
              refine ⟨17552703819353770609725079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23403605092471694146300105 17552703819353770609725079)
              ·
                refine ⟨26329055729030655914587619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17552703819353770609725079 26329055729030655914587619)
                ·
                  refine ⟨39493583593545983871881429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26329055729030655914587619 39493583593545983871881429)
                  ·
                    refine ⟨925630865473733996997221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39493583593545983871881429 925630865473733996997221)
                    ·
                      rfl

theorem cell23_5407979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_5407979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5407979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5407979 prefixEnd_5407979 := by exact prefixLift 5407979
  have htrace : WordTrace (prefixWord ++ tailWord_5407979) baseStart_5407979 baseEnd_5407979 := by
    simpa [prefixWord, tailWord_5407979, baseEnd_5407979] using wordTrace_append hprefix tailTrace_5407979
  have hstable : (prefixWord ++ tailWord_5407979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5407979).length < 2 ^ (prefixWord ++ tailWord_5407979).sum := by decide
  have hdescent : baseEnd_5407979 < baseStart_5407979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5407979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2]
def baseStart_5408016 : Nat := 118140960795 + 5408016 * 2 ^ 59
def prefixEnd_5408016 : Nat := 4983230072969 + 3 ^ 40 * 5408016 * 2
def baseEnd_5408016 : Nat := 2776911595205418346228993

theorem tailTrace_5408016 : CollatzResearch.WordTrace tailWord_5408016 prefixEnd_5408016 2776911595205418346228993 := by
  unfold tailWord_5408016
  simp only [CollatzResearch.WordTrace]
  refine ⟨98623273987844561222557951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131497698650459414963410601 98623273987844561222557951)
  ·
    refine ⟨147934910981766841833836927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98623273987844561222557951 147934910981766841833836927)
    ·
      refine ⟨221902366472650262750755391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147934910981766841833836927 221902366472650262750755391)
      ·
        refine ⟨332853549708975394126133087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221902366472650262750755391 332853549708975394126133087)
        ·
          refine ⟨499280324563463091189199631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332853549708975394126133087 499280324563463091189199631)
          ·
            refine ⟨748920486845194636783799447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499280324563463091189199631 748920486845194636783799447)
            ·
              refine ⟨1123380730267791955175699171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748920486845194636783799447 1123380730267791955175699171)
              ·
                refine ⟨1685071095401687932763548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123380730267791955175699171 1685071095401687932763548757)
                ·
                  refine ⟨19746926899238530462072837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1685071095401687932763548757 19746926899238530462072837)
                  ·
                    refine ⟨3702548793607224461638657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19746926899238530462072837 3702548793607224461638657)
                    ·
                      refine ⟨2776911595205418346228993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702548793607224461638657 2776911595205418346228993)
                      ·
                        rfl

theorem cell23_5408016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2].length) (baseStart_5408016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408016 prefixEnd_5408016 := by exact prefixLift 5408016
  have htrace : WordTrace (prefixWord ++ tailWord_5408016) baseStart_5408016 baseEnd_5408016 := by
    simpa [prefixWord, tailWord_5408016, baseEnd_5408016] using wordTrace_append hprefix tailTrace_5408016
  have hstable : (prefixWord ++ tailWord_5408016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408016).length < 2 ^ (prefixWord ++ tailWord_5408016).sum := by decide
  have hdescent : baseEnd_5408016 < baseStart_5408016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408053 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_5408053 : Nat := 118140960795 + 5408053 * 2 ^ 59
def prefixEnd_5408053 : Nat := 4983230072969 + 3 ^ 40 * 5408053 * 2
def baseEnd_5408053 : Nat := 2776930593989634701466323

theorem tailTrace_5408053 : CollatzResearch.WordTrace tailWord_5408053 prefixEnd_5408053 2776930593989634701466323 := by
  unfold tailWord_5408053
  simp only [CollatzResearch.WordTrace]
  refine ⟨197247897476555077764212813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131498598317703385176141875 197247897476555077764212813)
  ·
    refine ⟨73967961553708154161579805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197247897476555077764212813 73967961553708154161579805)
    ·
      refine ⟨27737985582640557810592427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73967961553708154161579805 27737985582640557810592427)
      ·
        refine ⟨41606978373960836715888641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27737985582640557810592427 41606978373960836715888641)
        ·
          refine ⟨31205233780470627536916481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41606978373960836715888641 31205233780470627536916481)
          ·
            refine ⟨23403925335352970652687361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31205233780470627536916481 23403925335352970652687361)
            ·
              refine ⟨17552944001514727989515521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23403925335352970652687361 17552944001514727989515521)
              ·
                refine ⟨13164708001136045992136641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17552944001514727989515521 13164708001136045992136641)
                ·
                  refine ⟨9873531000852034494102481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13164708001136045992136641 9873531000852034494102481)
                  ·
                    refine ⟨7405148250639025870576861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9873531000852034494102481 7405148250639025870576861)
                    ·
                      refine ⟨2776930593989634701466323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405148250639025870576861 2776930593989634701466323)
                      ·
                        rfl

theorem cell23_5408053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_5408053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408053 prefixEnd_5408053 := by exact prefixLift 5408053
  have htrace : WordTrace (prefixWord ++ tailWord_5408053) baseStart_5408053 baseEnd_5408053 := by
    simpa [prefixWord, tailWord_5408053, baseEnd_5408053] using wordTrace_append hprefix tailTrace_5408053
  have hstable : (prefixWord ++ tailWord_5408053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408053).length < 2 ^ (prefixWord ++ tailWord_5408053).sum := by decide
  have hdescent : baseEnd_5408053 < baseStart_5408053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408060 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_5408060 : Nat := 118140960795 + 5408060 * 2 ^ 59
def prefixEnd_5408060 : Nat := 4983230072969 + 3 ^ 40 * 5408060 * 2
def baseEnd_5408060 : Nat := 925644729451405391359597

theorem tailTrace_5408060 : CollatzResearch.WordTrace tailWord_5408060 prefixEnd_5408060 925644729451405391359597 := by
  unfold tailWord_5408060
  simp only [CollatzResearch.WordTrace]
  refine ⟨98624076393764858979858817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131498768525019811973145089 98624076393764858979858817)
  ·
    refine ⟨73968057295323644234894113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98624076393764858979858817 73968057295323644234894113)
    ·
      refine ⟨55476042971492733176170585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73968057295323644234894113 55476042971492733176170585)
      ·
        refine ⟨41607032228619549882127939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55476042971492733176170585 41607032228619549882127939)
        ·
          refine ⟨62410548342929324823191909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41607032228619549882127939 62410548342929324823191909)
          ·
            refine ⟨11701977814299248404348483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62410548342929324823191909 11701977814299248404348483)
            ·
              refine ⟨17552966721448872606522725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11701977814299248404348483 17552966721448872606522725)
              ·
                refine ⟨3291181260271663613723011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17552966721448872606522725 3291181260271663613723011)
                ·
                  refine ⟨4936771890407495420584517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291181260271663613723011 4936771890407495420584517)
                  ·
                    refine ⟨925644729451405391359597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936771890407495420584517 925644729451405391359597)
                    ·
                      rfl

theorem cell23_5408060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_5408060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408060 prefixEnd_5408060 := by exact prefixLift 5408060
  have htrace : WordTrace (prefixWord ++ tailWord_5408060) baseStart_5408060 baseEnd_5408060 := by
    simpa [prefixWord, tailWord_5408060, baseEnd_5408060] using wordTrace_append hprefix tailTrace_5408060
  have hstable : (prefixWord ++ tailWord_5408060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408060).length < 2 ^ (prefixWord ++ tailWord_5408060).sum := by decide
  have hdescent : baseEnd_5408060 < baseStart_5408060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408077 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5408077 : Nat := 118140960795 + 5408077 * 2 ^ 59
def prefixEnd_5408077 : Nat := 4983230072969 + 3 ^ 40 * 5408077 * 2
def baseEnd_5408077 : Nat := 925647639175114202522071

theorem tailTrace_5408077 : CollatzResearch.WordTrace tailWord_5408077 prefixEnd_5408077 925647639175114202522071 := by
  unfold tailWord_5408077
  simp only [CollatzResearch.WordTrace]
  refine ⟨197248772828468129863086485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131499181885645419908724323 197248772828468129863086485)
  ·
    refine ⟨9246036226334443587332179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 197248772828468129863086485 9246036226334443587332179)
    ·
      refine ⟨13869054339501665380998269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246036226334443587332179 13869054339501665380998269)
      ·
        refine ⟨5200895377313124517874351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13869054339501665380998269 5200895377313124517874351)
        ·
          refine ⟨7801343065969686776811527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200895377313124517874351 7801343065969686776811527)
          ·
            refine ⟨11702014598954530165217291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801343065969686776811527 11702014598954530165217291)
            ·
              refine ⟨17553021898431795247825937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11702014598954530165217291 17553021898431795247825937)
              ·
                refine ⟨13164766423823846435869453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17553021898431795247825937 13164766423823846435869453)
                ·
                  refine ⟨4936787408933942413451045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13164766423823846435869453 4936787408933942413451045)
                  ·
                    refine ⟨925647639175114202522071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936787408933942413451045 925647639175114202522071)
                    ·
                      rfl

theorem cell23_5408077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5408077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408077 prefixEnd_5408077 := by exact prefixLift 5408077
  have htrace : WordTrace (prefixWord ++ tailWord_5408077) baseStart_5408077 baseEnd_5408077 := by
    simpa [prefixWord, tailWord_5408077, baseEnd_5408077] using wordTrace_append hprefix tailTrace_5408077
  have hstable : (prefixWord ++ tailWord_5408077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408077).length < 2 ^ (prefixWord ++ tailWord_5408077).sum := by decide
  have hdescent : baseEnd_5408077 < baseStart_5408077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408079 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_5408079 : Nat := 118140960795 + 5408079 * 2 ^ 59
def prefixEnd_5408079 : Nat := 4983230072969 + 3 ^ 40 * 5408079 * 2
def baseEnd_5408079 : Nat := 2776943944486651599741203

theorem tailTrace_5408079 : CollatzResearch.WordTrace tailWord_5408079 prefixEnd_5408079 2776943944486651599741203 := by
  unfold tailWord_5408079
  simp only [CollatzResearch.WordTrace]
  refine ⟨197248845774460884204659291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131499230516307256136439527 197248845774460884204659291)
  ·
    refine ⟨295873268661691326306988937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197248845774460884204659291 295873268661691326306988937)
    ·
      refine ⟨221904951496268494730241703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295873268661691326306988937 221904951496268494730241703)
      ·
        refine ⟨332857427244402742095362555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221904951496268494730241703 332857427244402742095362555)
        ·
          refine ⟨499286140866604113143043833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332857427244402742095362555 499286140866604113143043833)
          ·
            refine ⟨374464605649953084857282875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499286140866604113143043833 374464605649953084857282875)
            ·
              refine ⟨561696908474929627285924313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374464605649953084857282875 561696908474929627285924313)
              ·
                refine ⟨421272681356197220464443235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561696908474929627285924313 421272681356197220464443235)
                ·
                  refine ⟨631909022034295830696664853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421272681356197220464443235 631909022034295830696664853)
                  ·
                    refine ⟨29620735407857617063906165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 631909022034295830696664853 29620735407857617063906165)
                    ·
                      refine ⟨2776943944486651599741203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29620735407857617063906165 2776943944486651599741203)
                      ·
                        rfl

theorem cell23_5408079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_5408079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408079 prefixEnd_5408079 := by exact prefixLift 5408079
  have htrace : WordTrace (prefixWord ++ tailWord_5408079) baseStart_5408079 baseEnd_5408079 := by
    simpa [prefixWord, tailWord_5408079, baseEnd_5408079] using wordTrace_append hprefix tailTrace_5408079
  have hstable : (prefixWord ++ tailWord_5408079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408079).length < 2 ^ (prefixWord ++ tailWord_5408079).sum := by decide
  have hdescent : baseEnd_5408079 < baseStart_5408079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408083 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 3]
def baseStart_5408083 : Nat := 118140960795 + 5408083 * 2 ^ 59
def prefixEnd_5408083 : Nat := 4983230072969 + 3 ^ 40 * 5408083 * 2
def baseEnd_5408083 : Nat := 2776945998409269584091185

theorem tailTrace_5408083 : CollatzResearch.WordTrace tailWord_5408083 prefixEnd_5408083 2776945998409269584091185 := by
  unfold tailWord_5408083
  simp only [CollatzResearch.WordTrace]
  refine ⟨197248991666446392887804903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131499327777630928591869935 197248991666446392887804903)
  ·
    refine ⟨295873487499669589331707355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197248991666446392887804903 295873487499669589331707355)
    ·
      refine ⟨443810231249504383997561033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295873487499669589331707355 443810231249504383997561033)
      ·
        refine ⟨332857673437128287998170775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443810231249504383997561033 332857673437128287998170775)
        ·
          refine ⟨499286510155692431997256163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332857673437128287998170775 499286510155692431997256163)
          ·
            refine ⟨748929765233538647995884245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499286510155692431997256163 748929765233538647995884245)
            ·
              refine ⟨17553041372661062062403537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 748929765233538647995884245 17553041372661062062403537)
              ·
                refine ⟨13164781029495796546802653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17553041372661062062403537 13164781029495796546802653)
                ·
                  refine ⟨4936792886060923705050995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13164781029495796546802653 4936792886060923705050995)
                  ·
                    refine ⟨7405189329091385557576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936792886060923705050995 7405189329091385557576493)
                    ·
                      refine ⟨2776945998409269584091185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405189329091385557576493 2776945998409269584091185)
                      ·
                        rfl

theorem cell23_5408083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_5408083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408083 prefixEnd_5408083 := by exact prefixLift 5408083
  have htrace : WordTrace (prefixWord ++ tailWord_5408083) baseStart_5408083 baseEnd_5408083 := by
    simpa [prefixWord, tailWord_5408083, baseEnd_5408083] using wordTrace_append hprefix tailTrace_5408083
  have hstable : (prefixWord ++ tailWord_5408083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408083).length < 2 ^ (prefixWord ++ tailWord_5408083).sum := by decide
  have hdescent : baseEnd_5408083 < baseStart_5408083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408117 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5408117 : Nat := 118140960795 + 5408117 * 2 ^ 59
def prefixEnd_5408117 : Nat := 4983230072969 + 3 ^ 40 * 5408117 * 2
def baseEnd_5408117 : Nat := 2776963456751522451066029

theorem tailTrace_5408117 : CollatzResearch.WordTrace tailWord_5408117 prefixEnd_5408117 2776963456751522451066029 := by
  unfold tailWord_5408117
  simp only [CollatzResearch.WordTrace]
  refine ⟨197250231748323216694542605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131500154498882144463028403 197250231748323216694542605)
  ·
    refine ⟨73968836905621206260453477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197250231748323216694542605 73968836905621206260453477)
    ·
      refine ⟨13869156919803976173835027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73968836905621206260453477 13869156919803976173835027)
      ·
        refine ⟨20803735379705964260752541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13869156919803976173835027 20803735379705964260752541)
        ·
          refine ⟨7801400767389736597782203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20803735379705964260752541 7801400767389736597782203)
          ·
            refine ⟨11702101151084604896673305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801400767389736597782203 11702101151084604896673305)
            ·
              refine ⟨8776575863313453672504979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11702101151084604896673305 8776575863313453672504979)
              ·
                refine ⟨13164863794970180508757469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776575863313453672504979 13164863794970180508757469)
                ·
                  refine ⟨4936823923113817690784051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13164863794970180508757469 4936823923113817690784051)
                  ·
                    refine ⟨7405235884670726536176077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936823923113817690784051 7405235884670726536176077)
                    ·
                      refine ⟨2776963456751522451066029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405235884670726536176077 2776963456751522451066029)
                      ·
                        rfl

theorem cell23_5408117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5408117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408117 prefixEnd_5408117 := by exact prefixLift 5408117
  have htrace : WordTrace (prefixWord ++ tailWord_5408117) baseStart_5408117 baseEnd_5408117 := by
    simpa [prefixWord, tailWord_5408117, baseEnd_5408117] using wordTrace_append hprefix tailTrace_5408117
  have hstable : (prefixWord ++ tailWord_5408117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408117).length < 2 ^ (prefixWord ++ tailWord_5408117).sum := by decide
  have hdescent : baseEnd_5408117 < baseStart_5408117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408133 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_5408133 : Nat := 118140960795 + 5408133 * 2 ^ 59
def prefixEnd_5408133 : Nat := 4983230072969 + 3 ^ 40 * 5408133 * 2
def baseEnd_5408133 : Nat := 925657224147331462821985

theorem tailTrace_5408133 : CollatzResearch.WordTrace tailWord_5408133 prefixEnd_5408133 925657224147331462821985 := by
  unfold tailWord_5408133
  simp only [CollatzResearch.WordTrace]
  refine ⟨197250815316265251427125053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131500543544176834284750035 197250815316265251427125053)
  ·
    refine ⟨73969055743599469285171895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197250815316265251427125053 73969055743599469285171895)
    ·
      refine ⟨110953583615399203927757843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73969055743599469285171895 110953583615399203927757843)
      ·
        refine ⟨166430375423098805891636765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110953583615399203927757843 166430375423098805891636765)
        ·
          refine ⟨62411390783662052209363787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166430375423098805891636765 62411390783662052209363787)
          ·
            refine ⟨93617086175493078314045681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62411390783662052209363787 93617086175493078314045681)
            ·
              refine ⟨70212814631619808735534261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93617086175493078314045681 70212814631619808735534261)
              ·
                refine ⟨6582451371714357068956337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70212814631619808735534261 6582451371714357068956337)
                ·
                  refine ⟨4936838528785767801717253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6582451371714357068956337 4936838528785767801717253)
                  ·
                    refine ⟨925657224147331462821985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936838528785767801717253 925657224147331462821985)
                    ·
                      rfl

theorem cell23_5408133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_5408133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408133 prefixEnd_5408133 := by exact prefixLift 5408133
  have htrace : WordTrace (prefixWord ++ tailWord_5408133) baseStart_5408133 baseEnd_5408133 := by
    simpa [prefixWord, tailWord_5408133, baseEnd_5408133] using wordTrace_append hprefix tailTrace_5408133
  have hstable : (prefixWord ++ tailWord_5408133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408133).length < 2 ^ (prefixWord ++ tailWord_5408133).sum := by decide
  have hdescent : baseEnd_5408133 < baseStart_5408133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408140 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 3, 2, 2]
def baseStart_5408140 : Nat := 118140960795 + 5408140 * 2 ^ 59
def prefixEnd_5408140 : Nat := 4983230072969 + 3 ^ 40 * 5408140 * 2
def baseEnd_5408140 : Nat := 2776975266806575861078423

theorem tailTrace_5408140 : CollatzResearch.WordTrace tailWord_5408140 prefixEnd_5408140 2776975266806575861078423 := by
  unfold tailWord_5408140
  simp only [CollatzResearch.WordTrace]
  refine ⟨98625535313619945811314937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131500713751493261081753249 98625535313619945811314937)
  ·
    refine ⟨73969151485214959358486203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98625535313619945811314937 73969151485214959358486203)
    ·
      refine ⟨110953727227822439037729305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73969151485214959358486203 110953727227822439037729305)
      ·
        refine ⟨83215295420866829278296979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110953727227822439037729305 83215295420866829278296979)
        ·
          refine ⟨124822943131300243917445469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83215295420866829278296979 124822943131300243917445469)
          ·
            refine ⟨46808603674237591469042051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124822943131300243917445469 46808603674237591469042051)
            ·
              refine ⟨70212905511356387203563077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46808603674237591469042051 70212905511356387203563077)
              ·
                refine ⟨13164919783379322600668077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70212905511356387203563077 13164919783379322600668077)
                ·
                  refine ⟨4936844918767245975250529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13164919783379322600668077 4936844918767245975250529)
                  ·
                    refine ⟨3702633689075434481437897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4936844918767245975250529 3702633689075434481437897)
                    ·
                      refine ⟨2776975266806575861078423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702633689075434481437897 2776975266806575861078423)
                      ·
                        rfl

theorem cell23_5408140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_5408140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408140 prefixEnd_5408140 := by exact prefixLift 5408140
  have htrace : WordTrace (prefixWord ++ tailWord_5408140) baseStart_5408140 baseEnd_5408140 := by
    simpa [prefixWord, tailWord_5408140, baseEnd_5408140] using wordTrace_append hprefix tailTrace_5408140
  have hstable : (prefixWord ++ tailWord_5408140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408140).length < 2 ^ (prefixWord ++ tailWord_5408140).sum := by decide
  have hdescent : baseEnd_5408140 < baseStart_5408140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408200 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_5408200 : Nat := 118140960795 + 5408200 * 2 ^ 59
def prefixEnd_5408200 : Nat := 4983230072969 + 3 ^ 40 * 5408200 * 2
def baseEnd_5408200 : Nat := 2777006075645845626328147

theorem tailTrace_5408200 : CollatzResearch.WordTrace tailWord_5408200 prefixEnd_5408200 2777006075645845626328147 := by
  unfold tailWord_5408200
  simp only [CollatzResearch.WordTrace]
  refine ⟨98626629503511260934907027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131502172671348347913209369 98626629503511260934907027)
  ·
    refine ⟨147939944255266891402360541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98626629503511260934907027 147939944255266891402360541)
    ·
      refine ⟨55477479095725084275885203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147939944255266891402360541 55477479095725084275885203)
      ·
        refine ⟨83216218643587626413827805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55477479095725084275885203 83216218643587626413827805)
        ·
          refine ⟨31206081991345359905185427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83216218643587626413827805 31206081991345359905185427)
          ·
            refine ⟨46809122987018039857778141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31206081991345359905185427 46809122987018039857778141)
            ·
              refine ⟨17553421120131764946666803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46809122987018039857778141 17553421120131764946666803)
              ·
                refine ⟨26330131680197647420000205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17553421120131764946666803 26330131680197647420000205)
                ·
                  refine ⟨9873799380074117782500077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26330131680197647420000205 9873799380074117782500077)
                  ·
                    refine ⟨3702674767527794168437529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9873799380074117782500077 3702674767527794168437529)
                    ·
                      refine ⟨2777006075645845626328147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702674767527794168437529 2777006075645845626328147)
                      ·
                        rfl

theorem cell23_5408200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_5408200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408200 prefixEnd_5408200 := by exact prefixLift 5408200
  have htrace : WordTrace (prefixWord ++ tailWord_5408200) baseStart_5408200 baseEnd_5408200 := by
    simpa [prefixWord, tailWord_5408200, baseEnd_5408200] using wordTrace_append hprefix tailTrace_5408200
  have hstable : (prefixWord ++ tailWord_5408200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408200).length < 2 ^ (prefixWord ++ tailWord_5408200).sum := by decide
  have hdescent : baseEnd_5408200 < baseStart_5408200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408253 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 7]
def baseStart_5408253 : Nat := 118140960795 + 5408253 * 2 ^ 59
def prefixEnd_5408253 : Nat := 4983230072969 + 3 ^ 40 * 5408253 * 2
def baseEnd_5408253 : Nat := 308559254457837102107267

theorem tailTrace_5408253 : CollatzResearch.WordTrace tailWord_5408253 prefixEnd_5408253 308559254457837102107267 := by
  unfold tailWord_5408253
  simp only [CollatzResearch.WordTrace]
  refine ⟨197255192075830511921493413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131503461383887007947662275 197255192075830511921493413)
  ·
    refine ⟨36985348514218220985280015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197255192075830511921493413 36985348514218220985280015)
    ·
      refine ⟨55478022771327331477920023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36985348514218220985280015 55478022771327331477920023)
      ·
        refine ⟨83217034156990997216880035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55478022771327331477920023 83217034156990997216880035)
        ·
          refine ⟨124825551235486495825320053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83217034156990997216880035 124825551235486495825320053)
          ·
            refine ⟨11702395428326858983623755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124825551235486495825320053 11702395428326858983623755)
            ·
              refine ⟨17553593142490288475435633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11702395428326858983623755 17553593142490288475435633)
              ·
                refine ⟨13165194856867716356576725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17553593142490288475435633 13165194856867716356576725)
                ·
                  refine ⟨308559254457837102107267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13165194856867716356576725 308559254457837102107267)
                  ·
                    rfl

theorem cell23_5408253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_5408253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408253 prefixEnd_5408253 := by exact prefixLift 5408253
  have htrace : WordTrace (prefixWord ++ tailWord_5408253) baseStart_5408253 baseEnd_5408253 := by
    simpa [prefixWord, tailWord_5408253, baseEnd_5408253] using wordTrace_append hprefix tailTrace_5408253
  have hstable : (prefixWord ++ tailWord_5408253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408253).length < 2 ^ (prefixWord ++ tailWord_5408253).sum := by decide
  have hdescent : baseEnd_5408253 < baseStart_5408253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408290 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_5408290 : Nat := 118140960795 + 5408290 * 2 ^ 59
def prefixEnd_5408290 : Nat := 4983230072969 + 3 ^ 40 * 5408290 * 2
def baseEnd_5408290 : Nat := 2777052288904750274202733

theorem tailTrace_5408290 : CollatzResearch.WordTrace tailWord_5408290 prefixEnd_5408290 2777052288904750274202733 := by
  unfold tailWord_5408290
  simp only [CollatzResearch.WordTrace]
  refine ⟨49314135394174116810147581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131504361051130978160393549 49314135394174116810147581)
  ·
    refine ⟨18492800772815293803805343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49314135394174116810147581 18492800772815293803805343)
    ·
      refine ⟨27739201159222940705708015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18492800772815293803805343 27739201159222940705708015)
      ·
        refine ⟨41608801738834411058562023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27739201159222940705708015 41608801738834411058562023)
        ·
          refine ⟨62413202608251616587843035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41608801738834411058562023 62413202608251616587843035)
          ·
            refine ⟨93619803912377424881764553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62413202608251616587843035 93619803912377424881764553)
            ·
              refine ⟨70214852934283068661323415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93619803912377424881764553 70214852934283068661323415)
              ·
                refine ⟨105322279401424602991985123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70214852934283068661323415 105322279401424602991985123)
                ·
                  refine ⟨157983419102136904487977685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105322279401424602991985123 157983419102136904487977685)
                  ·
                    refine ⟨3702736385206333698936977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 157983419102136904487977685 3702736385206333698936977)
                    ·
                      refine ⟨2777052288904750274202733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3702736385206333698936977 2777052288904750274202733)
                      ·
                        rfl

theorem cell23_5408290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_5408290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408290 prefixEnd_5408290 := by exact prefixLift 5408290
  have htrace : WordTrace (prefixWord ++ tailWord_5408290) baseStart_5408290 baseEnd_5408290 := by
    simpa [prefixWord, tailWord_5408290, baseEnd_5408290] using wordTrace_append hprefix tailTrace_5408290
  have hstable : (prefixWord ++ tailWord_5408290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408290).length < 2 ^ (prefixWord ++ tailWord_5408290).sum := by decide
  have hdescent : baseEnd_5408290 < baseStart_5408290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408343 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 8]
def baseStart_5408343 : Nat := 118140960795 + 5408343 * 2 ^ 59
def prefixEnd_5408343 : Nat := 4983230072969 + 3 ^ 40 * 5408343 * 2
def baseEnd_5408343 : Nat := 308564389264382062982221

theorem tailTrace_5408343 : CollatzResearch.WordTrace tailWord_5408343 prefixEnd_5408343 308564389264382062982221 := by
  unfold tailWord_5408343
  simp only [CollatzResearch.WordTrace]
  refine ⟨197258474645504457292269683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131505649763669638194846455 197258474645504457292269683)
  ·
    refine ⟨295887711968256685938404525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197258474645504457292269683 295887711968256685938404525)
    ·
      refine ⟨110957891988096257226901697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 295887711968256685938404525 110957891988096257226901697)
      ·
        refine ⟨83218418991072192920176273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110957891988096257226901697 83218418991072192920176273)
        ·
          refine ⟨62413814243304144690132205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83218418991072192920176273 62413814243304144690132205)
          ·
            refine ⟨23405180341239054258799577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62413814243304144690132205 23405180341239054258799577)
            ·
              refine ⟨17553885255929290694099683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23405180341239054258799577 17553885255929290694099683)
              ·
                refine ⟨26330827883893936041149525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17553885255929290694099683 26330827883893936041149525)
                ·
                  refine ⟨308564389264382062982221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26330827883893936041149525 308564389264382062982221)
                  ·
                    rfl

theorem cell23_5408343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 8].length) (baseStart_5408343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408343 prefixEnd_5408343 := by exact prefixLift 5408343
  have htrace : WordTrace (prefixWord ++ tailWord_5408343) baseStart_5408343 baseEnd_5408343 := by
    simpa [prefixWord, tailWord_5408343, baseEnd_5408343] using wordTrace_append hprefix tailTrace_5408343
  have hstable : (prefixWord ++ tailWord_5408343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408343).length < 2 ^ (prefixWord ++ tailWord_5408343).sum := by decide
  have hdescent : baseEnd_5408343 < baseStart_5408343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408374 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5408374 : Nat := 118140960795 + 5408374 * 2 ^ 59
def prefixEnd_5408374 : Nat := 4983230072969 + 3 ^ 40 * 5408374 * 2
def baseEnd_5408374 : Nat := 2777095421279727945552347

theorem tailTrace_5408374 : CollatzResearch.WordTrace tailWord_5408374 prefixEnd_5408374 2777095421279727945552347 := by
  unfold tailWord_5408374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328725331774509349165511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131506403538928099724432117 12328725331774509349165511)
  ·
    refine ⟨18493087997661764023748267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12328725331774509349165511 18493087997661764023748267)
    ·
      refine ⟨27739631996492646035622401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18493087997661764023748267 27739631996492646035622401)
      ·
        refine ⟨20804723997369484526716801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27739631996492646035622401 20804723997369484526716801)
        ·
          refine ⟨15603542998027113395037601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20804723997369484526716801 15603542998027113395037601)
          ·
            refine ⟨11702657248520335046278201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15603542998027113395037601 11702657248520335046278201)
            ·
              refine ⟨8776992936390251284708651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11702657248520335046278201 8776992936390251284708651)
              ·
                refine ⟨13165489404585376927062977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776992936390251284708651 13165489404585376927062977)
                ·
                  refine ⟨9874117053439032695297233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13165489404585376927062977 9874117053439032695297233)
                  ·
                    refine ⟨7405587790079274521472925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9874117053439032695297233 7405587790079274521472925)
                    ·
                      refine ⟨2777095421279727945552347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405587790079274521472925 2777095421279727945552347)
                      ·
                        rfl

theorem cell23_5408374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5408374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408374 prefixEnd_5408374 := by exact prefixLift 5408374
  have htrace : WordTrace (prefixWord ++ tailWord_5408374) baseStart_5408374 baseEnd_5408374 := by
    simpa [prefixWord, tailWord_5408374, baseEnd_5408374] using wordTrace_append hprefix tailTrace_5408374
  have hstable : (prefixWord ++ tailWord_5408374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408374).length < 2 ^ (prefixWord ++ tailWord_5408374).sum := by decide
  have hdescent : baseEnd_5408374 < baseStart_5408374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408420 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_5408420 : Nat := 118140960795 + 5408420 * 2 ^ 59
def prefixEnd_5408420 : Nat := 4983230072969 + 3 ^ 40 * 5408420 * 2
def baseEnd_5408420 : Nat := 925706347129944921859045

theorem tailTrace_5408420 : CollatzResearch.WordTrace tailWord_5408420 prefixEnd_5408420 925706347129944921859045 := by
  unfold tailWord_5408420
  simp only [CollatzResearch.WordTrace]
  refine ⟨98630641533112749721411357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131507522044150332961881809 98630641533112749721411357)
  ·
    refine ⟨36986490574917281145529259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98630641533112749721411357 36986490574917281145529259)
    ·
      refine ⟨55479735862375921718293889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36986490574917281145529259 55479735862375921718293889)
      ·
        refine ⟨41609801896781941288720417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55479735862375921718293889 41609801896781941288720417)
        ·
          refine ⟨31207351422586455966540313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41609801896781941288720417 31207351422586455966540313)
          ·
            refine ⟨23405513566939841974905235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31207351422586455966540313 23405513566939841974905235)
            ·
              refine ⟨35108270350409762962357853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23405513566939841974905235 35108270350409762962357853)
              ·
                refine ⟨13165601381403661110884195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35108270350409762962357853 13165601381403661110884195)
                ·
                  refine ⟨19748402072105491666326293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13165601381403661110884195 19748402072105491666326293)
                  ·
                    refine ⟨925706347129944921859045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19748402072105491666326293 925706347129944921859045)
                    ·
                      rfl

theorem cell23_5408420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_5408420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408420 prefixEnd_5408420 := by exact prefixLift 5408420
  have htrace : WordTrace (prefixWord ++ tailWord_5408420) baseStart_5408420 baseEnd_5408420 := by
    simpa [prefixWord, tailWord_5408420, baseEnd_5408420] using wordTrace_append hprefix tailTrace_5408420
  have hstable : (prefixWord ++ tailWord_5408420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408420).length < 2 ^ (prefixWord ++ tailWord_5408420).sum := by decide
  have hdescent : baseEnd_5408420 < baseStart_5408420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408438 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5408438 : Nat := 118140960795 + 5408438 * 2 ^ 59
def prefixEnd_5408438 : Nat := 4983230072969 + 3 ^ 40 * 5408438 * 2
def baseEnd_5408438 : Nat := 2777128284041615695152053

theorem tailTrace_5408438 : CollatzResearch.WordTrace tailWord_5408438 prefixEnd_5408438 2777128284041615695152053 := by
  unfold tailWord_5408438
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328871223760018032311123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 131507959720106859011318645 12328871223760018032311123)
  ·
    refine ⟨18493306835640027048466685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12328871223760018032311123 18493306835640027048466685)
    ·
      refine ⟨6934990063365010143175007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18493306835640027048466685 6934990063365010143175007)
      ·
        refine ⟨10402485095047515214762511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6934990063365010143175007 10402485095047515214762511)
        ·
          refine ⟨15603727642571272822143767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402485095047515214762511 15603727642571272822143767)
          ·
            refine ⟨23405591463856909233215651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15603727642571272822143767 23405591463856909233215651)
            ·
              refine ⟨35108387195785363849823477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23405591463856909233215651 35108387195785363849823477)
              ·
                refine ⟨3291411299604877860920951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35108387195785363849823477 3291411299604877860920951)
                ·
                  refine ⟨4937116949407316791381427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291411299604877860920951 4937116949407316791381427)
                  ·
                    refine ⟨7405675424110975187072141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4937116949407316791381427 7405675424110975187072141)
                    ·
                      refine ⟨2777128284041615695152053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405675424110975187072141 2777128284041615695152053)
                      ·
                        rfl

theorem cell23_5408438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5408438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408438 prefixEnd_5408438 := by exact prefixLift 5408438
  have htrace : WordTrace (prefixWord ++ tailWord_5408438) baseStart_5408438 baseEnd_5408438 := by
    simpa [prefixWord, tailWord_5408438, baseEnd_5408438] using wordTrace_append hprefix tailTrace_5408438
  have hstable : (prefixWord ++ tailWord_5408438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408438).length < 2 ^ (prefixWord ++ tailWord_5408438).sum := by decide
  have hdescent : baseEnd_5408438 < baseStart_5408438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408444 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 1, 1, 4]
def baseStart_5408444 : Nat := 118140960795 + 5408444 * 2 ^ 59
def prefixEnd_5408444 : Nat := 4983230072969 + 3 ^ 40 * 5408444 * 2
def baseEnd_5408444 : Nat := 2777131364925542671677025

theorem tailTrace_5408444 : CollatzResearch.WordTrace tailWord_5408444 prefixEnd_5408444 2777131364925542671677025 := by
  unfold tailWord_5408444
  simp only [CollatzResearch.WordTrace]
  refine ⟨98631079209069275770848193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131508105612092367694464257 98631079209069275770848193)
  ·
    refine ⟨73973309406801956828136145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98631079209069275770848193 73973309406801956828136145)
    ·
      refine ⟨55479982055101467621102109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73973309406801956828136145 55479982055101467621102109)
      ·
        refine ⟨20804993270663050357913291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55479982055101467621102109 20804993270663050357913291)
        ·
          refine ⟨31207489905994575536869937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20804993270663050357913291 31207489905994575536869937)
          ·
            refine ⟨23405617429495931652652453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31207489905994575536869937 23405617429495931652652453)
            ·
              refine ⟨4388553268030487184872335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23405617429495931652652453 4388553268030487184872335)
              ·
                refine ⟨6582829902045730777308503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388553268030487184872335 6582829902045730777308503)
                ·
                  refine ⟨9874244853068596165962755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582829902045730777308503 9874244853068596165962755)
                  ·
                    refine ⟨14811367279602894248944133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9874244853068596165962755 14811367279602894248944133)
                    ·
                      refine ⟨2777131364925542671677025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14811367279602894248944133 2777131364925542671677025)
                      ·
                        rfl

theorem cell23_5408444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_5408444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408444 prefixEnd_5408444 := by exact prefixLift 5408444
  have htrace : WordTrace (prefixWord ++ tailWord_5408444) baseStart_5408444 baseEnd_5408444 := by
    simpa [prefixWord, tailWord_5408444, baseEnd_5408444] using wordTrace_append hprefix tailTrace_5408444
  have hstable : (prefixWord ++ tailWord_5408444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408444).length < 2 ^ (prefixWord ++ tailWord_5408444).sum := by decide
  have hdescent : baseEnd_5408444 < baseStart_5408444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408447 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 3]
def baseStart_5408447 : Nat := 118140960795 + 5408447 * 2 ^ 59
def prefixEnd_5408447 : Nat := 4983230072969 + 3 ^ 40 * 5408447 * 2
def baseEnd_5408447 : Nat := 2777132905367506159939511

theorem tailTrace_5408447 : CollatzResearch.WordTrace tailWord_5408447 prefixEnd_5408447 2777132905367506159939511 := by
  unfold tailWord_5408447
  simp only [CollatzResearch.WordTrace]
  refine ⟨197262267837127683054055595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131508178558085122036037063 197262267837127683054055595)
  ·
    refine ⟨295893401755691524581083393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197262267837127683054055595 295893401755691524581083393)
    ·
      refine ⟨221920051316768643435812545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295893401755691524581083393 221920051316768643435812545)
      ·
        refine ⟨166440038487576482576859409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221920051316768643435812545 166440038487576482576859409)
        ·
          refine ⟨124830028865682361932644557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166440038487576482576859409 124830028865682361932644557)
          ·
            refine ⟨46811260824630885724741709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124830028865682361932644557 46811260824630885724741709)
            ·
              refine ⟨17554222809236582146778141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46811260824630885724741709 17554222809236582146778141)
              ·
                refine ⟨6582833553463718305041803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17554222809236582146778141 6582833553463718305041803)
                ·
                  refine ⟨9874250330195577457562705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582833553463718305041803 9874250330195577457562705)
                  ·
                    refine ⟨7405687747646683093172029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9874250330195577457562705 7405687747646683093172029)
                    ·
                      refine ⟨2777132905367506159939511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405687747646683093172029 2777132905367506159939511)
                      ·
                        rfl

theorem cell23_5408447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_5408447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408447 prefixEnd_5408447 := by exact prefixLift 5408447
  have htrace : WordTrace (prefixWord ++ tailWord_5408447) baseStart_5408447 baseEnd_5408447 := by
    simpa [prefixWord, tailWord_5408447, baseEnd_5408447] using wordTrace_append hprefix tailTrace_5408447
  have hstable : (prefixWord ++ tailWord_5408447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408447).length < 2 ^ (prefixWord ++ tailWord_5408447).sum := by decide
  have hdescent : baseEnd_5408447 < baseStart_5408447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408463 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 9]
def baseStart_5408463 : Nat := 118140960795 + 5408463 * 2 ^ 59
def prefixEnd_5408463 : Nat := 4983230072969 + 3 ^ 40 * 5408463 * 2
def baseEnd_5408463 : Nat := 925713707019326032446479

theorem tailTrace_5408463 : CollatzResearch.WordTrace tailWord_5408463 prefixEnd_5408463 925713707019326032446479 := by
  unfold tailWord_5408463
  simp only [CollatzResearch.WordTrace]
  refine ⟨197262851405069717786638043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131508567603379811857758695 197262851405069717786638043)
  ·
    refine ⟨295894277107604576679957065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197262851405069717786638043 295894277107604576679957065)
    ·
      refine ⟨221920707830703432509967799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295894277107604576679957065 221920707830703432509967799)
      ·
        refine ⟨332881061746055148764951699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221920707830703432509967799 332881061746055148764951699)
        ·
          refine ⟨499321592619082723147427549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332881061746055148764951699 499321592619082723147427549)
          ·
            refine ⟨187245597232156021180285331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499321592619082723147427549 187245597232156021180285331)
            ·
              refine ⟨280868395848234031770427997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187245597232156021180285331 280868395848234031770427997)
              ·
                refine ⟨105325648443087761913910499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280868395848234031770427997 105325648443087761913910499)
                ·
                  refine ⟨157988472664631642870865749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105325648443087761913910499 157988472664631642870865749)
                  ·
                    refine ⟨925713707019326032446479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 157988472664631642870865749 925713707019326032446479)
                    ·
                      rfl

theorem cell23_5408463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_5408463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408463 prefixEnd_5408463 := by exact prefixLift 5408463
  have htrace : WordTrace (prefixWord ++ tailWord_5408463) baseStart_5408463 baseEnd_5408463 := by
    simpa [prefixWord, tailWord_5408463, baseEnd_5408463] using wordTrace_append hprefix tailTrace_5408463
  have hstable : (prefixWord ++ tailWord_5408463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408463).length < 2 ^ (prefixWord ++ tailWord_5408463).sum := by decide
  have hdescent : baseEnd_5408463 < baseStart_5408463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408490 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5408490 : Nat := 118140960795 + 5408490 * 2 ^ 59
def prefixEnd_5408490 : Nat := 4983230072969 + 3 ^ 40 * 5408490 * 2
def baseEnd_5408490 : Nat := 2777154985035649491701813

theorem tailTrace_5408490 : CollatzResearch.WordTrace tailWord_5408490 prefixEnd_5408490 2777154985035649491701813 := by
  unfold tailWord_5408490
  simp only [CollatzResearch.WordTrace]
  refine ⟨49315959043992975349467731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131509224117314600931913949 49315959043992975349467731)
  ·
    refine ⟨73973938565989463024201597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49315959043992975349467731 73973938565989463024201597)
    ·
      refine ⟨27740226962246048634075599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73973938565989463024201597 27740226962246048634075599)
      ·
        refine ⟨41610340443369072951113399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27740226962246048634075599 41610340443369072951113399)
        ·
          refine ⟨62415510665053609426670099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41610340443369072951113399 62415510665053609426670099)
          ·
            refine ⟨93623265997580414140005149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62415510665053609426670099 93623265997580414140005149)
            ·
              refine ⟨35108724749092655302501931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93623265997580414140005149 35108724749092655302501931)
              ·
                refine ⟨52663087123638982953752897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35108724749092655302501931 52663087123638982953752897)
                ·
                  refine ⟨39497315342729237215314673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52663087123638982953752897 39497315342729237215314673)
                  ·
                    refine ⟨29622986507046927911486005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39497315342729237215314673 29622986507046927911486005)
                    ·
                      refine ⟨2777154985035649491701813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29622986507046927911486005 2777154985035649491701813)
                      ·
                        rfl

theorem cell23_5408490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5408490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408490 prefixEnd_5408490 := by exact prefixLift 5408490
  have htrace : WordTrace (prefixWord ++ tailWord_5408490) baseStart_5408490 baseEnd_5408490 := by
    simpa [prefixWord, tailWord_5408490, baseEnd_5408490] using wordTrace_append hprefix tailTrace_5408490
  have hstable : (prefixWord ++ tailWord_5408490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408490).length < 2 ^ (prefixWord ++ tailWord_5408490).sum := by decide
  have hdescent : baseEnd_5408490 < baseStart_5408490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408520 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_5408520 : Nat := 118140960795 + 5408520 * 2 ^ 59
def prefixEnd_5408520 : Nat := 4983230072969 + 3 ^ 40 * 5408520 * 2
def baseEnd_5408520 : Nat := 2777170389455284374326675

theorem tailTrace_5408520 : CollatzResearch.WordTrace tailWord_5408520 prefixEnd_5408520 2777170389455284374326675 := by
  unfold tailWord_5408520
  simp only [CollatzResearch.WordTrace]
  refine ⟨98632465182931608260731507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131509953577242144347642009 98632465182931608260731507)
  ·
    refine ⟨147948697774397412391097261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98632465182931608260731507 147948697774397412391097261)
    ·
      refine ⟨55480761665399029646661473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147948697774397412391097261 55480761665399029646661473)
      ·
        refine ⟨41610571249049272234996105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55480761665399029646661473 41610571249049272234996105)
        ·
          refine ⟨31207928436786954176247079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41610571249049272234996105 31207928436786954176247079)
          ·
            refine ⟨46811892655180431264370619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31207928436786954176247079 46811892655180431264370619)
            ·
              refine ⟨70217838982770646896555929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46811892655180431264370619 70217838982770646896555929)
              ·
                refine ⟨52663379237077985172416947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70217838982770646896555929 52663379237077985172416947)
                ·
                  refine ⟨78995068855616977758625421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52663379237077985172416947 78995068855616977758625421)
                  ·
                    refine ⟨29623150820856366659484533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78995068855616977758625421 29623150820856366659484533)
                    ·
                      refine ⟨2777170389455284374326675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29623150820856366659484533 2777170389455284374326675)
                      ·
                        rfl

theorem cell23_5408520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_5408520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408520 prefixEnd_5408520 := by exact prefixLift 5408520
  have htrace : WordTrace (prefixWord ++ tailWord_5408520) baseStart_5408520 baseEnd_5408520 := by
    simpa [prefixWord, tailWord_5408520, baseEnd_5408520] using wordTrace_append hprefix tailTrace_5408520
  have hstable : (prefixWord ++ tailWord_5408520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408520).length < 2 ^ (prefixWord ++ tailWord_5408520).sum := by decide
  have hdescent : baseEnd_5408520 < baseStart_5408520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408532 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5408532 : Nat := 118140960795 + 5408532 * 2 ^ 59
def prefixEnd_5408532 : Nat := 4983230072969 + 3 ^ 40 * 5408532 * 2
def baseEnd_5408532 : Nat := 2777176551223138327376621

theorem tailTrace_5408532 : CollatzResearch.WordTrace tailWord_5408532 prefixEnd_5408532 2777176551223138327376621 := by
  unfold tailWord_5408532
  simp only [CollatzResearch.WordTrace]
  refine ⟨98632684020909871285449925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131510245361213161713933233 98632684020909871285449925)
  ·
    refine ⟨18493628253920600866021861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98632684020909871285449925 18493628253920600866021861)
    ·
      refine ⟨3467555297610112662379099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18493628253920600866021861 3467555297610112662379099)
      ·
        refine ⟨5201332946415168993568649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467555297610112662379099 5201332946415168993568649)
        ·
          refine ⟨3900999709811376745176487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5201332946415168993568649 3900999709811376745176487)
          ·
            refine ⟨5851499564717065117764731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900999709811376745176487 5851499564717065117764731)
            ·
              refine ⟨8777249347075597676647097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851499564717065117764731 8777249347075597676647097)
              ·
                refine ⟨6582937010306698257485323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8777249347075597676647097 6582937010306698257485323)
                ·
                  refine ⟨9874405515460047386227985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582937010306698257485323 9874405515460047386227985)
                  ·
                    refine ⟨7405804136595035539670989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9874405515460047386227985 7405804136595035539670989)
                    ·
                      refine ⟨2777176551223138327376621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405804136595035539670989 2777176551223138327376621)
                      ·
                        rfl

theorem cell23_5408532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5408532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408532 prefixEnd_5408532 := by exact prefixLift 5408532
  have htrace : WordTrace (prefixWord ++ tailWord_5408532) baseStart_5408532 baseEnd_5408532 := by
    simpa [prefixWord, tailWord_5408532, baseEnd_5408532] using wordTrace_append hprefix tailTrace_5408532
  have hstable : (prefixWord ++ tailWord_5408532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408532).length < 2 ^ (prefixWord ++ tailWord_5408532).sum := by decide
  have hdescent : baseEnd_5408532 < baseStart_5408532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408540 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 9]
def baseStart_5408540 : Nat := 118140960795 + 5408540 * 2 ^ 59
def prefixEnd_5408540 : Nat := 4983230072969 + 3 ^ 40 * 5408540 * 2
def baseEnd_5408540 : Nat := 308575628785374921786287

theorem tailTrace_5408540 : CollatzResearch.WordTrace tailWord_5408540 prefixEnd_5408540 308575628785374921786287 := by
  unfold tailWord_5408540
  simp only [CollatzResearch.WordTrace]
  refine ⟨98632829912895379968595537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131510439883860506624794049 98632829912895379968595537)
  ·
    refine ⟨73974622434671534976446653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98632829912895379968595537 73974622434671534976446653)
    ·
      refine ⟨27740483413001825616167495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73974622434671534976446653 27740483413001825616167495)
      ·
        refine ⟨41610725119502738424251243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27740483413001825616167495 41610725119502738424251243)
        ·
          refine ⟨62416087679254107636376865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41610725119502738424251243 62416087679254107636376865)
          ·
            refine ⟨46812065759440580727282649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62416087679254107636376865 46812065759440580727282649)
            ·
              refine ⟨35109049319580435545461987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46812065759440580727282649 35109049319580435545461987)
              ·
                refine ⟨52663573979370653318192981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35109049319580435545461987 52663573979370653318192981)
                ·
                  refine ⟨308575628785374921786287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52663573979370653318192981 308575628785374921786287)
                  ·
                    rfl

theorem cell23_5408540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_5408540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408540 prefixEnd_5408540 := by exact prefixLift 5408540
  have htrace : WordTrace (prefixWord ++ tailWord_5408540) baseStart_5408540 baseEnd_5408540 := by
    simpa [prefixWord, tailWord_5408540, baseEnd_5408540] using wordTrace_append hprefix tailTrace_5408540
  have hstable : (prefixWord ++ tailWord_5408540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408540).length < 2 ^ (prefixWord ++ tailWord_5408540).sum := by decide
  have hdescent : baseEnd_5408540 < baseStart_5408540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408604 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5408604 : Nat := 118140960795 + 5408604 * 2 ^ 59
def prefixEnd_5408604 : Nat := 4983230072969 + 3 ^ 40 * 5408604 * 2
def baseEnd_5408604 : Nat := 925737840610087348558763

theorem tailTrace_5408604 : CollatzResearch.WordTrace tailWord_5408604 prefixEnd_5408604 925737840610087348558763 := by
  unfold tailWord_5408604
  simp only [CollatzResearch.WordTrace]
  refine ⟨98633997048779449433760433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131511996065039265911680577 98633997048779449433760433)
  ·
    refine ⟨73975497786584587075320325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98633997048779449433760433 73975497786584587075320325)
    ·
      refine ⟨13870405834984610076622561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73975497786584587075320325 13870405834984610076622561)
      ·
        refine ⟨10402804376238457557466921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13870405834984610076622561 10402804376238457557466921)
        ·
          refine ⟨7802103282178843168100191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10402804376238457557466921 7802103282178843168100191)
          ·
            refine ⟨11703154923268264752150287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802103282178843168100191 11703154923268264752150287)
            ·
              refine ⟨17554732384902397128225431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11703154923268264752150287 17554732384902397128225431)
              ·
                refine ⟨26332098577353595692338147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17554732384902397128225431 26332098577353595692338147)
                ·
                  refine ⟨39498147866030393538507221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26332098577353595692338147 39498147866030393538507221)
                  ·
                    refine ⟨925737840610087348558763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39498147866030393538507221 925737840610087348558763)
                    ·
                      rfl

theorem cell23_5408604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5408604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408604 prefixEnd_5408604 := by exact prefixLift 5408604
  have htrace : WordTrace (prefixWord ++ tailWord_5408604) baseStart_5408604 baseEnd_5408604 := by
    simpa [prefixWord, tailWord_5408604, baseEnd_5408604] using wordTrace_append hprefix tailTrace_5408604
  have hstable : (prefixWord ++ tailWord_5408604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408604).length < 2 ^ (prefixWord ++ tailWord_5408604).sum := by decide
  have hdescent : baseEnd_5408604 < baseStart_5408604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408607 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_5408607 : Nat := 118140960795 + 5408607 * 2 ^ 59
def prefixEnd_5408607 : Nat := 4983230072969 + 3 ^ 40 * 5408607 * 2
def baseEnd_5408607 : Nat := 2777215062272225533938775

theorem tailTrace_5408607 : CollatzResearch.WordTrace tailWord_5408607 prefixEnd_5408607 2777215062272225533938775 := by
  unfold tailWord_5408607
  simp only [CollatzResearch.WordTrace]
  refine ⟨197268103516548030379880075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131512069011032020253253383 197268103516548030379880075)
  ·
    refine ⟨295902155274822045569820113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197268103516548030379880075 295902155274822045569820113)
    ·
      refine ⟨221926616456116534177365085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295902155274822045569820113 221926616456116534177365085)
      ·
        refine ⟨83222481171043700316511907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221926616456116534177365085 83222481171043700316511907)
        ·
          refine ⟨124833721756565550474767861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83222481171043700316511907 124833721756565550474767861)
          ·
            refine ⟨11703161414678020357009487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124833721756565550474767861 11703161414678020357009487)
            ·
              refine ⟨17554742122017030535514231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11703161414678020357009487 17554742122017030535514231)
              ·
                refine ⟨26332113183025545803271347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17554742122017030535514231 26332113183025545803271347)
                ·
                  refine ⟨39498169774538318704907021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26332113183025545803271347 39498169774538318704907021)
                  ·
                    refine ⟨14811813665451869514340133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39498169774538318704907021 14811813665451869514340133)
                    ·
                      refine ⟨2777215062272225533938775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14811813665451869514340133 2777215062272225533938775)
                      ·
                        rfl

theorem cell23_5408607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_5408607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408607 prefixEnd_5408607 := by exact prefixLift 5408607
  have htrace : WordTrace (prefixWord ++ tailWord_5408607) baseStart_5408607 baseEnd_5408607 := by
    simpa [prefixWord, tailWord_5408607, baseEnd_5408607] using wordTrace_append hprefix tailTrace_5408607
  have hstable : (prefixWord ++ tailWord_5408607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408607).length < 2 ^ (prefixWord ++ tailWord_5408607).sum := by decide
  have hdescent : baseEnd_5408607 < baseStart_5408607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408627 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3]
def baseStart_5408627 : Nat := 118140960795 + 5408627 * 2 ^ 59
def prefixEnd_5408627 : Nat := 4983230072969 + 3 ^ 40 * 5408627 * 2
def baseEnd_5408627 : Nat := 2777225331885315455688683

theorem tailTrace_5408627 : CollatzResearch.WordTrace tailWord_5408627 prefixEnd_5408627 2777225331885315455688683 := by
  unfold tailWord_5408627
  simp only [CollatzResearch.WordTrace]
  refine ⟨197268832976475573795608135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131512555317650382530405423 197268832976475573795608135)
  ·
    refine ⟨295903249464713360693412203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197268832976475573795608135 295903249464713360693412203)
    ·
      refine ⟨443854874197070041040118305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295903249464713360693412203 443854874197070041040118305)
      ·
        refine ⟨332891155647802530780088729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443854874197070041040118305 332891155647802530780088729)
        ·
          refine ⟨249668366735851898085066547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332891155647802530780088729 249668366735851898085066547)
          ·
            refine ⟨374502550103777847127599821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249668366735851898085066547 374502550103777847127599821)
            ·
              refine ⟨140438456288916692672849933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374502550103777847127599821 140438456288916692672849933)
              ·
                refine ⟨52664421108343759752318725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140438456288916692672849933 52664421108343759752318725)
                ·
                  refine ⟨9874578957814454953559761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52664421108343759752318725 9874578957814454953559761)
                  ·
                    refine ⟨7405934218360841215169821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9874578957814454953559761 7405934218360841215169821)
                    ·
                      refine ⟨2777225331885315455688683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7405934218360841215169821 2777225331885315455688683)
                      ·
                        rfl

theorem cell23_5408627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_5408627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408627 prefixEnd_5408627 := by exact prefixLift 5408627
  have htrace : WordTrace (prefixWord ++ tailWord_5408627) baseStart_5408627 baseEnd_5408627 := by
    simpa [prefixWord, tailWord_5408627, baseEnd_5408627] using wordTrace_append hprefix tailTrace_5408627
  have hstable : (prefixWord ++ tailWord_5408627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408627).length < 2 ^ (prefixWord ++ tailWord_5408627).sum := by decide
  have hdescent : baseEnd_5408627 < baseStart_5408627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408668 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_5408668 : Nat := 118140960795 + 5408668 * 2 ^ 59
def prefixEnd_5408668 : Nat := 4983230072969 + 3 ^ 40 * 5408668 * 2
def baseEnd_5408668 : Nat := 925748794864049931758665

theorem tailTrace_5408668 : CollatzResearch.WordTrace tailWord_5408668 prefixEnd_5408668 925748794864049931758665 := by
  unfold tailWord_5408668
  simp only [CollatzResearch.WordTrace]
  refine ⟨98635164184663518898925329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131513552246218025198567105 98635164184663518898925329)
  ·
    refine ⟨73976373138497639174193997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98635164184663518898925329 73976373138497639174193997)
    ·
      refine ⟨27741139926936614690322749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73976373138497639174193997 27741139926936614690322749)
      ·
        refine ⟨10402927472601230508871031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27741139926936614690322749 10402927472601230508871031)
        ·
          refine ⟨15604391208901845763306547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402927472601230508871031 15604391208901845763306547)
          ·
            refine ⟨23406586813352768644959821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15604391208901845763306547 23406586813352768644959821)
            ·
              refine ⟨8777470055007288241859933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23406586813352768644959821 8777470055007288241859933)
              ·
                refine ⟨3291551270627733090697475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8777470055007288241859933 3291551270627733090697475)
                ·
                  refine ⟨4937326905941599636046213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291551270627733090697475 4937326905941599636046213)
                  ·
                    refine ⟨925748794864049931758665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937326905941599636046213 925748794864049931758665)
                    ·
                      rfl

theorem cell23_5408668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_5408668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408668 prefixEnd_5408668 := by exact prefixLift 5408668
  have htrace : WordTrace (prefixWord ++ tailWord_5408668) baseStart_5408668 baseEnd_5408668 := by
    simpa [prefixWord, tailWord_5408668, baseEnd_5408668] using wordTrace_append hprefix tailTrace_5408668
  have hstable : (prefixWord ++ tailWord_5408668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408668).length < 2 ^ (prefixWord ++ tailWord_5408668).sum := by decide
  have hdescent : baseEnd_5408668 < baseStart_5408668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408714 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_5408714 : Nat := 118140960795 + 5408714 * 2 ^ 59
def prefixEnd_5408714 : Nat := 4983230072969 + 3 ^ 40 * 5408714 * 2
def baseEnd_5408714 : Nat := 2777270004702256615300783

theorem tailTrace_5408714 : CollatzResearch.WordTrace tailWord_5408714 prefixEnd_5408714 2777270004702256615300783 := by
  unfold tailWord_5408714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49318001531790096913506299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131514670751440258436016797 49318001531790096913506299)
  ·
    refine ⟨73977002297685145370259449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49318001531790096913506299 73977002297685145370259449)
    ·
      refine ⟨55482751723263859027694587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73977002297685145370259449 55482751723263859027694587)
      ·
        refine ⟨83224127584895788541541881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55482751723263859027694587 83224127584895788541541881)
        ·
          refine ⟨62418095688671841406156411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83224127584895788541541881 62418095688671841406156411)
          ·
            refine ⟨93627143533007762109234617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62418095688671841406156411 93627143533007762109234617)
            ·
              refine ⟨70220357649755821581925963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93627143533007762109234617 70220357649755821581925963)
              ·
                refine ⟨105330536474633732372888945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70220357649755821581925963 105330536474633732372888945)
                ·
                  refine ⟨78997902355975299279666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105330536474633732372888945 78997902355975299279666709)
                  ·
                    refine ⟨3703026672936342153734377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78997902355975299279666709 3703026672936342153734377)
                    ·
                      refine ⟨2777270004702256615300783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703026672936342153734377 2777270004702256615300783)
                      ·
                        rfl

theorem cell23_5408714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_5408714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408714 prefixEnd_5408714 := by exact prefixLift 5408714
  have htrace : WordTrace (prefixWord ++ tailWord_5408714) baseStart_5408714 baseEnd_5408714 := by
    simpa [prefixWord, tailWord_5408714, baseEnd_5408714] using wordTrace_append hprefix tailTrace_5408714
  have hstable : (prefixWord ++ tailWord_5408714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408714).length < 2 ^ (prefixWord ++ tailWord_5408714).sum := by decide
  have hdescent : baseEnd_5408714 < baseStart_5408714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408724 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5408724 : Nat := 118140960795 + 5408724 * 2 ^ 59
def prefixEnd_5408724 : Nat := 4983230072969 + 3 ^ 40 * 5408724 * 2
def baseEnd_5408724 : Nat := 925758379836267192058579

theorem tailTrace_5408724 : CollatzResearch.WordTrace tailWord_5408724 prefixEnd_5408724 925758379836267192058579 := by
  unfold tailWord_5408724
  simp only [CollatzResearch.WordTrace]
  refine ⟨98636185428562079680944613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131514913904749439574592817 98636185428562079680944613)
  ·
    refine ⟨18494284767855389940177115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98636185428562079680944613 18494284767855389940177115)
    ·
      refine ⟨27741427151783084910265673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18494284767855389940177115 27741427151783084910265673)
      ·
        refine ⟨20806070363837313682699255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27741427151783084910265673 20806070363837313682699255)
        ·
          refine ⟨31209105545755970524048883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20806070363837313682699255 31209105545755970524048883)
          ·
            refine ⟨46813658318633955786073325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31209105545755970524048883 46813658318633955786073325)
            ·
              refine ⟨17555121869487733419777497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46813658318633955786073325 17555121869487733419777497)
              ·
                refine ⟨13166341402115800064833123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17555121869487733419777497 13166341402115800064833123)
                ·
                  refine ⟨19749512103173700097249685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13166341402115800064833123 19749512103173700097249685)
                  ·
                    refine ⟨925758379836267192058579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19749512103173700097249685 925758379836267192058579)
                    ·
                      rfl

theorem cell23_5408724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5408724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408724 prefixEnd_5408724 := by exact prefixLift 5408724
  have htrace : WordTrace (prefixWord ++ tailWord_5408724) baseStart_5408724 baseEnd_5408724 := by
    simpa [prefixWord, tailWord_5408724, baseEnd_5408724] using wordTrace_append hprefix tailTrace_5408724
  have hstable : (prefixWord ++ tailWord_5408724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408724).length < 2 ^ (prefixWord ++ tailWord_5408724).sum := by decide
  have hdescent : baseEnd_5408724 < baseStart_5408724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408825 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 1, 3, 2]
def baseStart_5408825 : Nat := 118140960795 + 5408825 * 2 ^ 59
def prefixEnd_5408825 : Nat := 4983230072969 + 3 ^ 40 * 5408825 * 2
def baseEnd_5408825 : Nat := 2777327001054905681012773

theorem tailTrace_5408825 : CollatzResearch.WordTrace tailWord_5408825 prefixEnd_5408825 2777327001054905681012773 := by
  unfold tailWord_5408825
  simp only [CollatzResearch.WordTrace]
  refine ⟨197276054629758253611315929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131517369753172169074210619 197276054629758253611315929)
  ·
    refine ⟨147957040972318690208486947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197276054629758253611315929 147957040972318690208486947)
    ·
      refine ⟨221935561458478035312730421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147957040972318690208486947 221935561458478035312730421)
      ·
        refine ⟨20806458886732315810568477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221935561458478035312730421 20806458886732315810568477)
        ·
          refine ⟨7802422082524618428963179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20806458886732315810568477 7802422082524618428963179)
          ·
            refine ⟨11703633123786927643444769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802422082524618428963179 11703633123786927643444769)
            ·
              refine ⟨8777724842840195732583577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11703633123786927643444769 8777724842840195732583577)
              ·
                refine ⟨6583293632130146799437683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8777724842840195732583577 6583293632130146799437683)
                ·
                  refine ⟨9874940448195220199156525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583293632130146799437683 9874940448195220199156525)
                  ·
                    refine ⟨3703102668073207574683697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9874940448195220199156525 3703102668073207574683697)
                    ·
                      refine ⟨2777327001054905681012773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703102668073207574683697 2777327001054905681012773)
                      ·
                        rfl

theorem cell23_5408825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_5408825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408825 prefixEnd_5408825 := by exact prefixLift 5408825
  have htrace : WordTrace (prefixWord ++ tailWord_5408825) baseStart_5408825 baseEnd_5408825 := by
    simpa [prefixWord, tailWord_5408825, baseEnd_5408825] using wordTrace_append hprefix tailTrace_5408825
  have hstable : (prefixWord ++ tailWord_5408825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408825).length < 2 ^ (prefixWord ++ tailWord_5408825).sum := by decide
  have hdescent : baseEnd_5408825 < baseStart_5408825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408928 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2]
def baseStart_5408928 : Nat := 118140960795 + 5408928 * 2 ^ 59
def prefixEnd_5408928 : Nat := 4983230072969 + 3 ^ 40 * 5408928 * 2
def baseEnd_5408928 : Nat := 2777379889562318778024799

theorem tailTrace_5408928 : CollatzResearch.WordTrace tailWord_5408928 prefixEnd_5408928 2777379889562318778024799 := by
  unfold tailWord_5408928
  simp only [CollatzResearch.WordTrace]
  refine ⟨98639905674192551101157719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131519874232256734801543625 98639905674192551101157719)
  ·
    refine ⟨147959858511288826651736579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98639905674192551101157719 147959858511288826651736579)
    ·
      refine ⟨221939787766933239977604869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147959858511288826651736579 221939787766933239977604869)
      ·
        refine ⟨41613710206299982495800913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221939787766933239977604869 41613710206299982495800913)
        ·
          refine ⟨31210282654724986871850685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41613710206299982495800913 31210282654724986871850685)
          ·
            refine ⟨11703855995521870076944007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31210282654724986871850685 11703855995521870076944007)
            ·
              refine ⟨17555783993282805115416011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11703855995521870076944007 17555783993282805115416011)
              ·
                refine ⟨26333675989924207673124017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17555783993282805115416011 26333675989924207673124017)
                ·
                  refine ⟨19750256992443155754843013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26333675989924207673124017 19750256992443155754843013)
                  ·
                    refine ⟨3703173186083091704033065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19750256992443155754843013 3703173186083091704033065)
                    ·
                      refine ⟨2777379889562318778024799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703173186083091704033065 2777379889562318778024799)
                      ·
                        rfl

theorem cell23_5408928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_5408928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408928 prefixEnd_5408928 := by exact prefixLift 5408928
  have htrace : WordTrace (prefixWord ++ tailWord_5408928) baseStart_5408928 baseEnd_5408928 := by
    simpa [prefixWord, tailWord_5408928, baseEnd_5408928] using wordTrace_append hprefix tailTrace_5408928
  have hstable : (prefixWord ++ tailWord_5408928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408928).length < 2 ^ (prefixWord ++ tailWord_5408928).sum := by decide
  have hdescent : baseEnd_5408928 < baseStart_5408928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408942 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5408942 : Nat := 118140960795 + 5408942 * 2 ^ 59
def prefixEnd_5408942 : Nat := 4983230072969 + 3 ^ 40 * 5408942 * 2
def baseEnd_5408942 : Nat := 925795692763827241083245

theorem tailTrace_5408942 : CollatzResearch.WordTrace tailWord_5408942 prefixEnd_5408942 925795692763827241083245 := by
  unfold tailWord_5408942
  simp only [CollatzResearch.WordTrace]
  refine ⟨24660040246291797824165635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131520214646889588395550053 24660040246291797824165635)
  ·
    refine ⟨36990060369437696736248453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24660040246291797824165635 36990060369437696736248453)
    ·
      refine ⟨6935636319269568138046585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36990060369437696736248453 6935636319269568138046585)
      ·
        refine ⟨5201727239452176103534939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6935636319269568138046585 5201727239452176103534939)
        ·
          refine ⟨7802590859178264155302409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201727239452176103534939 7802590859178264155302409)
          ·
            refine ⟨5851943144383698116476807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802590859178264155302409 5851943144383698116476807)
            ·
              refine ⟨8777914716575547174715211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851943144383698116476807 8777914716575547174715211)
              ·
                refine ⟨13166872074863320762072817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8777914716575547174715211 13166872074863320762072817)
                ·
                  refine ⟨9875154056147490571554613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13166872074863320762072817 9875154056147490571554613)
                  ·
                    refine ⟨925795692763827241083245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9875154056147490571554613 925795692763827241083245)
                    ·
                      rfl

theorem cell23_5408942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5408942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408942 prefixEnd_5408942 := by exact prefixLift 5408942
  have htrace : WordTrace (prefixWord ++ tailWord_5408942) baseStart_5408942 baseEnd_5408942 := by
    simpa [prefixWord, tailWord_5408942, baseEnd_5408942] using wordTrace_append hprefix tailTrace_5408942
  have hstable : (prefixWord ++ tailWord_5408942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408942).length < 2 ^ (prefixWord ++ tailWord_5408942).sum := by decide
  have hdescent : baseEnd_5408942 < baseStart_5408942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408945 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5408945 : Nat := 118140960795 + 5408945 * 2 ^ 59
def prefixEnd_5408945 : Nat := 4983230072969 + 3 ^ 40 * 5408945 * 2
def baseEnd_5408945 : Nat := 2777388618733445211512221

theorem tailTrace_5408945 : CollatzResearch.WordTrace tailWord_5408945 prefixEnd_5408945 2777388618733445211512221 := by
  unfold tailWord_5408945
  simp only [CollatzResearch.WordTrace]
  refine ⟨197280431389323514105684289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131520287592882342737122859 197280431389323514105684289)
  ·
    refine ⟨147960323541992635579263217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197280431389323514105684289 147960323541992635579263217)
    ·
      refine ⟨110970242656494476684447413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147960323541992635579263217 110970242656494476684447413)
      ·
        refine ⟨10403460249046357189166945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110970242656494476684447413 10403460249046357189166945)
        ·
          refine ⟨7802595186784767891875209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10403460249046357189166945 7802595186784767891875209)
          ·
            refine ⟨5851946390088575918906407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802595186784767891875209 5851946390088575918906407)
            ·
              refine ⟨8777919585132863878359611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851946390088575918906407 8777919585132863878359611)
              ·
                refine ⟨13166879377699295817539417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8777919585132863878359611 13166879377699295817539417)
                ·
                  refine ⟨9875159533274471863154563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13166879377699295817539417 9875159533274471863154563)
                  ·
                    refine ⟨14812739299911707794731845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9875159533274471863154563 14812739299911707794731845)
                    ·
                      refine ⟨2777388618733445211512221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14812739299911707794731845 2777388618733445211512221)
                      ·
                        rfl

theorem cell23_5408945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5408945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408945 prefixEnd_5408945 := by exact prefixLift 5408945
  have htrace : WordTrace (prefixWord ++ tailWord_5408945) baseStart_5408945 baseEnd_5408945 := by
    simpa [prefixWord, tailWord_5408945, baseEnd_5408945] using wordTrace_append hprefix tailTrace_5408945
  have hstable : (prefixWord ++ tailWord_5408945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408945).length < 2 ^ (prefixWord ++ tailWord_5408945).sum := by decide
  have hdescent : baseEnd_5408945 < baseStart_5408945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5408962 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5408962 : Nat := 118140960795 + 5408962 * 2 ^ 59
def prefixEnd_5408962 : Nat := 4983230072969 + 3 ^ 40 * 5408962 * 2
def baseEnd_5408962 : Nat := 2777397347904571644999643

theorem tailTrace_5408962 : CollatzResearch.WordTrace tailWord_5408962 prefixEnd_5408962 2777397347904571644999643 := by
  unfold tailWord_5408962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49320262857565481502263285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131520700953507950672702093 49320262857565481502263285)
  ·
    refine ⟨4623774642896763890837183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49320262857565481502263285 4623774642896763890837183)
    ·
      refine ⟨6935661964345145836255775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623774642896763890837183 6935661964345145836255775)
      ·
        refine ⟨10403492946517718754383663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935661964345145836255775 10403492946517718754383663)
        ·
          refine ⟨15605239419776578131575495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10403492946517718754383663 15605239419776578131575495)
          ·
            refine ⟨23407859129664867197363243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15605239419776578131575495 23407859129664867197363243)
            ·
              refine ⟨35111788694497300796044865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23407859129664867197363243 35111788694497300796044865)
              ·
                refine ⟨26333841520872975597033649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35111788694497300796044865 26333841520872975597033649)
                ·
                  refine ⟨19750381140654731697775237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26333841520872975597033649 19750381140654731697775237)
                  ·
                    refine ⟨3703196463872762193332857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19750381140654731697775237 3703196463872762193332857)
                    ·
                      refine ⟨2777397347904571644999643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703196463872762193332857 2777397347904571644999643)
                      ·
                        rfl

theorem cell23_5408962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5408962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5408962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5408962 prefixEnd_5408962 := by exact prefixLift 5408962
  have htrace : WordTrace (prefixWord ++ tailWord_5408962) baseStart_5408962 baseEnd_5408962 := by
    simpa [prefixWord, tailWord_5408962, baseEnd_5408962] using wordTrace_append hprefix tailTrace_5408962
  have hstable : (prefixWord ++ tailWord_5408962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5408962).length < 2 ^ (prefixWord ++ tailWord_5408962).sum := by decide
  have hdescent : baseEnd_5408962 < baseStart_5408962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5408962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409011 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 6, 4]
def baseStart_5409011 : Nat := 118140960795 + 5409011 * 2 ^ 59
def prefixEnd_5409011 : Nat := 4983230072969 + 3 ^ 40 * 5409011 * 2
def baseEnd_5409011 : Nat := 925807502818880651095639

theorem tailTrace_5409011 : CollatzResearch.WordTrace tailWord_5409011 prefixEnd_5409011 925807502818880651095639 := by
  unfold tailWord_5409011
  simp only [CollatzResearch.WordTrace]
  refine ⟨197282838607084407377586887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131521892404722938251724591 197282838607084407377586887)
  ·
    refine ⟨295924257910626611066380331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197282838607084407377586887 295924257910626611066380331)
    ·
      refine ⟨443886386865939916599570497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295924257910626611066380331 443886386865939916599570497)
      ·
        refine ⟨332914790149454937449677873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443886386865939916599570497 332914790149454937449677873)
        ·
          refine ⟨249686092612091203087258405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332914790149454937449677873 249686092612091203087258405)
          ·
            refine ⟨46816142364767100578860951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249686092612091203087258405 46816142364767100578860951)
            ·
              refine ⟨70224213547150650868291427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46816142364767100578860951 70224213547150650868291427)
              ·
                refine ⟨105336320320725976302437141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70224213547150650868291427 105336320320725976302437141)
                ·
                  refine ⟨4937640015034030139176741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105336320320725976302437141 4937640015034030139176741)
                  ·
                    refine ⟨925807502818880651095639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937640015034030139176741 925807502818880651095639)
                    ·
                      rfl

theorem cell23_5409011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 4].length) (baseStart_5409011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409011 prefixEnd_5409011 := by exact prefixLift 5409011
  have htrace : WordTrace (prefixWord ++ tailWord_5409011) baseStart_5409011 baseEnd_5409011 := by
    simpa [prefixWord, tailWord_5409011, baseEnd_5409011] using wordTrace_append hprefix tailTrace_5409011
  have hstable : (prefixWord ++ tailWord_5409011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409011).length < 2 ^ (prefixWord ++ tailWord_5409011).sum := by decide
  have hdescent : baseEnd_5409011 < baseStart_5409011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409018 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_5409018 : Nat := 118140960795 + 5409018 * 2 ^ 59
def prefixEnd_5409018 : Nat := 4983230072969 + 3 ^ 40 * 5409018 * 2
def baseEnd_5409018 : Nat := 2777426102821223425899385

theorem tailTrace_5409018 : CollatzResearch.WordTrace tailWord_5409018 prefixEnd_5409018 2777426102821223425899385 := by
  unfold tailWord_5409018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49320773479514761893272927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131522062612039365048727805 49320773479514761893272927)
  ·
    refine ⟨73981160219272142839909391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49320773479514761893272927 73981160219272142839909391)
    ·
      refine ⟨110971740328908214259864087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73981160219272142839909391 110971740328908214259864087)
      ·
        refine ⟨166457610493362321389796131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110971740328908214259864087 166457610493362321389796131)
        ·
          refine ⟨249686415740043482084694197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166457610493362321389796131 249686415740043482084694197)
          ·
            refine ⟨23408101475629076445440081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249686415740043482084694197 23408101475629076445440081)
            ·
              refine ⟨17556076106721807334080061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23408101475629076445440081 17556076106721807334080061)
              ·
                refine ⟨6583528540020677750280023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17556076106721807334080061 6583528540020677750280023)
                ·
                  refine ⟨9875292810031016625420035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583528540020677750280023 9875292810031016625420035)
                  ·
                    refine ⟨14812939215046524938130053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9875292810031016625420035 14812939215046524938130053)
                    ·
                      refine ⟨2777426102821223425899385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14812939215046524938130053 2777426102821223425899385)
                      ·
                        rfl

theorem cell23_5409018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_5409018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409018 prefixEnd_5409018 := by exact prefixLift 5409018
  have htrace : WordTrace (prefixWord ++ tailWord_5409018) baseStart_5409018 baseEnd_5409018 := by
    simpa [prefixWord, tailWord_5409018, baseEnd_5409018] using wordTrace_append hprefix tailTrace_5409018
  have hstable : (prefixWord ++ tailWord_5409018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409018).length < 2 ^ (prefixWord ++ tailWord_5409018).sum := by decide
  have hdescent : baseEnd_5409018 < baseStart_5409018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409024 : List Nat := [2, 1, 1, 2, 1, 1, 15]
def baseStart_5409024 : Nat := 118140960795 + 5409024 * 2 ^ 59
def prefixEnd_5409024 : Nat := 4983230072969 + 3 ^ 40 * 5409024 * 2
def baseEnd_5409024 : Nat := 34289249181545066696597

theorem tailTrace_5409024 : CollatzResearch.WordTrace tailWord_5409024 prefixEnd_5409024 34289249181545066696597 := by
  unfold tailWord_5409024
  simp only [CollatzResearch.WordTrace]
  refine ⟨98641656378018655298905063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131522208504024873731873417 98641656378018655298905063)
  ·
    refine ⟨147962484567027982948357595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98641656378018655298905063 147962484567027982948357595)
    ·
      refine ⟨221943726850541974422536393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147962484567027982948357595 221943726850541974422536393)
      ·
        refine ⟨166457795137906480816902295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221943726850541974422536393 166457795137906480816902295)
        ·
          refine ⟨249686692706859721225353443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166457795137906480816902295 249686692706859721225353443)
          ·
            refine ⟨374530039060289581838030165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249686692706859721225353443 374530039060289581838030165)
            ·
              refine ⟨34289249181545066696597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 374530039060289581838030165 34289249181545066696597)
              ·
                rfl

theorem cell23_5409024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 15].length) (baseStart_5409024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409024 prefixEnd_5409024 := by exact prefixLift 5409024
  have htrace : WordTrace (prefixWord ++ tailWord_5409024) baseStart_5409024 baseEnd_5409024 := by
    simpa [prefixWord, tailWord_5409024, baseEnd_5409024] using wordTrace_append hprefix tailTrace_5409024
  have hstable : (prefixWord ++ tailWord_5409024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409024).length < 2 ^ (prefixWord ++ tailWord_5409024).sum := by decide
  have hdescent : baseEnd_5409024 < baseStart_5409024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409038 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5409038 : Nat := 118140960795 + 5409038 * 2 ^ 59
def prefixEnd_5409038 : Nat := 4983230072969 + 3 ^ 40 * 5409038 * 2
def baseEnd_5409038 : Nat := 2777436372434313347649293

theorem tailTrace_5409038 : CollatzResearch.WordTrace tailWord_5409038 prefixEnd_5409038 2777436372434313347649293 := by
  unfold tailWord_5409038
  simp only [CollatzResearch.WordTrace]
  refine ⟨24660477922248323873602471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131522548918657727325879845 24660477922248323873602471)
  ·
    refine ⟨36990716883372485810403707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24660477922248323873602471 36990716883372485810403707)
    ·
      refine ⟨55486075325058728715605561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36990716883372485810403707 55486075325058728715605561)
      ·
        refine ⟨41614556493794046536704171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55486075325058728715605561 41614556493794046536704171)
        ·
          refine ⟨62421834740691069805056257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41614556493794046536704171 62421834740691069805056257)
          ·
            refine ⟨46816376055518302353792193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62421834740691069805056257 46816376055518302353792193)
            ·
              refine ⟨35112282041638726765344145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46816376055518302353792193 35112282041638726765344145)
              ·
                refine ⟨26334211531229045074008109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35112282041638726765344145 26334211531229045074008109)
                ·
                  refine ⟨9875329324210891902753041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26334211531229045074008109 9875329324210891902753041)
                  ·
                    refine ⟨7406496993158168927064781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9875329324210891902753041 7406496993158168927064781)
                    ·
                      refine ⟨2777436372434313347649293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406496993158168927064781 2777436372434313347649293)
                      ·
                        rfl

theorem cell23_5409038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5409038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409038 prefixEnd_5409038 := by exact prefixLift 5409038
  have htrace : WordTrace (prefixWord ++ tailWord_5409038) baseStart_5409038 baseEnd_5409038 := by
    simpa [prefixWord, tailWord_5409038, baseEnd_5409038] using wordTrace_append hprefix tailTrace_5409038
  have hstable : (prefixWord ++ tailWord_5409038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409038).length < 2 ^ (prefixWord ++ tailWord_5409038).sum := by decide
  have hdescent : baseEnd_5409038 < baseStart_5409038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409041 : List Nat := [1, 2, 2, 1, 1, 6, 2, 8]
def baseStart_5409041 : Nat := 118140960795 + 5409041 * 2 ^ 59
def prefixEnd_5409041 : Nat := 4983230072969 + 3 ^ 40 * 5409041 * 2
def baseEnd_5409041 : Nat := 102868070847269512441177

theorem tailTrace_5409041 : CollatzResearch.WordTrace tailWord_5409041 prefixEnd_5409041 102868070847269512441177 := by
  unfold tailWord_5409041
  simp only [CollatzResearch.WordTrace]
  refine ⟨197283932796975722501178977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131522621864650481667452651 197283932796975722501178977)
  ·
    refine ⟨147962949597731791875884233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197283932796975722501178977 147962949597731791875884233)
    ·
      refine ⟨110972212198298843906913175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147962949597731791875884233 110972212198298843906913175)
      ·
        refine ⟨166458318297448265860369763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110972212198298843906913175 166458318297448265860369763)
        ·
          refine ⟨249687477446172398790554645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166458318297448265860369763 249687477446172398790554645)
          ·
            refine ⟨11704100505289331193307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 249687477446172398790554645 11704100505289331193307249)
            ·
              refine ⟨8778075378966998394980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11704100505289331193307249 8778075378966998394980437)
              ·
                refine ⟨102868070847269512441177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8778075378966998394980437 102868070847269512441177)
                ·
                  rfl

theorem cell23_5409041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 8].length) (baseStart_5409041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409041 prefixEnd_5409041 := by exact prefixLift 5409041
  have htrace : WordTrace (prefixWord ++ tailWord_5409041) baseStart_5409041 baseEnd_5409041 := by
    simpa [prefixWord, tailWord_5409041, baseEnd_5409041] using wordTrace_append hprefix tailTrace_5409041
  have hstable : (prefixWord ++ tailWord_5409041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409041).length < 2 ^ (prefixWord ++ tailWord_5409041).sum := by decide
  have hdescent : baseEnd_5409041 < baseStart_5409041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409045 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_5409045 : Nat := 118140960795 + 5409045 * 2 ^ 59
def prefixEnd_5409045 : Nat := 4983230072969 + 3 ^ 40 * 5409045 * 2
def baseEnd_5409045 : Nat := 925813322266298273420587

theorem tailTrace_5409045 : CollatzResearch.WordTrace tailWord_5409045 prefixEnd_5409045 925813322266298273420587 := by
  unfold tailWord_5409045
  simp only [CollatzResearch.WordTrace]
  refine ⟨197284078688961231184324589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131522719125974154122883059 197284078688961231184324589)
  ·
    refine ⟨73981529508360461694121721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197284078688961231184324589 73981529508360461694121721)
    ·
      refine ⟨55486147131270346270591291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73981529508360461694121721 55486147131270346270591291)
      ·
        refine ⟨83229220696905519405886937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55486147131270346270591291 83229220696905519405886937)
        ·
          refine ⟨62421915522679139554415203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83229220696905519405886937 62421915522679139554415203)
          ·
            refine ⟨93632873284018709331622805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62421915522679139554415203 93632873284018709331622805)
            ·
              refine ⟨4389040935188376999919819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93632873284018709331622805 4389040935188376999919819)
              ·
                refine ⟨6583561402782565499879729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389040935188376999919819 6583561402782565499879729)
                ·
                  refine ⟨4937671052086924124909797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6583561402782565499879729 4937671052086924124909797)
                  ·
                    refine ⟨925813322266298273420587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937671052086924124909797 925813322266298273420587)
                    ·
                      rfl

theorem cell23_5409045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_5409045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409045 prefixEnd_5409045 := by exact prefixLift 5409045
  have htrace : WordTrace (prefixWord ++ tailWord_5409045) baseStart_5409045 baseEnd_5409045 := by
    simpa [prefixWord, tailWord_5409045, baseEnd_5409045] using wordTrace_append hprefix tailTrace_5409045
  have hstable : (prefixWord ++ tailWord_5409045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409045).length < 2 ^ (prefixWord ++ tailWord_5409045).sum := by decide
  have hdescent : baseEnd_5409045 < baseStart_5409045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409055 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_5409055 : Nat := 118140960795 + 5409055 * 2 ^ 59
def prefixEnd_5409055 : Nat := 4983230072969 + 3 ^ 40 * 5409055 * 2
def baseEnd_5409055 : Nat := 2777445101605439781136715

theorem tailTrace_5409055 : CollatzResearch.WordTrace tailWord_5409055 prefixEnd_5409055 2777445101605439781136715 := by
  unfold tailWord_5409055
  simp only [CollatzResearch.WordTrace]
  refine ⟨197284443418925002892188619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131522962279283335261459079 197284443418925002892188619)
  ·
    refine ⟨295926665128387504338282929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197284443418925002892188619 295926665128387504338282929)
    ·
      refine ⟨221944998846290628253712197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295926665128387504338282929 221944998846290628253712197)
      ·
        refine ⟨41614687283679492797571037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 221944998846290628253712197 41614687283679492797571037)
        ·
          refine ⟨15605507731379809799089139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41614687283679492797571037 15605507731379809799089139)
          ·
            refine ⟨23408261597069714698633709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15605507731379809799089139 23408261597069714698633709)
            ·
              refine ⟨8778098098901143011987641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23408261597069714698633709 8778098098901143011987641)
              ·
                refine ⟨6583573574175857258990731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8778098098901143011987641 6583573574175857258990731)
                ·
                  refine ⟨9875360361263785888486097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583573574175857258990731 9875360361263785888486097)
                  ·
                    refine ⟨7406520270947839416364573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9875360361263785888486097 7406520270947839416364573)
                    ·
                      refine ⟨2777445101605439781136715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406520270947839416364573 2777445101605439781136715)
                      ·
                        rfl

theorem cell23_5409055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_5409055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409055 prefixEnd_5409055 := by exact prefixLift 5409055
  have htrace : WordTrace (prefixWord ++ tailWord_5409055) baseStart_5409055 baseEnd_5409055 := by
    simpa [prefixWord, tailWord_5409055, baseEnd_5409055] using wordTrace_append hprefix tailTrace_5409055
  have hstable : (prefixWord ++ tailWord_5409055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409055).length < 2 ^ (prefixWord ++ tailWord_5409055).sum := by decide
  have hdescent : baseEnd_5409055 < baseStart_5409055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409068 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 3]
def baseStart_5409068 : Nat := 118140960795 + 5409068 * 2 ^ 59
def prefixEnd_5409068 : Nat := 4983230072969 + 3 ^ 40 * 5409068 * 2
def baseEnd_5409068 : Nat := 2777451776853948230274155

theorem tailTrace_5409068 : CollatzResearch.WordTrace tailWord_5409068 prefixEnd_5409068 2777451776853948230274155 := by
  unfold tailWord_5409068
  simp only [CollatzResearch.WordTrace]
  refine ⟨98642458783938953056205929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131523278378585270741607905 98642458783938953056205929)
  ·
    refine ⟨73981844087954214792154447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98642458783938953056205929 73981844087954214792154447)
    ·
      refine ⟨110972766131931322188231671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73981844087954214792154447 110972766131931322188231671)
      ·
        refine ⟨166459149197896983282347507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110972766131931322188231671 166459149197896983282347507)
        ·
          refine ⟨249688723796845474923521261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166459149197896983282347507 249688723796845474923521261)
          ·
            refine ⟨93633271423817053096320473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249688723796845474923521261 93633271423817053096320473)
            ·
              refine ⟨70224953567862789822240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93633271423817053096320473 70224953567862789822240355)
              ·
                refine ⟨105337430351794184733360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70224953567862789822240355 105337430351794184733360533)
                ·
                  refine ⟨4937692047740352409376275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105337430351794184733360533 4937692047740352409376275)
                  ·
                    refine ⟨7406538071610528614064413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4937692047740352409376275 7406538071610528614064413)
                    ·
                      refine ⟨2777451776853948230274155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406538071610528614064413 2777451776853948230274155)
                      ·
                        rfl

theorem cell23_5409068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 3].length) (baseStart_5409068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409068 prefixEnd_5409068 := by exact prefixLift 5409068
  have htrace : WordTrace (prefixWord ++ tailWord_5409068) baseStart_5409068 baseEnd_5409068 := by
    simpa [prefixWord, tailWord_5409068, baseEnd_5409068] using wordTrace_append hprefix tailTrace_5409068
  have hstable : (prefixWord ++ tailWord_5409068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409068).length < 2 ^ (prefixWord ++ tailWord_5409068).sum := by decide
  have hdescent : baseEnd_5409068 < baseStart_5409068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409069 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5409069 : Nat := 118140960795 + 5409069 * 2 ^ 59
def prefixEnd_5409069 : Nat := 4983230072969 + 3 ^ 40 * 5409069 * 2
def baseEnd_5409069 : Nat := 2777452290334602726361651

theorem tailTrace_5409069 : CollatzResearch.WordTrace tailWord_5409069 prefixEnd_5409069 2777452290334602726361651 := by
  unfold tailWord_5409069
  simp only [CollatzResearch.WordTrace]
  refine ⟨197284954040874283283198261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131523302693916188855465507 197284954040874283283198261)
  ·
    refine ⟨18495464441331964057799837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197284954040874283283198261 18495464441331964057799837)
    ·
      refine ⟨6935799165499486521674939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18495464441331964057799837 6935799165499486521674939)
      ·
        refine ⟨10403698748249229782512409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935799165499486521674939 10403698748249229782512409)
        ·
          refine ⟨7802774061186922336884307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10403698748249229782512409 7802774061186922336884307)
          ·
            refine ⟨11704161091780383505326461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802774061186922336884307 11704161091780383505326461)
            ·
              refine ⟨4389060409417643814497423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11704161091780383505326461 4389060409417643814497423)
              ·
                refine ⟨6583590614126465721746135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389060409417643814497423 6583590614126465721746135)
                ·
                  refine ⟨9875385921189698582619203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583590614126465721746135 9875385921189698582619203)
                  ·
                    refine ⟨14813078881784547873928805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9875385921189698582619203 14813078881784547873928805)
                    ·
                      refine ⟨2777452290334602726361651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14813078881784547873928805 2777452290334602726361651)
                      ·
                        rfl

theorem cell23_5409069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5409069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409069 prefixEnd_5409069 := by exact prefixLift 5409069
  have htrace : WordTrace (prefixWord ++ tailWord_5409069) baseStart_5409069 baseEnd_5409069 := by
    simpa [prefixWord, tailWord_5409069, baseEnd_5409069] using wordTrace_append hprefix tailTrace_5409069
  have hstable : (prefixWord ++ tailWord_5409069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409069).length < 2 ^ (prefixWord ++ tailWord_5409069).sum := by decide
  have hdescent : baseEnd_5409069 < baseStart_5409069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409086 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_5409086 : Nat := 118140960795 + 5409086 * 2 ^ 59
def prefixEnd_5409086 : Nat := 4983230072969 + 3 ^ 40 * 5409086 * 2
def baseEnd_5409086 : Nat := 2777461019505729159849073

theorem tailTrace_5409086 : CollatzResearch.WordTrace tailWord_5409086 prefixEnd_5409086 2777461019505729159849073 := by
  unfold tailWord_5409086
  simp only [CollatzResearch.WordTrace]
  refine ⟨24660696760226586898320889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131523716054541796791044741 24660696760226586898320889)
  ·
    refine ⟨18495522570169940173740667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24660696760226586898320889 18495522570169940173740667)
    ·
      refine ⟨27743283855254910260611001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18495522570169940173740667 27743283855254910260611001)
      ·
        refine ⟨20807462891441182695458251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27743283855254910260611001 20807462891441182695458251)
        ·
          refine ⟨31211194337161774043187377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20807462891441182695458251 31211194337161774043187377)
          ·
            refine ⟨23408395752871330532390533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31211194337161774043187377 23408395752871330532390533)
            ·
              refine ⟨4389074203663374474823225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23408395752871330532390533 4389074203663374474823225)
              ·
                refine ⟨3291805652747530856117419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4389074203663374474823225 3291805652747530856117419)
                ·
                  refine ⟨4937708479121296284176129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291805652747530856117419 4937708479121296284176129)
                  ·
                    refine ⟨3703281359340972213132097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937708479121296284176129 3703281359340972213132097)
                    ·
                      refine ⟨2777461019505729159849073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703281359340972213132097 2777461019505729159849073)
                      ·
                        rfl

theorem cell23_5409086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_5409086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409086 prefixEnd_5409086 := by exact prefixLift 5409086
  have htrace : WordTrace (prefixWord ++ tailWord_5409086) baseStart_5409086 baseEnd_5409086 := by
    simpa [prefixWord, tailWord_5409086, baseEnd_5409086] using wordTrace_append hprefix tailTrace_5409086
  have hstable : (prefixWord ++ tailWord_5409086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409086).length < 2 ^ (prefixWord ++ tailWord_5409086).sum := by decide
  have hdescent : baseEnd_5409086 < baseStart_5409086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409091 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_5409091 : Nat := 118140960795 + 5409091 * 2 ^ 59
def prefixEnd_5409091 : Nat := 4983230072969 + 3 ^ 40 * 5409091 * 2
def baseEnd_5409091 : Nat := 2777463586909001640286549

theorem tailTrace_5409091 : CollatzResearch.WordTrace tailWord_5409091 prefixEnd_5409091 2777463586909001640286549 := by
  unfold tailWord_5409091
  simp only [CollatzResearch.WordTrace]
  refine ⟨197285756446794581040499127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131523837631196387360332751 197285756446794581040499127)
  ·
    refine ⟨295928634670191871560748691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197285756446794581040499127 295928634670191871560748691)
    ·
      refine ⟨443892952005287807341123037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295928634670191871560748691 443892952005287807341123037)
      ·
        refine ⟨166459857001982927752921139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 443892952005287807341123037 166459857001982927752921139)
        ·
          refine ⟨249689785502974391629381709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166459857001982927752921139 249689785502974391629381709)
          ·
            refine ⟨93633669563615396861018141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249689785502974391629381709 93633669563615396861018141)
            ·
              refine ⟨35112626086355773822881803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93633669563615396861018141 35112626086355773822881803)
              ·
                refine ⟨52668939129533660734322705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35112626086355773822881803 52668939129533660734322705)
                ·
                  refine ⟨39501704347150245550742029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52668939129533660734322705 39501704347150245550742029)
                  ·
                    refine ⟨14813139130181342081528261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39501704347150245550742029 14813139130181342081528261)
                    ·
                      refine ⟨2777463586909001640286549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14813139130181342081528261 2777463586909001640286549)
                      ·
                        rfl

theorem cell23_5409091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_5409091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409091 prefixEnd_5409091 := by exact prefixLift 5409091
  have htrace : WordTrace (prefixWord ++ tailWord_5409091) baseStart_5409091 baseEnd_5409091 := by
    simpa [prefixWord, tailWord_5409091, baseEnd_5409091] using wordTrace_append hprefix tailTrace_5409091
  have hstable : (prefixWord ++ tailWord_5409091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409091).length < 2 ^ (prefixWord ++ tailWord_5409091).sum := by decide
  have hdescent : baseEnd_5409091 < baseStart_5409091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409092 : List Nat := [2, 3, 4, 1, 3, 1, 1, 8]
def baseStart_5409092 : Nat := 118140960795 + 5409092 * 2 ^ 59
def prefixEnd_5409092 : Nat := 4983230072969 + 3 ^ 40 * 5409092 * 2
def baseEnd_5409092 : Nat := 102869040755172449495335

theorem tailTrace_5409092 : CollatzResearch.WordTrace tailWord_5409092 prefixEnd_5409092 102869040755172449495335 := by
  unfold tailWord_5409092
  simp only [CollatzResearch.WordTrace]
  refine ⟨98642896459895479105642765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131523861946527305474190353 98642896459895479105642765)
  ·
    refine ⟨36991086172460804664616037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98642896459895479105642765 36991086172460804664616037)
    ·
      refine ⟨6935828657336400874615507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36991086172460804664616037 6935828657336400874615507)
      ·
        refine ⟨10403742986004601311923261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935828657336400874615507 10403742986004601311923261)
        ·
          refine ⟨3901403619751725491971223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10403742986004601311923261 3901403619751725491971223)
          ·
            refine ⟨5852105429627588237956835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901403619751725491971223 5852105429627588237956835)
            ·
              refine ⟨8778158144441382356935253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852105429627588237956835 8778158144441382356935253)
              ·
                refine ⟨102869040755172449495335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8778158144441382356935253 102869040755172449495335)
                ·
                  rfl

theorem cell23_5409092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 8].length) (baseStart_5409092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409092 prefixEnd_5409092 := by exact prefixLift 5409092
  have htrace : WordTrace (prefixWord ++ tailWord_5409092) baseStart_5409092 baseEnd_5409092 := by
    simpa [prefixWord, tailWord_5409092, baseEnd_5409092] using wordTrace_append hprefix tailTrace_5409092
  have hstable : (prefixWord ++ tailWord_5409092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409092).length < 2 ^ (prefixWord ++ tailWord_5409092).sum := by decide
  have hdescent : baseEnd_5409092 < baseStart_5409092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409125 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_5409125 : Nat := 118140960795 + 5409125 * 2 ^ 59
def prefixEnd_5409125 : Nat := 4983230072969 + 3 ^ 40 * 5409125 * 2
def baseEnd_5409125 : Nat := 2777481045251254507261393

theorem tailTrace_5409125 : CollatzResearch.WordTrace tailWord_5409125 prefixEnd_5409125 2777481045251254507261393 := by
  unfold tailWord_5409125
  simp only [CollatzResearch.WordTrace]
  refine ⟨197286996528671404847236829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131524664352447603231491219 197286996528671404847236829)
  ·
    refine ⟨73982623698251776817713811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197286996528671404847236829 73982623698251776817713811)
    ·
      refine ⟨110973935547377665226570717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73982623698251776817713811 110973935547377665226570717)
      ·
        refine ⟨41615225830266624459964019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110973935547377665226570717 41615225830266624459964019)
        ·
          refine ⟨62422838745399936689946029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41615225830266624459964019 62422838745399936689946029)
          ·
            refine ⟨23408564529524976258729761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62422838745399936689946029 23408564529524976258729761)
            ·
              refine ⟨17556423397143732194047321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23408564529524976258729761 17556423397143732194047321)
              ·
                refine ⟨13167317547857799145535491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17556423397143732194047321 13167317547857799145535491)
                ·
                  refine ⟨19750976321786698718303237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13167317547857799145535491 19750976321786698718303237)
                  ·
                    refine ⟨3703308060335006009681857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19750976321786698718303237 3703308060335006009681857)
                    ·
                      refine ⟨2777481045251254507261393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703308060335006009681857 2777481045251254507261393)
                      ·
                        rfl

theorem cell23_5409125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_5409125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409125 prefixEnd_5409125 := by exact prefixLift 5409125
  have htrace : WordTrace (prefixWord ++ tailWord_5409125) baseStart_5409125 baseEnd_5409125 := by
    simpa [prefixWord, tailWord_5409125, baseEnd_5409125] using wordTrace_append hprefix tailTrace_5409125
  have hstable : (prefixWord ++ tailWord_5409125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409125).length < 2 ^ (prefixWord ++ tailWord_5409125).sum := by decide
  have hdescent : baseEnd_5409125 < baseStart_5409125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409138 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5409138 : Nat := 118140960795 + 5409138 * 2 ^ 59
def prefixEnd_5409138 : Nat := 4983230072969 + 3 ^ 40 * 5409138 * 2
def baseEnd_5409138 : Nat := 2777487720499762956398833

theorem tailTrace_5409138 : CollatzResearch.WordTrace tailWord_5409138 prefixEnd_5409138 2777487720499762956398833 := by
  unfold tailWord_5409138
  simp only [CollatzResearch.WordTrace]
  refine ⟨49321867669406077016865017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131524980451749538711640045 49321867669406077016865017)
  ·
    refine ⟨36991400752054557762648763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49321867669406077016865017 36991400752054557762648763)
    ·
      refine ⟨55487101128081836643973145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36991400752054557762648763 55487101128081836643973145)
      ·
        refine ⟨41615325846061377482979859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55487101128081836643973145 41615325846061377482979859)
        ·
          refine ⟨62422988769092066224469789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41615325846061377482979859 62422988769092066224469789)
          ·
            refine ⟨23408620788409524834176171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62422988769092066224469789 23408620788409524834176171)
            ·
              refine ⟨35112931182614287251264257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23408620788409524834176171 35112931182614287251264257)
              ·
                refine ⟨26334698386960715438448193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35112931182614287251264257 26334698386960715438448193)
                ·
                  refine ⟨19751023790220536578836145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26334698386960715438448193 19751023790220536578836145)
                  ·
                    refine ⟨14813267842665402434127109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19751023790220536578836145 14813267842665402434127109)
                    ·
                      refine ⟨2777487720499762956398833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14813267842665402434127109 2777487720499762956398833)
                      ·
                        rfl

theorem cell23_5409138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5409138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409138 prefixEnd_5409138 := by exact prefixLift 5409138
  have htrace : WordTrace (prefixWord ++ tailWord_5409138) baseStart_5409138 baseEnd_5409138 := by
    simpa [prefixWord, tailWord_5409138, baseEnd_5409138] using wordTrace_append hprefix tailTrace_5409138
  have hstable : (prefixWord ++ tailWord_5409138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409138).length < 2 ^ (prefixWord ++ tailWord_5409138).sum := by decide
  have hdescent : baseEnd_5409138 < baseStart_5409138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409159 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_5409159 : Nat := 118140960795 + 5409159 * 2 ^ 59
def prefixEnd_5409159 : Nat := 4983230072969 + 3 ^ 40 * 5409159 * 2
def baseEnd_5409159 : Nat := 2777498503593507374236237

theorem tailTrace_5409159 : CollatzResearch.WordTrace tailWord_5409159 prefixEnd_5409159 2777498503593507374236237 := by
  unfold tailWord_5409159
  simp only [CollatzResearch.WordTrace]
  refine ⟨197288236610548228653974531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131525491073698819102649687 197288236610548228653974531)
  ·
    refine ⟨295932354915822342980961797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197288236610548228653974531 295932354915822342980961797)
    ·
      refine ⟨55487316546716689308930337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 295932354915822342980961797 55487316546716689308930337)
      ·
        refine ⟨41615487410037516981697753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55487316546716689308930337 41615487410037516981697753)
        ·
          refine ⟨31211615557528137736273315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41615487410037516981697753 31211615557528137736273315)
          ·
            refine ⟨46817423336292206604409973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31211615557528137736273315 46817423336292206604409973)
            ·
              refine ⟨4389133437777394369163435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46817423336292206604409973 4389133437777394369163435)
              ·
                refine ⟨6583700156666091553745153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389133437777394369163435 6583700156666091553745153)
                ·
                  refine ⟨4937775117499568665308865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6583700156666091553745153 4937775117499568665308865)
                  ·
                    refine ⟨3703331338124676498981649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937775117499568665308865 3703331338124676498981649)
                    ·
                      refine ⟨2777498503593507374236237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703331338124676498981649 2777498503593507374236237)
                      ·
                        rfl

theorem cell23_5409159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_5409159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409159 prefixEnd_5409159 := by exact prefixLift 5409159
  have htrace : WordTrace (prefixWord ++ tailWord_5409159) baseStart_5409159 baseEnd_5409159 := by
    simpa [prefixWord, tailWord_5409159, baseEnd_5409159] using wordTrace_append hprefix tailTrace_5409159
  have hstable : (prefixWord ++ tailWord_5409159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409159).length < 2 ^ (prefixWord ++ tailWord_5409159).sum := by decide
  have hdescent : baseEnd_5409159 < baseStart_5409159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409178 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_5409178 : Nat := 118140960795 + 5409178 * 2 ^ 59
def prefixEnd_5409178 : Nat := 4983230072969 + 3 ^ 40 * 5409178 * 2
def baseEnd_5409178 : Nat := 925836086575314266632883

theorem tailTrace_5409178 : CollatzResearch.WordTrace tailWord_5409178 prefixEnd_5409178 925836086575314266632883 := by
  unfold tailWord_5409178
  simp only [CollatzResearch.WordTrace]
  refine ⟨49322232399369848724729047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131525953064986263265944125 49322232399369848724729047)
  ·
    refine ⟨73983348599054773087093571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49322232399369848724729047 73983348599054773087093571)
    ·
      refine ⟨110975022898582159630640357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73983348599054773087093571 110975022898582159630640357)
      ·
        refine ⟨20807816793484154930745067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110975022898582159630640357 20807816793484154930745067)
        ·
          refine ⟨31211725190226232396117601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20807816793484154930745067 31211725190226232396117601)
          ·
            refine ⟨23408793892669674297088201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31211725190226232396117601 23408793892669674297088201)
            ·
              refine ⟨17556595419502255722816151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23408793892669674297088201 17556595419502255722816151)
              ·
                refine ⟨26334893129253383584224227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17556595419502255722816151 26334893129253383584224227)
                ·
                  refine ⟨39502339693880075376336341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26334893129253383584224227 39502339693880075376336341)
                  ·
                    refine ⟨925836086575314266632883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39502339693880075376336341 925836086575314266632883)
                    ·
                      rfl

theorem cell23_5409178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_5409178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409178 prefixEnd_5409178 := by exact prefixLift 5409178
  have htrace : WordTrace (prefixWord ++ tailWord_5409178) baseStart_5409178 baseEnd_5409178 := by
    simpa [prefixWord, tailWord_5409178, baseEnd_5409178] using wordTrace_append hprefix tailTrace_5409178
  have hstable : (prefixWord ++ tailWord_5409178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409178).length < 2 ^ (prefixWord ++ tailWord_5409178).sum := by decide
  have hdescent : baseEnd_5409178 < baseStart_5409178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409205 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_5409205 : Nat := 118140960795 + 5409205 * 2 ^ 59
def prefixEnd_5409205 : Nat := 4983230072969 + 3 ^ 40 * 5409205 * 2
def baseEnd_5409205 : Nat := 2777522123703614194261025

theorem tailTrace_5409205 : CollatzResearch.WordTrace tailWord_5409205 prefixEnd_5409205 2777522123703614194261025 := by
  unfold tailWord_5409205
  simp only [CollatzResearch.WordTrace]
  refine ⟨197289914368381578510149069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131526609578921052340099379 197289914368381578510149069)
  ·
    refine ⟨73983717888143091941305901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197289914368381578510149069 73983717888143091941305901)
    ·
      refine ⟨27743894208053659477989713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73983717888143091941305901 27743894208053659477989713)
      ·
        refine ⟨20807920656040244608492285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27743894208053659477989713 20807920656040244608492285)
        ·
          refine ⟨7802970246015091728184607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20807920656040244608492285 7802970246015091728184607)
          ·
            refine ⟨11704455369022637592276911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802970246015091728184607 11704455369022637592276911)
            ·
              refine ⟨17556683053533956388415367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704455369022637592276911 17556683053533956388415367)
              ·
                refine ⟨26335024580300934582623051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17556683053533956388415367 26335024580300934582623051)
                ·
                  refine ⟨39502536870451401873934577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26335024580300934582623051 39502536870451401873934577)
                  ·
                    refine ⟨29626902652838551405450933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39502536870451401873934577 29626902652838551405450933)
                    ·
                      refine ⟨2777522123703614194261025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29626902652838551405450933 2777522123703614194261025)
                      ·
                        rfl

theorem cell23_5409205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_5409205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409205 prefixEnd_5409205 := by exact prefixLift 5409205
  have htrace : WordTrace (prefixWord ++ tailWord_5409205) baseStart_5409205 baseEnd_5409205 := by
    simpa [prefixWord, tailWord_5409205, baseEnd_5409205] using wordTrace_append hprefix tailTrace_5409205
  have hstable : (prefixWord ++ tailWord_5409205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409205).length < 2 ^ (prefixWord ++ tailWord_5409205).sum := by decide
  have hdescent : baseEnd_5409205 < baseStart_5409205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409242 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 1, 4]
def baseStart_5409242 : Nat := 118140960795 + 5409242 * 2 ^ 59
def prefixEnd_5409242 : Nat := 4983230072969 + 3 ^ 40 * 5409242 * 2
def baseEnd_5409242 : Nat := 925847040829276849832785

theorem tailTrace_5409242 : CollatzResearch.WordTrace tailWord_5409242 prefixEnd_5409242 925847040829276849832785 := by
  unfold tailWord_5409242
  simp only [CollatzResearch.WordTrace]
  refine ⟨49322815967311883457311495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131527509246165022552830653 49322815967311883457311495)
  ·
    refine ⟨73984223950967825185967243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49322815967311883457311495 73984223950967825185967243)
    ·
      refine ⟨110976335926451737778950865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73984223950967825185967243 110976335926451737778950865)
      ·
        refine ⟨83232251944838803334213149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110976335926451737778950865 83232251944838803334213149)
        ·
          refine ⟨31212094479314551250329931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83232251944838803334213149 31212094479314551250329931)
          ·
            refine ⟨46818141718971826875494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31212094479314551250329931 46818141718971826875494897)
            ·
              refine ⟨35113606289228870156621173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46818141718971826875494897 35113606289228870156621173)
              ·
                refine ⟨3291900589615206577183235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35113606289228870156621173 3291900589615206577183235)
                ·
                  refine ⟨4937850884422809865774853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291900589615206577183235 4937850884422809865774853)
                  ·
                    refine ⟨925847040829276849832785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937850884422809865774853 925847040829276849832785)
                    ·
                      rfl

theorem cell23_5409242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 4].length) (baseStart_5409242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409242 prefixEnd_5409242 := by exact prefixLift 5409242
  have htrace : WordTrace (prefixWord ++ tailWord_5409242) baseStart_5409242 baseEnd_5409242 := by
    simpa [prefixWord, tailWord_5409242, baseEnd_5409242] using wordTrace_append hprefix tailTrace_5409242
  have hstable : (prefixWord ++ tailWord_5409242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409242).length < 2 ^ (prefixWord ++ tailWord_5409242).sum := by decide
  have hdescent : baseEnd_5409242 < baseStart_5409242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409255 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 6]
def baseStart_5409255 : Nat := 118140960795 + 5409255 * 2 ^ 59
def prefixEnd_5409255 : Nat := 4983230072969 + 3 ^ 40 * 5409255 * 2
def baseEnd_5409255 : Nat := 308616421970704333181755

theorem tailTrace_5409255 : CollatzResearch.WordTrace tailWord_5409255 prefixEnd_5409255 308616421970704333181755 := by
  unfold tailWord_5409255
  simp only [CollatzResearch.WordTrace]
  refine ⟨197291738018200437049469219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131527825345466958032979479 197291738018200437049469219)
  ·
    refine ⟨295937607027300655574203829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197291738018200437049469219 295937607027300655574203829)
    ·
      refine ⟨27744150658809436460081609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 295937607027300655574203829 27744150658809436460081609)
      ·
        refine ⟨20808112994107077345061207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27744150658809436460081609 20808112994107077345061207)
        ·
          refine ⟨31212169491160616017591811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20808112994107077345061207 31212169491160616017591811)
          ·
            refine ⟨46818254236740924026387717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31212169491160616017591811 46818254236740924026387717)
            ·
              refine ⟨8778422669388923254947697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46818254236740924026387717 8778422669388923254947697)
              ·
                refine ⟨6583817002041692441210773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8778422669388923254947697 6583817002041692441210773)
                ·
                  refine ⟨308616421970704333181755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6583817002041692441210773 308616421970704333181755)
                  ·
                    rfl

theorem cell23_5409255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 6].length) (baseStart_5409255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409255 prefixEnd_5409255 := by exact prefixLift 5409255
  have htrace : WordTrace (prefixWord ++ tailWord_5409255) baseStart_5409255 baseEnd_5409255 := by
    simpa [prefixWord, tailWord_5409255, baseEnd_5409255] using wordTrace_append hprefix tailTrace_5409255
  have hstable : (prefixWord ++ tailWord_5409255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409255).length < 2 ^ (prefixWord ++ tailWord_5409255).sum := by decide
  have hdescent : baseEnd_5409255 < baseStart_5409255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409286 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_5409286 : Nat := 118140960795 + 5409286 * 2 ^ 59
def prefixEnd_5409286 : Nat := 4983230072969 + 3 ^ 40 * 5409286 * 2
def baseEnd_5409286 : Nat := 2777563715636628377348153

theorem tailTrace_5409286 : CollatzResearch.WordTrace tailWord_5409286 prefixEnd_5409286 2777563715636628377348153 := by
  unfold tailWord_5409286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165402146284004041995241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131528579120725419562565141 6165402146284004041995241)
  ·
    refine ⟨4624051609713003031496431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6165402146284004041995241 4624051609713003031496431)
    ·
      refine ⟨6936077414569504547244647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624051609713003031496431 6936077414569504547244647)
      ·
        refine ⟨10404116121854256820866971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936077414569504547244647 10404116121854256820866971)
        ·
          refine ⟨15606174182781385231300457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404116121854256820866971 15606174182781385231300457)
          ·
            refine ⟨11704630637086038923475343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15606174182781385231300457 11704630637086038923475343)
            ·
              refine ⟨17556945955629058385213015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704630637086038923475343 17556945955629058385213015)
              ·
                refine ⟨26335418933443587577819523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17556945955629058385213015 26335418933443587577819523)
                ·
                  refine ⟨39503128400165381366729285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26335418933443587577819523 39503128400165381366729285)
                  ·
                    refine ⟨7406836575031009006261741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39503128400165381366729285 7406836575031009006261741)
                    ·
                      refine ⟨2777563715636628377348153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406836575031009006261741 2777563715636628377348153)
                      ·
                        rfl

theorem cell23_5409286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_5409286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409286 prefixEnd_5409286 := by exact prefixLift 5409286
  have htrace : WordTrace (prefixWord ++ tailWord_5409286) baseStart_5409286 baseEnd_5409286 := by
    simpa [prefixWord, tailWord_5409286, baseEnd_5409286] using wordTrace_append hprefix tailTrace_5409286
  have hstable : (prefixWord ++ tailWord_5409286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409286).length < 2 ^ (prefixWord ++ tailWord_5409286).sum := by decide
  have hdescent : baseEnd_5409286 < baseStart_5409286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409292 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 5, 2]
def baseStart_5409292 : Nat := 118140960795 + 5409292 * 2 ^ 59
def prefixEnd_5409292 : Nat := 4983230072969 + 3 ^ 40 * 5409292 * 2
def baseEnd_5409292 : Nat := 2777566796520555353873125

theorem tailTrace_5409292 : CollatzResearch.WordTrace tailWord_5409292 prefixEnd_5409292 2777566796520555353873125 := by
  unfold tailWord_5409292
  simp only [CollatzResearch.WordTrace]
  refine ⟨98646543759533196184283065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131528725012710928245710753 98646543759533196184283065)
  ·
    refine ⟨73984907819649897138212299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98646543759533196184283065 73984907819649897138212299)
    ·
      refine ⟨110977361729474845707318449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73984907819649897138212299 110977361729474845707318449)
      ·
        refine ⟨83233021297106134280488837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110977361729474845707318449 83233021297106134280488837)
        ·
          refine ⟨15606191493207400177591657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83233021297106134280488837 15606191493207400177591657)
          ·
            refine ⟨11704643619905550133193743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15606191493207400177591657 11704643619905550133193743)
            ·
              refine ⟨17556965429858325199790615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704643619905550133193743 17556965429858325199790615)
              ·
                refine ⟨26335448144787487799685923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17556965429858325199790615 26335448144787487799685923)
                ·
                  refine ⟨39503172217181231699528885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26335448144787487799685923 39503172217181231699528885)
                  ·
                    refine ⟨3703422395360740471830833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39503172217181231699528885 3703422395360740471830833)
                    ·
                      refine ⟨2777566796520555353873125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3703422395360740471830833 2777566796520555353873125)
                      ·
                        rfl

theorem cell23_5409292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_5409292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409292 prefixEnd_5409292 := by exact prefixLift 5409292
  have htrace : WordTrace (prefixWord ++ tailWord_5409292) baseStart_5409292 baseEnd_5409292 := by
    simpa [prefixWord, tailWord_5409292, baseEnd_5409292] using wordTrace_append hprefix tailTrace_5409292
  have hstable : (prefixWord ++ tailWord_5409292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409292).length < 2 ^ (prefixWord ++ tailWord_5409292).sum := by decide
  have hdescent : baseEnd_5409292 < baseStart_5409292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409293 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5409293 : Nat := 118140960795 + 5409293 * 2 ^ 59
def prefixEnd_5409293 : Nat := 4983230072969 + 3 ^ 40 * 5409293 * 2
def baseEnd_5409293 : Nat := 925855770000403283320207

theorem tailTrace_5409293 : CollatzResearch.WordTrace tailWord_5409293 prefixEnd_5409293 925855770000403283320207 := by
  unfold tailWord_5409293
  simp only [CollatzResearch.WordTrace]
  refine ⟨197293123992062769539352533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131528749328041846359568355 197293123992062769539352533)
  ·
    refine ⟨4624057593563971161078575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 197293123992062769539352533 4624057593563971161078575)
    ·
      refine ⟨6936086390345956741617863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624057593563971161078575 6936086390345956741617863)
      ·
        refine ⟨10404129585518935112426795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936086390345956741617863 10404129585518935112426795)
        ·
          refine ⟨15606194378278402668640193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404129585518935112426795 15606194378278402668640193)
          ·
            refine ⟨11704645783708802001480145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15606194378278402668640193 11704645783708802001480145)
            ·
              refine ⟨8778484337781601501110109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11704645783708802001480145 8778484337781601501110109)
              ·
                refine ⟨3291931626668100562916291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8778484337781601501110109 3291931626668100562916291)
                ·
                  refine ⟨4937897440002150844374437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291931626668100562916291 4937897440002150844374437)
                  ·
                    refine ⟨925855770000403283320207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937897440002150844374437 925855770000403283320207)
                    ·
                      rfl

theorem cell23_5409293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5409293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409293 prefixEnd_5409293 := by exact prefixLift 5409293
  have htrace : WordTrace (prefixWord ++ tailWord_5409293) baseStart_5409293 baseEnd_5409293 := by
    simpa [prefixWord, tailWord_5409293, baseEnd_5409293] using wordTrace_append hprefix tailTrace_5409293
  have hstable : (prefixWord ++ tailWord_5409293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409293).length < 2 ^ (prefixWord ++ tailWord_5409293).sum := by decide
  have hdescent : baseEnd_5409293 < baseStart_5409293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409299 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 1, 1, 3]
def baseStart_5409299 : Nat := 118140960795 + 5409299 * 2 ^ 59
def prefixEnd_5409299 : Nat := 4983230072969 + 3 ^ 40 * 5409299 * 2
def baseEnd_5409299 : Nat := 2777570390885136826485593

theorem tailTrace_5409299 : CollatzResearch.WordTrace tailWord_5409299 prefixEnd_5409299 2777570390885136826485593 := by
  unfold tailWord_5409299
  simp only [CollatzResearch.WordTrace]
  refine ⟨197293342830041032564070951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131528895220027355042713967 197293342830041032564070951)
  ·
    refine ⟨295940014245061548846106427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197293342830041032564070951 295940014245061548846106427)
    ·
      refine ⟨443910021367592323269159641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295940014245061548846106427 443910021367592323269159641)
      ·
        refine ⟨332932516025694242451869731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443910021367592323269159641 332932516025694242451869731)
        ·
          refine ⟨499398774038541363677804597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332932516025694242451869731 499398774038541363677804597)
          ·
            refine ⟨46818635066113252844794181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 499398774038541363677804597 46818635066113252844794181)
            ·
              refine ⟨8778494074896234908398909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46818635066113252844794181 8778494074896234908398909)
              ·
                refine ⟨3291935278086088090649591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8778494074896234908398909 3291935278086088090649591)
                ·
                  refine ⟨4937902917129132135974387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291935278086088090649591 4937902917129132135974387)
                  ·
                    refine ⟨7406854375693698203961581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4937902917129132135974387 7406854375693698203961581)
                    ·
                      refine ⟨2777570390885136826485593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406854375693698203961581 2777570390885136826485593)
                      ·
                        rfl

theorem cell23_5409299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 1, 3].length) (baseStart_5409299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409299 prefixEnd_5409299 := by exact prefixLift 5409299
  have htrace : WordTrace (prefixWord ++ tailWord_5409299) baseStart_5409299 baseEnd_5409299 := by
    simpa [prefixWord, tailWord_5409299, baseEnd_5409299] using wordTrace_append hprefix tailTrace_5409299
  have hstable : (prefixWord ++ tailWord_5409299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409299).length < 2 ^ (prefixWord ++ tailWord_5409299).sum := by decide
  have hdescent : baseEnd_5409299 < baseStart_5409299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409305 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_5409305 : Nat := 118140960795 + 5409305 * 2 ^ 59
def prefixEnd_5409305 : Nat := 4983230072969 + 3 ^ 40 * 5409305 * 2
def baseEnd_5409305 : Nat := 2777573471769063803010565

theorem tailTrace_5409305 : CollatzResearch.WordTrace tailWord_5409305 prefixEnd_5409305 2777573471769063803010565 := by
  unfold tailWord_5409305
  simp only [CollatzResearch.WordTrace]
  refine ⟨197293561668019295588789369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131529041112012863725859579 197293561668019295588789369)
  ·
    refine ⟨147970171251014471691592027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197293561668019295588789369 147970171251014471691592027)
    ·
      refine ⟨221955256876521707537388041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147970171251014471691592027 221955256876521707537388041)
      ·
        refine ⟨166466442657391280653041031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221955256876521707537388041 166466442657391280653041031)
        ·
          refine ⟨249699663986086920979561547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166466442657391280653041031 249699663986086920979561547)
          ·
            refine ⟨374549495979130381469342321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249699663986086920979561547 374549495979130381469342321)
            ·
              refine ⟨280912121984347786102006741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374549495979130381469342321 280912121984347786102006741)
              ·
                refine ⟨6583877859008151236765783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280912121984347786102006741 6583877859008151236765783)
                ·
                  refine ⟨9875816788512226855148675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583877859008151236765783 9875816788512226855148675)
                  ·
                    refine ⟨14813725182768340282723013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9875816788512226855148675 14813725182768340282723013)
                    ·
                      refine ⟨2777573471769063803010565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14813725182768340282723013 2777573471769063803010565)
                      ·
                        rfl

theorem cell23_5409305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_5409305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409305 prefixEnd_5409305 := by exact prefixLift 5409305
  have htrace : WordTrace (prefixWord ++ tailWord_5409305) baseStart_5409305 baseEnd_5409305 := by
    simpa [prefixWord, tailWord_5409305, baseEnd_5409305] using wordTrace_append hprefix tailTrace_5409305
  have hstable : (prefixWord ++ tailWord_5409305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409305).length < 2 ^ (prefixWord ++ tailWord_5409305).sum := by decide
  have hdescent : baseEnd_5409305 < baseStart_5409305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409316 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5409316 : Nat := 118140960795 + 5409316 * 2 ^ 59
def prefixEnd_5409316 : Nat := 4983230072969 + 3 ^ 40 * 5409316 * 2
def baseEnd_5409316 : Nat := 2777579120056263259973015

theorem tailTrace_5409316 : CollatzResearch.WordTrace tailWord_5409316 prefixEnd_5409316 2777579120056263259973015 := by
  unfold tailWord_5409316
  simp only [CollatzResearch.WordTrace]
  refine ⟨98646981435489722233719901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131529308580652962978293201 98646981435489722233719901)
  ·
    refine ⟨36992618038308645837644963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98646981435489722233719901 36992618038308645837644963)
    ·
      refine ⟨55488927057462968756467445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36992618038308645837644963 55488927057462968756467445)
      ·
        refine ⟨5202086911637153320918823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55488927057462968756467445 5202086911637153320918823)
        ·
          refine ⟨7803130367455729981378235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202086911637153320918823 7803130367455729981378235)
          ·
            refine ⟨11704695551183594972067353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7803130367455729981378235 11704695551183594972067353)
            ·
              refine ⟨8778521663387696229050515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11704695551183594972067353 8778521663387696229050515)
              ·
                refine ⟨13167782495081544343575773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8778521663387696229050515 13167782495081544343575773)
                ·
                  refine ⟨4937918435655579128840915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13167782495081544343575773 4937918435655579128840915)
                  ·
                    refine ⟨7406877653483368693261373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4937918435655579128840915 7406877653483368693261373)
                    ·
                      refine ⟨2777579120056263259973015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406877653483368693261373 2777579120056263259973015)
                      ·
                        rfl

theorem cell23_5409316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5409316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409316 prefixEnd_5409316 := by exact prefixLift 5409316
  have htrace : WordTrace (prefixWord ++ tailWord_5409316) baseStart_5409316 baseEnd_5409316 := by
    simpa [prefixWord, tailWord_5409316, baseEnd_5409316] using wordTrace_append hprefix tailTrace_5409316
  have hstable : (prefixWord ++ tailWord_5409316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409316).length < 2 ^ (prefixWord ++ tailWord_5409316).sum := by decide
  have hdescent : baseEnd_5409316 < baseStart_5409316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409345 : List Nat := [1, 2, 5, 1, 1, 3, 1, 9]
def baseStart_5409345 : Nat := 118140960795 + 5409345 * 2 ^ 59
def prefixEnd_5409345 : Nat := 4983230072969 + 3 ^ 40 * 5409345 * 2
def baseEnd_5409345 : Nat := 102873852259083098018903

theorem tailTrace_5409345 : CollatzResearch.WordTrace tailWord_5409345 prefixEnd_5409345 102873852259083098018903 := by
  unfold tailWord_5409345
  simp only [CollatzResearch.WordTrace]
  refine ⟨197295020587874382420245489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131530013725249588280163659 197295020587874382420245489)
  ·
    refine ⟨147971265440905786815184117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197295020587874382420245489 147971265440905786815184117)
    ·
      refine ⟨13872306135084917513923511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147971265440905786815184117 13872306135084917513923511)
      ·
        refine ⟨20808459202627376270885267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13872306135084917513923511 20808459202627376270885267)
        ·
          refine ⟨31212688803941064406327901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20808459202627376270885267 31212688803941064406327901)
          ·
            refine ⟨11704758301477899152372963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31212688803941064406327901 11704758301477899152372963)
            ·
              refine ⟨17557137452216848728559445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704758301477899152372963 17557137452216848728559445)
              ·
                refine ⟨102873852259083098018903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17557137452216848728559445 102873852259083098018903)
                ·
                  rfl

theorem cell23_5409345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 9].length) (baseStart_5409345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409345 prefixEnd_5409345 := by exact prefixLift 5409345
  have htrace : WordTrace (prefixWord ++ tailWord_5409345) baseStart_5409345 baseEnd_5409345 := by
    simpa [prefixWord, tailWord_5409345, baseEnd_5409345] using wordTrace_append hprefix tailTrace_5409345
  have hstable : (prefixWord ++ tailWord_5409345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409345).length < 2 ^ (prefixWord ++ tailWord_5409345).sum := by decide
  have hdescent : baseEnd_5409345 < baseStart_5409345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5409350 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_5409350 : Nat := 118140960795 + 5409350 * 2 ^ 59
def prefixEnd_5409350 : Nat := 4983230072969 + 3 ^ 40 * 5409350 * 2
def baseEnd_5409350 : Nat := 2777596578398516126947859

theorem tailTrace_5409350 : CollatzResearch.WordTrace tailWord_5409350 prefixEnd_5409350 2777596578398516126947859 := by
  unfold tailWord_5409350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165475092276758383568047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 131530135301904178849451669 6165475092276758383568047)
  ·
    refine ⟨9248212638415137575352071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6165475092276758383568047 9248212638415137575352071)
    ·
      refine ⟨13872318957622706363028107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9248212638415137575352071 13872318957622706363028107)
      ·
        refine ⟨20808478436434059544542161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13872318957622706363028107 20808478436434059544542161)
        ·
          refine ⟨15606358827325544658406621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20808478436434059544542161 15606358827325544658406621)
          ·
            refine ⟨5852384560247079246902483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15606358827325544658406621 5852384560247079246902483)
            ·
              refine ⟨8778576840370618870353725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852384560247079246902483 8778576840370618870353725)
              ·
                refine ⟨3291966315138982076382647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8778576840370618870353725 3291966315138982076382647)
                ·
                  refine ⟨4937949472708473114573971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291966315138982076382647 4937949472708473114573971)
                  ·
                    refine ⟨7406924209062709671860957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4937949472708473114573971 7406924209062709671860957)
                    ·
                      refine ⟨2777596578398516126947859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7406924209062709671860957 2777596578398516126947859)
                      ·
                        rfl

theorem cell23_5409350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_5409350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5409350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5409350 prefixEnd_5409350 := by exact prefixLift 5409350
  have htrace : WordTrace (prefixWord ++ tailWord_5409350) baseStart_5409350 baseEnd_5409350 := by
    simpa [prefixWord, tailWord_5409350, baseEnd_5409350] using wordTrace_append hprefix tailTrace_5409350
  have hstable : (prefixWord ++ tailWord_5409350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5409350).length < 2 ^ (prefixWord ++ tailWord_5409350).sum := by decide
  have hdescent : baseEnd_5409350 < baseStart_5409350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5409350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
